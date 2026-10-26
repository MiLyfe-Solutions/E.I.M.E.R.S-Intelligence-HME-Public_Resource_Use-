import V185TrunkScan23Chunk0348

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2064584 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_2064584 : Nat := 118140960795 + 2064584 * 2 ^ 59
def prefixEnd_2064584 : Nat := 4983230072969 + 3 ^ 40 * 2064584 * 2
def baseEnd_2064584 : Nat := 1060123943582255539305157

theorem tailTrace_2064584 : CollatzResearch.WordTrace tailWord_2064584 prefixEnd_2064584 1060123943582255539305157 := by
  unfold tailWord_2064584
  simp only [CollatzResearch.WordTrace]
  refine ⟨37650782376186122860080403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50201043168248163813440537 37650782376186122860080403)
  ·
    refine ⟨56476173564279184290120605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37650782376186122860080403 56476173564279184290120605)
    ·
      refine ⟨21178565086604694108795227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56476173564279184290120605 21178565086604694108795227)
      ·
        refine ⟨31767847629907041163192841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21178565086604694108795227 31767847629907041163192841)
        ·
          refine ⟨23825885722430280872394631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31767847629907041163192841 23825885722430280872394631)
          ·
            refine ⟨35738828583645421308591947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23825885722430280872394631 35738828583645421308591947)
            ·
              refine ⟨53608242875468131962887921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35738828583645421308591947 53608242875468131962887921)
              ·
                refine ⟨40206182156601098972165941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53608242875468131962887921 40206182156601098972165941)
                ·
                  refine ⟨3769329577181353028640557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40206182156601098972165941 3769329577181353028640557)
                  ·
                    refine ⟨1413498591443007385740209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769329577181353028640557 1413498591443007385740209)
                    ·
                      refine ⟨1060123943582255539305157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413498591443007385740209 1060123943582255539305157)
                      ·
                        rfl

theorem cell23_2064584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_2064584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064584 prefixEnd_2064584 := by exact prefixLift 2064584
  have htrace : WordTrace (prefixWord ++ tailWord_2064584) baseStart_2064584 baseEnd_2064584 := by
    simpa [prefixWord, tailWord_2064584, baseEnd_2064584] using wordTrace_append hprefix tailTrace_2064584
  have hstable : (prefixWord ++ tailWord_2064584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064584).length < 2 ^ (prefixWord ++ tailWord_2064584).sum := by decide
  have hdescent : baseEnd_2064584 < baseStart_2064584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064617 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_2064617 : Nat := 118140960795 + 2064617 * 2 ^ 59
def prefixEnd_2064617 : Nat := 4983230072969 + 3 ^ 40 * 2064617 * 2
def baseEnd_2064617 : Nat := 1060140888443853910192505

theorem tailTrace_2064617 : CollatzResearch.WordTrace tailWord_2064617 prefixEnd_2064617 1060140888443853910192505 := by
  unfold tailWord_2064617
  simp only [CollatzResearch.WordTrace]
  refine ⟨75302768361252692356112105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50201845574168461570741403 75302768361252692356112105)
  ·
    refine ⟨56477076270939519267084079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75302768361252692356112105 56477076270939519267084079)
    ·
      refine ⟨84715614406409278900626119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56477076270939519267084079 84715614406409278900626119)
      ·
        refine ⟨127073421609613918350939179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84715614406409278900626119 127073421609613918350939179)
        ·
          refine ⟨190610132414420877526408769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127073421609613918350939179 190610132414420877526408769)
          ·
            refine ⟨142957599310815658144806577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190610132414420877526408769 142957599310815658144806577)
            ·
              refine ⟨107218199483111743608604933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142957599310815658144806577 107218199483111743608604933)
              ·
                refine ⟨20103412403083451926613425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107218199483111743608604933 20103412403083451926613425)
                ·
                  refine ⟨15077559302312588944960069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20103412403083451926613425 15077559302312588944960069)
                  ·
                    refine ⟨2827042369183610427180013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15077559302312588944960069 2827042369183610427180013)
                    ·
                      refine ⟨1060140888443853910192505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2827042369183610427180013 1060140888443853910192505)
                      ·
                        rfl

theorem cell23_2064617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_2064617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064617 prefixEnd_2064617 := by exact prefixLift 2064617
  have htrace : WordTrace (prefixWord ++ tailWord_2064617) baseStart_2064617 baseEnd_2064617 := by
    simpa [prefixWord, tailWord_2064617, baseEnd_2064617] using wordTrace_append hprefix tailTrace_2064617
  have hstable : (prefixWord ++ tailWord_2064617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064617).length < 2 ^ (prefixWord ++ tailWord_2064617).sum := by decide
  have hdescent : baseEnd_2064617 < baseStart_2064617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064648 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_2064648 : Nat := 118140960795 + 2064648 * 2 ^ 59
def prefixEnd_2064648 : Nat := 4983230072969 + 3 ^ 40 * 2064648 * 2
def baseEnd_2064648 : Nat := 1060156806344143288904863

theorem tailTrace_2064648 : CollatzResearch.WordTrace tailWord_2064648 prefixEnd_2064648 1060156806344143288904863 := by
  unfold tailWord_2064648
  simp only [CollatzResearch.WordTrace]
  refine ⟨37651949512070192325245299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50202599349426923100327065 37651949512070192325245299)
  ·
    refine ⟨56477924268105288487867949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37651949512070192325245299 56477924268105288487867949)
    ·
      refine ⟨21179221600539483182950481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56477924268105288487867949 21179221600539483182950481)
      ·
        refine ⟨15884416200404612387212861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21179221600539483182950481 15884416200404612387212861)
        ·
          refine ⟨5956656075151729645204823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15884416200404612387212861 5956656075151729645204823)
          ·
            refine ⟨8934984112727594467807235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956656075151729645204823 8934984112727594467807235)
            ·
              refine ⟨13402476169091391701710853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934984112727594467807235 13402476169091391701710853)
              ·
                refine ⟨2512964281704635944070785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13402476169091391701710853 2512964281704635944070785)
                ·
                  refine ⟨1884723211278476958053089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2512964281704635944070785 1884723211278476958053089)
                  ·
                    refine ⟨1413542408458857718539817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1884723211278476958053089 1413542408458857718539817)
                    ·
                      refine ⟨1060156806344143288904863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413542408458857718539817 1060156806344143288904863)
                      ·
                        rfl

theorem cell23_2064648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_2064648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064648 prefixEnd_2064648 := by exact prefixLift 2064648
  have htrace : WordTrace (prefixWord ++ tailWord_2064648) baseStart_2064648 baseEnd_2064648 := by
    simpa [prefixWord, tailWord_2064648, baseEnd_2064648] using wordTrace_append hprefix tailTrace_2064648
  have hstable : (prefixWord ++ tailWord_2064648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064648).length < 2 ^ (prefixWord ++ tailWord_2064648).sum := by decide
  have hdescent : baseEnd_2064648 < baseStart_2064648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064664 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2064664 : Nat := 118140960795 + 2064664 * 2 ^ 59
def prefixEnd_2064664 : Nat := 4983230072969 + 3 ^ 40 * 2064664 * 2
def baseEnd_2064664 : Nat := 1060165022034615226304789

theorem tailTrace_2064664 : CollatzResearch.WordTrace tailWord_2064664 prefixEnd_2064664 1060165022034615226304789 := by
  unfold tailWord_2064664
  simp only [CollatzResearch.WordTrace]
  refine ⟨37652241296041209691536523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50202988394721612922048697 37652241296041209691536523)
  ·
    refine ⟨56478361944061814537304785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37652241296041209691536523 56478361944061814537304785)
    ·
      refine ⟨42358771458046360902978589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56478361944061814537304785 42358771458046360902978589)
      ·
        refine ⟨15884539296767385338616971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42358771458046360902978589 15884539296767385338616971)
        ·
          refine ⟨23826808945151078007925457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15884539296767385338616971 23826808945151078007925457)
          ·
            refine ⟨17870106708863308505944093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23826808945151078007925457 17870106708863308505944093)
            ·
              refine ⟨6701290015823740689729035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17870106708863308505944093 6701290015823740689729035)
              ·
                refine ⟨10051935023735611034593553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701290015823740689729035 10051935023735611034593553)
                ·
                  refine ⟨7538951267801708275945165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10051935023735611034593553 7538951267801708275945165)
                  ·
                    refine ⟨2827106725425640603479437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7538951267801708275945165 2827106725425640603479437)
                    ·
                      refine ⟨1060165022034615226304789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2827106725425640603479437 1060165022034615226304789)
                      ·
                        rfl

theorem cell23_2064664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2064664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064664 prefixEnd_2064664 := by exact prefixLift 2064664
  have htrace : WordTrace (prefixWord ++ tailWord_2064664) baseStart_2064664 baseEnd_2064664 := by
    simpa [prefixWord, tailWord_2064664, baseEnd_2064664] using wordTrace_append hprefix tailTrace_2064664
  have hstable : (prefixWord ++ tailWord_2064664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064664).length < 2 ^ (prefixWord ++ tailWord_2064664).sum := by decide
  have hdescent : baseEnd_2064664 < baseStart_2064664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064667 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 4, 5]
def baseStart_2064667 : Nat := 118140960795 + 2064667 * 2 ^ 59
def prefixEnd_2064667 : Nat := 4983230072969 + 3 ^ 40 * 2064667 * 2
def baseEnd_2064667 : Nat := 353388854158859571522425

theorem tailTrace_2064667 : CollatzResearch.WordTrace tailWord_2064667 prefixEnd_2064667 353388854158859571522425 := by
  unfold tailWord_2064667
  simp only [CollatzResearch.WordTrace]
  refine ⟨75304592011071550895432255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50203061340714367263621503 75304592011071550895432255)
  ·
    refine ⟨112956888016607326343148383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75304592011071550895432255 112956888016607326343148383)
    ·
      refine ⟨169435332024910989514722575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112956888016607326343148383 169435332024910989514722575)
      ·
        refine ⟨254152998037366484272083863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169435332024910989514722575 254152998037366484272083863)
        ·
          refine ⟨381229497056049726408125795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254152998037366484272083863 381229497056049726408125795)
          ·
            refine ⟨571844245584074589612188693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381229497056049726408125795 571844245584074589612188693)
            ·
              refine ⟨26805199011753496388071345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 571844245584074589612188693 26805199011753496388071345)
              ·
                refine ⟨20103899258815122291053509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26805199011753496388071345 20103899258815122291053509)
                ·
                  refine ⟨3769481111027835429572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20103899258815122291053509 3769481111027835429572533)
                  ·
                    refine ⟨353388854158859571522425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3769481111027835429572533 353388854158859571522425)
                    ·
                      rfl

theorem cell23_2064667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 5].length) (baseStart_2064667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064667 prefixEnd_2064667 := by exact prefixLift 2064667
  have htrace : WordTrace (prefixWord ++ tailWord_2064667) baseStart_2064667 baseEnd_2064667 := by
    simpa [prefixWord, tailWord_2064667, baseEnd_2064667] using wordTrace_append hprefix tailTrace_2064667
  have hstable : (prefixWord ++ tailWord_2064667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064667).length < 2 ^ (prefixWord ++ tailWord_2064667).sum := by decide
  have hdescent : baseEnd_2064667 < baseStart_2064667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064684 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_2064684 : Nat := 118140960795 + 2064684 * 2 ^ 59
def prefixEnd_2064684 : Nat := 4983230072969 + 3 ^ 40 * 2064684 * 2
def baseEnd_2064684 : Nat := 353391763882568382684899

theorem tailTrace_2064684 : CollatzResearch.WordTrace tailWord_2064684 prefixEnd_2064684 353391763882568382684899 := by
  unfold tailWord_2064684
  simp only [CollatzResearch.WordTrace]
  refine ⟨37652606026004981399400553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50203474701339975199200737 37652606026004981399400553)
  ·
    refine ⟨28239454519503736049550415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37652606026004981399400553 28239454519503736049550415)
    ·
      refine ⟨42359181779255604074325623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28239454519503736049550415 42359181779255604074325623)
      ·
        refine ⟨63538772668883406111488435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42359181779255604074325623 63538772668883406111488435)
        ·
          refine ⟨95308159003325109167232653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63538772668883406111488435 95308159003325109167232653)
          ·
            refine ⟨35740559626246915937712245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95308159003325109167232653 35740559626246915937712245)
            ·
              refine ⟨3350677464960648369160523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35740559626246915937712245 3350677464960648369160523)
              ·
                refine ⟨5026016197440972553740785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350677464960648369160523 5026016197440972553740785)
                ·
                  refine ⟨3769512148080729415305589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5026016197440972553740785 3769512148080729415305589)
                  ·
                    refine ⟨353391763882568382684899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3769512148080729415305589 353391763882568382684899)
                    ·
                      rfl

theorem cell23_2064684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_2064684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064684 prefixEnd_2064684 := by exact prefixLift 2064684
  have htrace : WordTrace (prefixWord ++ tailWord_2064684) baseStart_2064684 baseEnd_2064684 := by
    simpa [prefixWord, tailWord_2064684, baseEnd_2064684] using wordTrace_append hprefix tailTrace_2064684
  have hstable : (prefixWord ++ tailWord_2064684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064684).length < 2 ^ (prefixWord ++ tailWord_2064684).sum := by decide
  have hdescent : baseEnd_2064684 < baseStart_2064684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064707 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5]
def baseStart_2064707 : Nat := 118140960795 + 2064707 * 2 ^ 59
def prefixEnd_2064707 : Nat := 4983230072969 + 3 ^ 40 * 2064707 * 2
def baseEnd_2064707 : Nat := 1060187101702758558067091

theorem tailTrace_2064707 : CollatzResearch.WordTrace tailWord_2064707 prefixEnd_2064707 1060187101702758558067091 := by
  unfold tailWord_2064707
  simp only [CollatzResearch.WordTrace]
  refine ⟨75306050930926637726888375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50204033953951091817925583 75306050930926637726888375)
  ·
    refine ⟨112959076396389956590332563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75306050930926637726888375 112959076396389956590332563)
    ·
      refine ⟨169438614594584934885498845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112959076396389956590332563 169438614594584934885498845)
      ·
        refine ⟨63539480472969350582062067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169438614594584934885498845 63539480472969350582062067)
        ·
          refine ⟨95309220709454025873093101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63539480472969350582062067 95309220709454025873093101)
          ·
            refine ⟨35740957766045259702409913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95309220709454025873093101 35740957766045259702409913)
            ·
              refine ⟨26805718324533944776807435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35740957766045259702409913 26805718324533944776807435)
              ·
                refine ⟨40208577486800917165211153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26805718324533944776807435 40208577486800917165211153)
                ·
                  refine ⟨30156433115100687873908365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40208577486800917165211153 30156433115100687873908365)
                  ·
                    refine ⟨11308662418162757952715637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30156433115100687873908365 11308662418162757952715637)
                    ·
                      refine ⟨1060187101702758558067091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11308662418162757952715637 1060187101702758558067091)
                      ·
                        rfl

theorem cell23_2064707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_2064707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064707 prefixEnd_2064707 := by exact prefixLift 2064707
  have htrace : WordTrace (prefixWord ++ tailWord_2064707) baseStart_2064707 baseEnd_2064707 := by
    simpa [prefixWord, tailWord_2064707, baseEnd_2064707] using wordTrace_append hprefix tailTrace_2064707
  have hstable : (prefixWord ++ tailWord_2064707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064707).length < 2 ^ (prefixWord ++ tailWord_2064707).sum := by decide
  have hdescent : baseEnd_2064707 < baseStart_2064707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064721 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 2, 4, 2]
def baseStart_2064721 : Nat := 118140960795 + 2064721 * 2 ^ 59
def prefixEnd_2064721 : Nat := 4983230072969 + 3 ^ 40 * 2064721 * 2
def baseEnd_2064721 : Nat := 1060194290431921503292027

theorem tailTrace_2064721 : CollatzResearch.WordTrace tailWord_2064721 prefixEnd_2064721 1060194290431921503292027 := by
  unfold tailWord_2064721
  simp only [CollatzResearch.WordTrace]
  refine ⟨75306561552875918117898017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50204374368583945411932011 75306561552875918117898017)
  ·
    refine ⟨56479921164656938588423513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75306561552875918117898017 56479921164656938588423513)
    ·
      refine ⟨42359940873492703941317635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56479921164656938588423513 42359940873492703941317635)
      ·
        refine ⟨63539911310239055911976453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42359940873492703941317635 63539911310239055911976453)
        ·
          refine ⟨11913733370669822983495585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63539911310239055911976453 11913733370669822983495585)
          ·
            refine ⟨8935300028002367237621689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11913733370669822983495585 8935300028002367237621689)
            ·
              refine ⟨6701475021001775428216267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8935300028002367237621689 6701475021001775428216267)
              ·
                refine ⟨10052212531502663142324401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701475021001775428216267 10052212531502663142324401)
                ·
                  refine ⟨7539159398626997356743301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10052212531502663142324401 7539159398626997356743301)
                  ·
                    refine ⟨1413592387242562004389369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539159398626997356743301 1413592387242562004389369)
                    ·
                      refine ⟨1060194290431921503292027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413592387242562004389369 1060194290431921503292027)
                      ·
                        rfl

theorem cell23_2064721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_2064721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064721 prefixEnd_2064721 := by exact prefixLift 2064721
  have htrace : WordTrace (prefixWord ++ tailWord_2064721) baseStart_2064721 baseEnd_2064721 := by
    simpa [prefixWord, tailWord_2064721, baseEnd_2064721] using wordTrace_append hprefix tailTrace_2064721
  have hstable : (prefixWord ++ tailWord_2064721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064721).length < 2 ^ (prefixWord ++ tailWord_2064721).sum := by decide
  have hdescent : baseEnd_2064721 < baseStart_2064721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064737 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_2064737 : Nat := 118140960795 + 2064737 * 2 ^ 59
def prefixEnd_2064737 : Nat := 4983230072969 + 3 ^ 40 * 2064737 * 2
def baseEnd_2064737 : Nat := 1060202506122393440691953

theorem tailTrace_2064737 : CollatzResearch.WordTrace tailWord_2064737 prefixEnd_2064737 1060202506122393440691953 := by
  unfold tailWord_2064737
  simp only [CollatzResearch.WordTrace]
  refine ⟨75307145120817952850480465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50204763413878635233653643 75307145120817952850480465)
  ·
    refine ⟨56480358840613464637860349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75307145120817952850480465 56480358840613464637860349)
    ·
      refine ⟨21180134565230049239197631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56480358840613464637860349 21180134565230049239197631)
      ·
        refine ⟨31770201847845073858796447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21180134565230049239197631 31770201847845073858796447)
        ·
          refine ⟨47655302771767610788194671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31770201847845073858796447 47655302771767610788194671)
          ·
            refine ⟨71482954157651416182292007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47655302771767610788194671 71482954157651416182292007)
            ·
              refine ⟨107224431236477124273438011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71482954157651416182292007 107224431236477124273438011)
              ·
                refine ⟨160836646854715686410157017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107224431236477124273438011 160836646854715686410157017)
                ·
                  refine ⟨120627485141036764807617763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160836646854715686410157017 120627485141036764807617763)
                  ·
                    refine ⟨180941227711555147211426645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120627485141036764807617763 180941227711555147211426645)
                    ·
                      refine ⟨1060202506122393440691953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 180941227711555147211426645 1060202506122393440691953)
                      ·
                        rfl

theorem cell23_2064737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_2064737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064737 prefixEnd_2064737 := by exact prefixLift 2064737
  have htrace : WordTrace (prefixWord ++ tailWord_2064737) baseStart_2064737 baseEnd_2064737 := by
    simpa [prefixWord, tailWord_2064737, baseEnd_2064737] using wordTrace_append hprefix tailTrace_2064737
  have hstable : (prefixWord ++ tailWord_2064737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064737).length < 2 ^ (prefixWord ++ tailWord_2064737).sum := by decide
  have hdescent : baseEnd_2064737 < baseStart_2064737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064744 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 8]
def baseStart_2064744 : Nat := 118140960795 + 2064744 * 2 ^ 59
def prefixEnd_2064744 : Nat := 4983230072969 + 3 ^ 40 * 2064744 * 2
def baseEnd_2064744 : Nat := 117800677831886101478269

theorem tailTrace_2064744 : CollatzResearch.WordTrace tailWord_2064744 prefixEnd_2064744 117800677831886101478269 := by
  unfold tailWord_2064744
  simp only [CollatzResearch.WordTrace]
  refine ⟨37653700215896296522992643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50204933621195062030656857 37653700215896296522992643)
  ·
    refine ⟨56480550323844444784488965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37653700215896296522992643 56480550323844444784488965)
    ·
      refine ⟨10590103185720833397091681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56480550323844444784488965 10590103185720833397091681)
      ·
        refine ⟨7942577389290625047818761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10590103185720833397091681 7942577389290625047818761)
        ·
          refine ⟨5956933041967968785864071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7942577389290625047818761 5956933041967968785864071)
          ·
            refine ⟨8935399562951953178796107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956933041967968785864071 8935399562951953178796107)
            ·
              refine ⟨13403099344427929768194161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935399562951953178796107 13403099344427929768194161)
              ·
                refine ⟨10052324508320947326145621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13403099344427929768194161 10052324508320947326145621)
                ·
                  refine ⟨117800677831886101478269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10052324508320947326145621 117800677831886101478269)
                  ·
                    rfl

theorem cell23_2064744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_2064744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064744 prefixEnd_2064744 := by exact prefixLift 2064744
  have htrace : WordTrace (prefixWord ++ tailWord_2064744) baseStart_2064744 baseEnd_2064744 := by
    simpa [prefixWord, tailWord_2064744, baseEnd_2064744] using wordTrace_append hprefix tailTrace_2064744
  have hstable : (prefixWord ++ tailWord_2064744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064744).length < 2 ^ (prefixWord ++ tailWord_2064744).sum := by decide
  have hdescent : baseEnd_2064744 < baseStart_2064744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064747 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6]
def baseStart_2064747 : Nat := 118140960795 + 2064747 * 2 ^ 59
def prefixEnd_2064747 : Nat := 4983230072969 + 3 ^ 40 * 2064747 * 2
def baseEnd_2064747 : Nat := 1060207640928938401566907

theorem tailTrace_2064747 : CollatzResearch.WordTrace tailWord_2064747 prefixEnd_2064747 1060207640928938401566907 := by
  unfold tailWord_2064747
  simp only [CollatzResearch.WordTrace]
  refine ⟨75307509850781724558344495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50205006567187816372229663 75307509850781724558344495)
  ·
    refine ⟨112961264776172586837516743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75307509850781724558344495 112961264776172586837516743)
    ·
      refine ⟨169441897164258880256275115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112961264776172586837516743 169441897164258880256275115)
      ·
        refine ⟨254162845746388320384412673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169441897164258880256275115 254162845746388320384412673)
        ·
          refine ⟨190622134309791240288309505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254162845746388320384412673 190622134309791240288309505)
          ·
            refine ⟨142966600732343430216232129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190622134309791240288309505 142966600732343430216232129)
            ·
              refine ⟨107224950549257572662174097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142966600732343430216232129 107224950549257572662174097)
              ·
                refine ⟨80418712911943179496630573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107224950549257572662174097 80418712911943179496630573)
                ·
                  refine ⟨30157017341978692311236465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80418712911943179496630573 30157017341978692311236465)
                  ·
                    refine ⟨22617763006484019233427349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30157017341978692311236465 22617763006484019233427349)
                    ·
                      refine ⟨1060207640928938401566907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22617763006484019233427349 1060207640928938401566907)
                      ·
                        rfl

theorem cell23_2064747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_2064747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064747 prefixEnd_2064747 := by exact prefixLift 2064747
  have htrace : WordTrace (prefixWord ++ tailWord_2064747) baseStart_2064747 baseEnd_2064747 := by
    simpa [prefixWord, tailWord_2064747, baseEnd_2064747] using wordTrace_append hprefix tailTrace_2064747
  have hstable : (prefixWord ++ tailWord_2064747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064747).length < 2 ^ (prefixWord ++ tailWord_2064747).sum := by decide
  have hdescent : baseEnd_2064747 < baseStart_2064747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064765 : List Nat := [1, 4, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_2064765 : Nat := 118140960795 + 2064765 * 2 ^ 59
def prefixEnd_2064765 : Nat := 4983230072969 + 3 ^ 40 * 2064765 * 2
def baseEnd_2064765 : Nat := 353405627860239777047275

theorem tailTrace_2064765 : CollatzResearch.WordTrace tailWord_2064765 prefixEnd_2064765 353405627860239777047275 := by
  unfold tailWord_2064765
  simp only [CollatzResearch.WordTrace]
  refine ⟨75308166364716513632499749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50205444243144342421666499 75308166364716513632499749)
  ·
    refine ⟨14120281193384346306093703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75308166364716513632499749 14120281193384346306093703)
    ·
      refine ⟨21180421790076519459140555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120281193384346306093703 21180421790076519459140555)
      ·
        refine ⟨31770632685114779188710833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21180421790076519459140555 31770632685114779188710833)
        ·
          refine ⟨23827974513836084391533125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31770632685114779188710833 23827974513836084391533125)
          ·
            refine ⟨4467745221344265823412461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23827974513836084391533125 4467745221344265823412461)
            ·
              refine ⟨1675404458004099683779673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4467745221344265823412461 1675404458004099683779673)
              ·
                refine ⟨1256553343503074762834755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675404458004099683779673 1256553343503074762834755)
                ·
                  refine ⟨1884830015254612144252133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256553343503074762834755 1884830015254612144252133)
                  ·
                    refine ⟨353405627860239777047275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1884830015254612144252133 353405627860239777047275)
                    ·
                      rfl

theorem cell23_2064765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_2064765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064765 prefixEnd_2064765 := by exact prefixLift 2064765
  have htrace : WordTrace (prefixWord ++ tailWord_2064765) baseStart_2064765 baseEnd_2064765 := by
    simpa [prefixWord, tailWord_2064765, baseEnd_2064765] using wordTrace_append hprefix tailTrace_2064765
  have hstable : (prefixWord ++ tailWord_2064765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064765).length < 2 ^ (prefixWord ++ tailWord_2064765).sum := by decide
  have hdescent : baseEnd_2064765 < baseStart_2064765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064778 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_2064778 : Nat := 118140960795 + 2064778 * 2 ^ 59
def prefixEnd_2064778 : Nat := 4983230072969 + 3 ^ 40 * 2064778 * 2
def baseEnd_2064778 : Nat := 117802617647691975586585

theorem tailTrace_2064778 : CollatzResearch.WordTrace tailWord_2064778 prefixEnd_2064778 117802617647691975586585 := by
  unfold tailWord_2064778
  simp only [CollatzResearch.WordTrace]
  refine ⟨18827160128417354213180747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50205760342446277901815325 18827160128417354213180747)
  ·
    refine ⟨28240740192626031319771121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18827160128417354213180747 28240740192626031319771121)
    ·
      refine ⟨21180555144469523489828341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28240740192626031319771121 21180555144469523489828341)
      ·
        refine ⟨1985677044794017827171407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21180555144469523489828341 1985677044794017827171407)
        ·
          refine ⟨2978515567191026740757111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985677044794017827171407 2978515567191026740757111)
          ·
            refine ⟨4467773350786540111135667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978515567191026740757111 4467773350786540111135667)
            ·
              refine ⟨6701660026179810166703501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467773350786540111135667 6701660026179810166703501)
              ·
                refine ⟨2513122509817428812513813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6701660026179810166703501 2513122509817428812513813)
                ·
                  refine ⟨117802617647691975586585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2513122509817428812513813 117802617647691975586585)
                  ·
                    rfl

theorem cell23_2064778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_2064778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064778 prefixEnd_2064778 := by exact prefixLift 2064778
  have htrace : WordTrace (prefixWord ++ tailWord_2064778) baseStart_2064778 baseEnd_2064778 := by
    simpa [prefixWord, tailWord_2064778, baseEnd_2064778] using wordTrace_append hprefix tailTrace_2064778
  have hstable : (prefixWord ++ tailWord_2064778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064778).length < 2 ^ (prefixWord ++ tailWord_2064778).sum := by decide
  have hdescent : baseEnd_2064778 < baseStart_2064778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064791 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 1, 5]
def baseStart_2064791 : Nat := 118140960795 + 2064791 * 2 ^ 59
def prefixEnd_2064791 : Nat := 4983230072969 + 3 ^ 40 * 2064791 * 2
def baseEnd_2064791 : Nat := 353410078025912076472235

theorem tailTrace_2064791 : CollatzResearch.WordTrace tailWord_2064791 prefixEnd_2064791 353410078025912076472235 := by
  unfold tailWord_2064791
  simp only [CollatzResearch.WordTrace]
  refine ⟨75309114662622320072946227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50206076441748213381964151 75309114662622320072946227)
  ·
    refine ⟨112963671993933480109419341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75309114662622320072946227 112963671993933480109419341)
    ·
      refine ⟨42361376997725055041032253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112963671993933480109419341 42361376997725055041032253)
      ·
        refine ⟨15885516374146895640387095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42361376997725055041032253 15885516374146895640387095)
        ·
          refine ⟨23828274561220343460580643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885516374146895640387095 23828274561220343460580643)
          ·
            refine ⟨35742411841830515190870965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23828274561220343460580643 35742411841830515190870965)
            ·
              refine ⟨3350851110171610799144153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35742411841830515190870965 3350851110171610799144153)
              ·
                refine ⟨2513138332628708099358115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350851110171610799144153 2513138332628708099358115)
                ·
                  refine ⟨3769707498943062149037173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513138332628708099358115 3769707498943062149037173)
                  ·
                    refine ⟨353410078025912076472235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3769707498943062149037173 353410078025912076472235)
                    ·
                      rfl

theorem cell23_2064791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_2064791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064791 prefixEnd_2064791 := by exact prefixLift 2064791
  have htrace : WordTrace (prefixWord ++ tailWord_2064791) baseStart_2064791 baseEnd_2064791 := by
    simpa [prefixWord, tailWord_2064791, baseEnd_2064791] using wordTrace_append hprefix tailTrace_2064791
  have hstable : (prefixWord ++ tailWord_2064791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064791).length < 2 ^ (prefixWord ++ tailWord_2064791).sum := by decide
  have hdescent : baseEnd_2064791 < baseStart_2064791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064804 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_2064804 : Nat := 118140960795 + 2064804 * 2 ^ 59
def prefixEnd_2064804 : Nat := 4983230072969 + 3 ^ 40 * 2064804 * 2
def baseEnd_2064804 : Nat := 353412303108748226184715

theorem tailTrace_2064804 : CollatzResearch.WordTrace tailWord_2064804 prefixEnd_2064804 353412303108748226184715 := by
  unfold tailWord_2064804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654794405787611646584733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50206392541050148862112977 37654794405787611646584733)
  ·
    refine ⟨14120547902170354367469275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37654794405787611646584733 14120547902170354367469275)
    ·
      refine ⟨21180821853255531551203913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120547902170354367469275 21180821853255531551203913)
      ·
        refine ⟨15885616389941648663402935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21180821853255531551203913 15885616389941648663402935)
        ·
          refine ⟨23828424584912472995104403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885616389941648663402935 23828424584912472995104403)
          ·
            refine ⟨35742636877368709492656605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23828424584912472995104403 35742636877368709492656605)
            ·
              refine ⟨13403488829013266059746227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35742636877368709492656605 13403488829013266059746227)
              ·
                refine ⟨20105233243519899089619341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13403488829013266059746227 20105233243519899089619341)
                ·
                  refine ⟨7539462466319962158607253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20105233243519899089619341 7539462466319962158607253)
                  ·
                    refine ⟨353412303108748226184715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7539462466319962158607253 353412303108748226184715)
                    ·
                      rfl

theorem cell23_2064804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_2064804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064804 prefixEnd_2064804 := by exact prefixLift 2064804
  have htrace : WordTrace (prefixWord ++ tailWord_2064804) baseStart_2064804 baseEnd_2064804 := by
    simpa [prefixWord, tailWord_2064804, baseEnd_2064804] using wordTrace_append hprefix tailTrace_2064804
  have hstable : (prefixWord ++ tailWord_2064804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064804).length < 2 ^ (prefixWord ++ tailWord_2064804).sum := by decide
  have hdescent : baseEnd_2064804 < baseStart_2064804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064824 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_2064824 : Nat := 118140960795 + 2064824 * 2 ^ 59
def prefixEnd_2064824 : Nat := 4983230072969 + 3 ^ 40 * 2064824 * 2
def baseEnd_2064824 : Nat := 1060247178939334600304053

theorem tailTrace_2064824 : CollatzResearch.WordTrace tailWord_2064824 prefixEnd_2064824 1060247178939334600304053 := by
  unfold tailWord_2064824
  simp only [CollatzResearch.WordTrace]
  refine ⟨37655159135751383354448763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50206878847668511139265017 37655159135751383354448763)
  ·
    refine ⟨56482738703627075031673145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37655159135751383354448763 56482738703627075031673145)
    ·
      refine ⟨42362054027720306273754859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56482738703627075031673145 42362054027720306273754859)
      ·
        refine ⟨63543081041580459410632289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42362054027720306273754859 63543081041580459410632289)
        ·
          refine ⟨47657310781185344557974217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63543081041580459410632289 47657310781185344557974217)
          ·
            refine ⟨35742983085889008418480663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47657310781185344557974217 35742983085889008418480663)
            ·
              refine ⟨53614474628833512627720995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35742983085889008418480663 53614474628833512627720995)
              ·
                refine ⟨80421711943250268941581493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53614474628833512627720995 80421711943250268941581493)
                ·
                  refine ⟨7539535494679712713273265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80421711943250268941581493 7539535494679712713273265)
                  ·
                    refine ⟨5654651621009784534954949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7539535494679712713273265 5654651621009784534954949)
                    ·
                      refine ⟨1060247178939334600304053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5654651621009784534954949 1060247178939334600304053)
                      ·
                        rfl

theorem cell23_2064824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_2064824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064824 prefixEnd_2064824 := by exact prefixLift 2064824
  have htrace : WordTrace (prefixWord ++ tailWord_2064824) baseStart_2064824 baseEnd_2064824 := by
    simpa [prefixWord, tailWord_2064824, baseEnd_2064824] using wordTrace_append hprefix tailTrace_2064824
  have hstable : (prefixWord ++ tailWord_2064824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064824).length < 2 ^ (prefixWord ++ tailWord_2064824).sum := by decide
  have hdescent : baseEnd_2064824 < baseStart_2064824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064895 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 2, 1, 3]
def baseStart_2064895 : Nat := 118140960795 + 2064895 * 2 ^ 59
def prefixEnd_2064895 : Nat := 4983230072969 + 3 ^ 40 * 2064895 * 2
def baseEnd_2064895 : Nat := 1060283636065803822516227

theorem tailTrace_2064895 : CollatzResearch.WordTrace tailWord_2064895 prefixEnd_2064895 1060283636065803822516227 := by
  unfold tailWord_2064895
  simp only [CollatzResearch.WordTrace]
  refine ⟨75312907854245545834732139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50208605236163697223154759 75312907854245545834732139)
  ·
    refine ⟨112969361781368318752098209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75312907854245545834732139 112969361781368318752098209)
    ·
      refine ⟨84727021336026239064073657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112969361781368318752098209 84727021336026239064073657)
      ·
        refine ⟨63545266002019679298055243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84727021336026239064073657 63545266002019679298055243)
        ·
          refine ⟨95317899003029518947082865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63545266002019679298055243 95317899003029518947082865)
          ·
            refine ⟨71488424252272139210312149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95317899003029518947082865 71488424252272139210312149)
            ·
              refine ⟨1675509943412628262741691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71488424252272139210312149 1675509943412628262741691)
              ·
                refine ⟨2513264915118942394112537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675509943412628262741691 2513264915118942394112537)
                ·
                  refine ⟨1884948686339206795584403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2513264915118942394112537 1884948686339206795584403)
                  ·
                    refine ⟨2827423029508810193376605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1884948686339206795584403 2827423029508810193376605)
                    ·
                      refine ⟨1060283636065803822516227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2827423029508810193376605 1060283636065803822516227)
                      ·
                        rfl

theorem cell23_2064895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_2064895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064895 prefixEnd_2064895 := by exact prefixLift 2064895
  have htrace : WordTrace (prefixWord ++ tailWord_2064895) baseStart_2064895 baseEnd_2064895 := by
    simpa [prefixWord, tailWord_2064895, baseEnd_2064895] using wordTrace_append hprefix tailTrace_2064895
  have hstable : (prefixWord ++ tailWord_2064895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064895).length < 2 ^ (prefixWord ++ tailWord_2064895).sum := by decide
  have hdescent : baseEnd_2064895 < baseStart_2064895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064902 : List Nat := [6, 2, 1, 1, 1, 1, 4, 7]
def baseStart_2064902 : Nat := 118140960795 + 2064902 * 2 ^ 59
def prefixEnd_2064902 : Nat := 4983230072969 + 3 ^ 40 * 2064902 * 2
def baseEnd_2064902 : Nat := 39269897423347603523285

theorem tailTrace_2064902 : CollatzResearch.WordTrace tailWord_2064902 prefixEnd_2064902 39269897423347603523285 := by
  unfold tailWord_2064902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353536348913130813444905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50208775443480124020157973 2353536348913130813444905)
  ·
    refine ⟨1765152261684848110083679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2353536348913130813444905 1765152261684848110083679)
    ·
      refine ⟨2647728392527272165125519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1765152261684848110083679 2647728392527272165125519)
      ·
        refine ⟨3971592588790908247688279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647728392527272165125519 3971592588790908247688279)
        ·
          refine ⟨5957388883186362371532419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971592588790908247688279 5957388883186362371532419)
          ·
            refine ⟨8936083324779543557298629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957388883186362371532419 8936083324779543557298629)
            ·
              refine ⟨1675515623396164416993493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8936083324779543557298629 1675515623396164416993493)
              ·
                refine ⟨39269897423347603523285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1675515623396164416993493 39269897423347603523285)
                ·
                  rfl

theorem cell23_2064902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_2064902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064902 prefixEnd_2064902 := by exact prefixLift 2064902
  have htrace : WordTrace (prefixWord ++ tailWord_2064902) baseStart_2064902 baseEnd_2064902 := by
    simpa [prefixWord, tailWord_2064902, baseEnd_2064902] using wordTrace_append hprefix tailTrace_2064902
  have hstable : (prefixWord ++ tailWord_2064902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064902).length < 2 ^ (prefixWord ++ tailWord_2064902).sum := by decide
  have hdescent : baseEnd_2064902 < baseStart_2064902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064951 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_2064951 : Nat := 118140960795 + 2064951 * 2 ^ 59
def prefixEnd_2064951 : Nat := 4983230072969 + 3 ^ 40 * 2064951 * 2
def baseEnd_2064951 : Nat := 1060312390982455603415969

theorem tailTrace_2064951 : CollatzResearch.WordTrace tailWord_2064951 prefixEnd_2064951 1060312390982455603415969 := by
  unfold tailWord_2064951
  simp only [CollatzResearch.WordTrace]
  refine ⟨75314950342042667398770707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50209966894695111599180471 75314950342042667398770707)
  ·
    refine ⟨112972425513064001098156061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75314950342042667398770707 112972425513064001098156061)
    ·
      refine ⟨42364659567399000411808523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112972425513064001098156061 42364659567399000411808523)
      ·
        refine ⟨63546989351098500617712785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42364659567399000411808523 63546989351098500617712785)
        ·
          refine ⟨47660242013323875463284589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63546989351098500617712785 47660242013323875463284589)
          ·
            refine ⟨17872590754996453298731721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47660242013323875463284589 17872590754996453298731721)
            ·
              refine ⟨13404443066247339974048791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17872590754996453298731721 13404443066247339974048791)
              ·
                refine ⟨20106664599371009961073187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13404443066247339974048791 20106664599371009961073187)
                ·
                  refine ⟨30159996899056514941609781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20106664599371009961073187 30159996899056514941609781)
                  ·
                    refine ⟨2827499709286548275775917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30159996899056514941609781 2827499709286548275775917)
                    ·
                      refine ⟨1060312390982455603415969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2827499709286548275775917 1060312390982455603415969)
                      ·
                        rfl

theorem cell23_2064951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_2064951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064951 prefixEnd_2064951 := by exact prefixLift 2064951
  have htrace : WordTrace (prefixWord ++ tailWord_2064951) baseStart_2064951 baseEnd_2064951 := by
    simpa [prefixWord, tailWord_2064951, baseEnd_2064951] using wordTrace_append hprefix tailTrace_2064951
  have hstable : (prefixWord ++ tailWord_2064951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064951).length < 2 ^ (prefixWord ++ tailWord_2064951).sum := by decide
  have hdescent : baseEnd_2064951 < baseStart_2064951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064971 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 2, 5]
def baseStart_2064971 : Nat := 118140960795 + 2064971 * 2 ^ 59
def prefixEnd_2064971 : Nat := 4983230072969 + 3 ^ 40 * 2064971 * 2
def baseEnd_2064971 : Nat := 353440886865181841721959

theorem tailTrace_2064971 : CollatzResearch.WordTrace tailWord_2064971 prefixEnd_2064971 353440886865181841721959 := by
  unfold tailWord_2064971
  simp only [CollatzResearch.WordTrace]
  refine ⟨75315679801970210814498767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50210453201313473876332511 75315679801970210814498767)
  ·
    refine ⟨112973519702955316221748151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75315679801970210814498767 112973519702955316221748151)
    ·
      refine ⟨169460279554432974332622227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112973519702955316221748151 169460279554432974332622227)
      ·
        refine ⟨254190419331649461498933341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169460279554432974332622227 254190419331649461498933341)
        ·
          refine ⟨95321407249368548062100003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254190419331649461498933341 95321407249368548062100003)
          ·
            refine ⟨142982110874052822093150005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95321407249368548062100003 142982110874052822093150005)
            ·
              refine ⟨13404572894442452071232813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142982110874052822093150005 13404572894442452071232813)
              ·
                refine ⟨5026714835415919526712305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13404572894442452071232813 5026714835415919526712305)
                ·
                  refine ⟨3770036126561939645034229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5026714835415919526712305 3770036126561939645034229)
                  ·
                    refine ⟨353440886865181841721959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3770036126561939645034229 353440886865181841721959)
                    ·
                      rfl

theorem cell23_2064971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 5].length) (baseStart_2064971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064971 prefixEnd_2064971 := by exact prefixLift 2064971
  have htrace : WordTrace (prefixWord ++ tailWord_2064971) baseStart_2064971 baseEnd_2064971 := by
    simpa [prefixWord, tailWord_2064971, baseEnd_2064971] using wordTrace_append hprefix tailTrace_2064971
  have hstable : (prefixWord ++ tailWord_2064971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064971).length < 2 ^ (prefixWord ++ tailWord_2064971).sum := by decide
  have hdescent : baseEnd_2064971 < baseStart_2064971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064981 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2064981 : Nat := 118140960795 + 2064981 * 2 ^ 59
def prefixEnd_2064981 : Nat := 4983230072969 + 3 ^ 40 * 2064981 * 2
def baseEnd_2064981 : Nat := 1060327795402090486040831

theorem tailTrace_2064981 : CollatzResearch.WordTrace tailWord_2064981 prefixEnd_2064981 1060327795402090486040831 := by
  unfold tailWord_2064981
  simp only [CollatzResearch.WordTrace]
  refine ⟨75316044531933982522362797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50210696354622655014908531 75316044531933982522362797)
  ·
    refine ⟨28243516699475243445886049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75316044531933982522362797 28243516699475243445886049)
    ·
      refine ⟨21182637524606432584414537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28243516699475243445886049 21182637524606432584414537)
      ·
        refine ⟨15886978143454824438310903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21182637524606432584414537 15886978143454824438310903)
        ·
          refine ⟨23830467215182236657466355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15886978143454824438310903 23830467215182236657466355)
          ·
            refine ⟨35745700822773354986199533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23830467215182236657466355 35745700822773354986199533)
            ·
              refine ⟨13404637808540008119824825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35745700822773354986199533 13404637808540008119824825)
              ·
                refine ⟨10053478356405006089868619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13404637808540008119824825 10053478356405006089868619)
                ·
                  refine ⟨15080217534607509134802929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10053478356405006089868619 15080217534607509134802929)
                  ·
                    refine ⟨11310163150955631851102197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15080217534607509134802929 11310163150955631851102197)
                    ·
                      refine ⟨1060327795402090486040831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11310163150955631851102197 1060327795402090486040831)
                      ·
                        rfl

theorem cell23_2064981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2064981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2064981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2064981 prefixEnd_2064981 := by exact prefixLift 2064981
  have htrace : WordTrace (prefixWord ++ tailWord_2064981) baseStart_2064981 baseEnd_2064981 := by
    simpa [prefixWord, tailWord_2064981, baseEnd_2064981] using wordTrace_append hprefix tailTrace_2064981
  have hstable : (prefixWord ++ tailWord_2064981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064981).length < 2 ^ (prefixWord ++ tailWord_2064981).sum := by decide
  have hdescent : baseEnd_2064981 < baseStart_2064981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065026 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2065026 : Nat := 118140960795 + 2065026 * 2 ^ 59
def prefixEnd_2065026 : Nat := 4983230072969 + 3 ^ 40 * 2065026 * 2
def baseEnd_2065026 : Nat := 117816766892393645553125

theorem tailTrace_2065026 : CollatzResearch.WordTrace tailWord_2065026 prefixEnd_2065026 117816766892393645553125 := by
  unfold tailWord_2065026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18829421454192738801937733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50211790544513970138500621 18829421454192738801937733)
  ·
    refine ⟨3530516522661138525363325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18829421454192738801937733 3530516522661138525363325)
    ·
      refine ⟨1323943695997926947011247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3530516522661138525363325 1323943695997926947011247)
      ·
        refine ⟨1985915543996890420516871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323943695997926947011247 1985915543996890420516871)
        ·
          refine ⟨2978873315995335630775307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985915543996890420516871 2978873315995335630775307)
          ·
            refine ⟨4468309973993003446162961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978873315995335630775307 4468309973993003446162961)
            ·
              refine ⟨3351232480494752584622221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4468309973993003446162961 3351232480494752584622221)
              ·
                refine ⟨1256712180185532219233333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3351232480494752584622221 1256712180185532219233333)
                ·
                  refine ⟨117816766892393645553125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1256712180185532219233333 117816766892393645553125)
                  ·
                    rfl

theorem cell23_2065026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2065026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065026 prefixEnd_2065026 := by exact prefixLift 2065026
  have htrace : WordTrace (prefixWord ++ tailWord_2065026) baseStart_2065026 baseEnd_2065026 := by
    simpa [prefixWord, tailWord_2065026, baseEnd_2065026] using wordTrace_append hprefix tailTrace_2065026
  have hstable : (prefixWord ++ tailWord_2065026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065026).length < 2 ^ (prefixWord ++ tailWord_2065026).sum := by decide
  have hdescent : baseEnd_2065026 < baseStart_2065026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065031 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 8]
def baseStart_2065031 : Nat := 118140960795 + 2065031 * 2 ^ 59
def prefixEnd_2065031 : Nat := 4983230072969 + 3 ^ 40 * 2065031 * 2
def baseEnd_2065031 : Nat := 117817052159423921157289

theorem tailTrace_2065031 : CollatzResearch.WordTrace tailWord_2065031 prefixEnd_2065031 117817052159423921157289 := by
  unfold tailWord_2065031
  simp only [CollatzResearch.WordTrace]
  refine ⟨75317868181752841061682947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50211912121168560707788631 75317868181752841061682947)
  ·
    refine ⟨112976802272629261592524421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75317868181752841061682947 112976802272629261592524421)
    ·
      refine ⟨21183150426117986548598329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112976802272629261592524421 21183150426117986548598329)
      ·
        refine ⟨15887362819588489911448747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21183150426117986548598329 15887362819588489911448747)
        ·
          refine ⟨23831044229382734867173121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15887362819588489911448747 23831044229382734867173121)
          ·
            refine ⟨17873283172037051150379841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23831044229382734867173121 17873283172037051150379841)
            ·
              refine ⟨13404962379027788362784881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17873283172037051150379841 13404962379027788362784881)
              ·
                refine ⟨10053721784270841272088661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13404962379027788362784881 10053721784270841272088661)
                ·
                  refine ⟨117817052159423921157289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10053721784270841272088661 117817052159423921157289)
                  ·
                    rfl

theorem cell23_2065031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 8].length) (baseStart_2065031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065031 prefixEnd_2065031 := by exact prefixLift 2065031
  have htrace : WordTrace (prefixWord ++ tailWord_2065031) baseStart_2065031 baseEnd_2065031 := by
    simpa [prefixWord, tailWord_2065031, baseEnd_2065031] using wordTrace_append hprefix tailTrace_2065031
  have hstable : (prefixWord ++ tailWord_2065031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065031).length < 2 ^ (prefixWord ++ tailWord_2065031).sum := by decide
  have hdescent : baseEnd_2065031 < baseStart_2065031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065052 : List Nat := [2, 2, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_2065052 : Nat := 118140960795 + 2065052 * 2 ^ 59
def prefixEnd_2065052 : Nat := 4983230072969 + 3 ^ 40 * 2065052 * 2
def baseEnd_2065052 : Nat := 353454750842853236084335

theorem tailTrace_2065052 : CollatzResearch.WordTrace tailWord_2065052 prefixEnd_2065052 353454750842853236084335 := by
  unfold tailWord_2065052
  simp only [CollatzResearch.WordTrace]
  refine ⟨37659317057338380824098705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50212422743117841098798273 37659317057338380824098705)
  ·
    refine ⟨28244487793003785618074029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37659317057338380824098705 28244487793003785618074029)
    ·
      refine ⟨10591682922376419606777761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28244487793003785618074029 10591682922376419606777761)
      ·
        refine ⟨7943762191782314705083321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10591682922376419606777761 7943762191782314705083321)
        ·
          refine ⟨5957821643836736028812491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7943762191782314705083321 5957821643836736028812491)
          ·
            refine ⟨8936732465755104043218737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957821643836736028812491 8936732465755104043218737)
            ·
              refine ⟨6702549349316328032414053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8936732465755104043218737 6702549349316328032414053)
              ·
                refine ⟨1256728002996811506077635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6702549349316328032414053 1256728002996811506077635)
                ·
                  refine ⟨1885092004495217259116453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256728002996811506077635 1885092004495217259116453)
                  ·
                    refine ⟨353454750842853236084335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885092004495217259116453 353454750842853236084335)
                    ·
                      rfl

theorem cell23_2065052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_2065052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065052 prefixEnd_2065052 := by exact prefixLift 2065052
  have htrace : WordTrace (prefixWord ++ tailWord_2065052) baseStart_2065052 baseEnd_2065052 := by
    simpa [prefixWord, tailWord_2065052, baseEnd_2065052] using wordTrace_append hprefix tailTrace_2065052
  have hstable : (prefixWord ++ tailWord_2065052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065052).length < 2 ^ (prefixWord ++ tailWord_2065052).sum := by decide
  have hdescent : baseEnd_2065052 < baseStart_2065052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065075 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 3]
def baseStart_2065075 : Nat := 118140960795 + 2065075 * 2 ^ 59
def prefixEnd_2065075 : Nat := 4983230072969 + 3 ^ 40 * 2065075 * 2
def baseEnd_2065075 : Nat := 1060376062583613118265399

theorem tailTrace_2065075 : CollatzResearch.WordTrace tailWord_2065075 prefixEnd_2065075 1060376062583613118265399 := by
  unfold tailWord_2065075
  simp only [CollatzResearch.WordTrace]
  refine ⟨75319472993593436576284679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50212981995728957717523119 75319472993593436576284679)
  ·
    refine ⟨112979209490390154864427019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75319472993593436576284679 112979209490390154864427019)
    ·
      refine ⟨169468814235585232296640529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112979209490390154864427019 169468814235585232296640529)
      ·
        refine ⟨127101610676688924222480397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169468814235585232296640529 127101610676688924222480397)
        ·
          refine ⟨47663104003758346583430149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127101610676688924222480397 47663104003758346583430149)
          ·
            refine ⟨8936832000704689984393153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47663104003758346583430149 8936832000704689984393153)
            ·
              refine ⟨6702624000528517488294865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8936832000704689984393153 6702624000528517488294865)
              ·
                refine ⟨5026968000396388116221149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702624000528517488294865 5026968000396388116221149)
                ·
                  refine ⟨1885113000148645543582931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5026968000396388116221149 1885113000148645543582931)
                  ·
                    refine ⟨2827669500222968315374397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1885113000148645543582931 2827669500222968315374397)
                    ·
                      refine ⟨1060376062583613118265399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2827669500222968315374397 1060376062583613118265399)
                      ·
                        rfl

theorem cell23_2065075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_2065075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065075 prefixEnd_2065075 := by exact prefixLift 2065075
  have htrace : WordTrace (prefixWord ++ tailWord_2065075) baseStart_2065075 baseEnd_2065075 := by
    simpa [prefixWord, tailWord_2065075, baseEnd_2065075] using wordTrace_append hprefix tailTrace_2065075
  have hstable : (prefixWord ++ tailWord_2065075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065075).length < 2 ^ (prefixWord ++ tailWord_2065075).sum := by decide
  have hdescent : baseEnd_2065075 < baseStart_2065075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065085 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_2065085 : Nat := 118140960795 + 2065085 * 2 ^ 59
def prefixEnd_2065085 : Nat := 4983230072969 + 3 ^ 40 * 2065085 * 2
def baseEnd_2065085 : Nat := 1060381197390158079140353

theorem tailTrace_2065085 : CollatzResearch.WordTrace tailWord_2065085 prefixEnd_2065085 1060381197390158079140353 := by
  unfold tailWord_2065085
  simp only [CollatzResearch.WordTrace]
  refine ⟨75319837723557208284148709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50213225149038138856099139 75319837723557208284148709)
  ·
    refine ⟨14122469573166976553277883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75319837723557208284148709 14122469573166976553277883)
    ·
      refine ⟨21183704359750464829916825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14122469573166976553277883 21183704359750464829916825)
      ·
        refine ⟨15887778269812848622437619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21183704359750464829916825 15887778269812848622437619)
        ·
          refine ⟨23831667404719272933656429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15887778269812848622437619 23831667404719272933656429)
          ·
            refine ⟨8936875276769727350121161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23831667404719272933656429 8936875276769727350121161)
            ·
              refine ⟨6702656457577295512590871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8936875276769727350121161 6702656457577295512590871)
              ·
                refine ⟨10053984686365943268886307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702656457577295512590871 10053984686365943268886307)
                ·
                  refine ⟨15080977029548914903329461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10053984686365943268886307 15080977029548914903329461)
                  ·
                    refine ⟨1413841596520210772187137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15080977029548914903329461 1413841596520210772187137)
                    ·
                      refine ⟨1060381197390158079140353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413841596520210772187137 1060381197390158079140353)
                      ·
                        rfl

theorem cell23_2065085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_2065085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065085 prefixEnd_2065085 := by exact prefixLift 2065085
  have htrace : WordTrace (prefixWord ++ tailWord_2065085) baseStart_2065085 baseEnd_2065085 := by
    simpa [prefixWord, tailWord_2065085, baseEnd_2065085] using wordTrace_append hprefix tailTrace_2065085
  have hstable : (prefixWord ++ tailWord_2065085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065085).length < 2 ^ (prefixWord ++ tailWord_2065085).sum := by decide
  have hdescent : baseEnd_2065085 < baseStart_2065085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065102 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_2065102 : Nat := 118140960795 + 2065102 * 2 ^ 59
def prefixEnd_2065102 : Nat := 4983230072969 + 3 ^ 40 * 2065102 * 2
def baseEnd_2065102 : Nat := 1060389926561284512627775

theorem tailTrace_2065102 : CollatzResearch.WordTrace tailWord_2065102 prefixEnd_2065102 1060389926561284512627775 := by
  unfold tailWord_2065102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415057220561952523439695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50213638509663746791678373 9415057220561952523439695)
  ·
    refine ⟨14122585830842928785159543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9415057220561952523439695 14122585830842928785159543)
    ·
      refine ⟨21183878746264393177739315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14122585830842928785159543 21183878746264393177739315)
      ·
        refine ⟨31775818119396589766608973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21183878746264393177739315 31775818119396589766608973)
        ·
          refine ⟨11915931794773721162478365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31775818119396589766608973 11915931794773721162478365)
          ·
            refine ⟨4468474423040145435929387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11915931794773721162478365 4468474423040145435929387)
            ·
              refine ⟨6702711634560218153894081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468474423040145435929387 6702711634560218153894081)
              ·
                refine ⟨5027033725920163615420561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702711634560218153894081 5027033725920163615420561)
                ·
                  refine ⟨3770275294440122711565421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027033725920163615420561 3770275294440122711565421)
                  ·
                    refine ⟨1413853235415046016837033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3770275294440122711565421 1413853235415046016837033)
                    ·
                      refine ⟨1060389926561284512627775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413853235415046016837033 1060389926561284512627775)
                      ·
                        rfl

theorem cell23_2065102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_2065102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065102 prefixEnd_2065102 := by exact prefixLift 2065102
  have htrace : WordTrace (prefixWord ++ tailWord_2065102) baseStart_2065102 baseEnd_2065102 := by
    simpa [prefixWord, tailWord_2065102, baseEnd_2065102] using wordTrace_append hprefix tailTrace_2065102
  have hstable : (prefixWord ++ tailWord_2065102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065102).length < 2 ^ (prefixWord ++ tailWord_2065102).sum := by decide
  have hdescent : baseEnd_2065102 < baseStart_2065102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065115 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 9, 2, 2]
def baseStart_2065115 : Nat := 118140960795 + 2065115 * 2 ^ 59
def prefixEnd_2065115 : Nat := 4983230072969 + 3 ^ 40 * 2065115 * 2
def baseEnd_2065115 : Nat := 1060396601809792961765215

theorem tailTrace_2065115 : CollatzResearch.WordTrace tailWord_2065115 prefixEnd_2065115 1060396601809792961765215 := by
  unfold tailWord_2065115
  simp only [CollatzResearch.WordTrace]
  refine ⟨75320931913448523407740799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50213954608965682271827199 75320931913448523407740799)
  ·
    refine ⟨112981397870172785111611199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75320931913448523407740799 112981397870172785111611199)
    ·
      refine ⟨169472096805259177667416799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112981397870172785111611199 169472096805259177667416799)
      ·
        refine ⟨254208145207888766501125199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169472096805259177667416799 254208145207888766501125199)
        ·
          refine ⟨381312217811833149751687799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254208145207888766501125199 381312217811833149751687799)
          ·
            refine ⟨571968326717749724627531699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381312217811833149751687799 571968326717749724627531699)
            ·
              refine ⟨857952490076624586941297549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571968326717749724627531699 857952490076624586941297549)
              ·
                refine ⟨321732183778734220102986581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857952490076624586941297549 321732183778734220102986581)
                ·
                  refine ⟨1885149514328520820915937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 321732183778734220102986581 1885149514328520820915937)
                  ·
                    refine ⟨1413862135746390615686953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1885149514328520820915937 1413862135746390615686953)
                    ·
                      refine ⟨1060396601809792961765215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413862135746390615686953 1060396601809792961765215)
                      ·
                        rfl

theorem cell23_2065115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 2, 2].length) (baseStart_2065115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065115 prefixEnd_2065115 := by exact prefixLift 2065115
  have htrace : WordTrace (prefixWord ++ tailWord_2065115) baseStart_2065115 baseEnd_2065115 := by
    simpa [prefixWord, tailWord_2065115, baseEnd_2065115] using wordTrace_append hprefix tailTrace_2065115
  have hstable : (prefixWord ++ tailWord_2065115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065115).length < 2 ^ (prefixWord ++ tailWord_2065115).sum := by decide
  have hdescent : baseEnd_2065115 < baseStart_2065115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065135 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_2065135 : Nat := 118140960795 + 2065135 * 2 ^ 59
def prefixEnd_2065135 : Nat := 4983230072969 + 3 ^ 40 * 2065135 * 2
def baseEnd_2065135 : Nat := 1060406871422882883515123

theorem tailTrace_2065135 : CollatzResearch.WordTrace tailWord_2065135 prefixEnd_2065135 1060406871422882883515123 := by
  unfold tailWord_2065135
  simp only [CollatzResearch.WordTrace]
  refine ⟨75321661373376066823468859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50214440915584044548979239 75321661373376066823468859)
  ·
    refine ⟨112982492060064100235203289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75321661373376066823468859 112982492060064100235203289)
    ·
      refine ⟨84736869045048075176402467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112982492060064100235203289 84736869045048075176402467)
      ·
        refine ⟨127105303567572112764603701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84736869045048075176402467 127105303567572112764603701)
        ·
          refine ⟨11916122209459885571681597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127105303567572112764603701 11916122209459885571681597)
          ·
            refine ⟨4468545828547457089380599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11916122209459885571681597 4468545828547457089380599)
            ·
              refine ⟨6702818742821185634070899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468545828547457089380599 6702818742821185634070899)
              ·
                refine ⟨10054228114231778451106349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702818742821185634070899 10054228114231778451106349)
                ·
                  refine ⟨3770335542836916919164881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10054228114231778451106349 3770335542836916919164881)
                  ·
                    refine ⟨2827751657127687689373661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3770335542836916919164881 2827751657127687689373661)
                    ·
                      refine ⟨1060406871422882883515123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2827751657127687689373661 1060406871422882883515123)
                      ·
                        rfl

theorem cell23_2065135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_2065135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065135 prefixEnd_2065135 := by exact prefixLift 2065135
  have htrace : WordTrace (prefixWord ++ tailWord_2065135) baseStart_2065135 baseEnd_2065135 := by
    simpa [prefixWord, tailWord_2065135, baseEnd_2065135] using wordTrace_append hprefix tailTrace_2065135
  have hstable : (prefixWord ++ tailWord_2065135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065135).length < 2 ^ (prefixWord ++ tailWord_2065135).sum := by decide
  have hdescent : baseEnd_2065135 < baseStart_2065135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065138 : List Nat := [3, 2, 1, 3, 1, 2, 2, 9]
def baseStart_2065138 : Nat := 118140960795 + 2065138 * 2 ^ 59
def prefixEnd_2065138 : Nat := 4983230072969 + 3 ^ 40 * 2065138 * 2
def baseEnd_2065138 : Nat := 39274385624623939695467

theorem tailTrace_2065138 : CollatzResearch.WordTrace tailWord_2065138 prefixEnd_2065138 39274385624623939695467 := by
  unfold tailWord_2065138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18830442698091299583957017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50214513861576798890552045 18830442698091299583957017)
  ·
    refine ⟨14122832023568474687967763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18830442698091299583957017 14122832023568474687967763)
    ·
      refine ⟨21184248035352712031951645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14122832023568474687967763 21184248035352712031951645)
      ·
        refine ⟨7944093013257267011981867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21184248035352712031951645 7944093013257267011981867)
        ·
          refine ⟨11916139519885900517972801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944093013257267011981867 11916139519885900517972801)
          ·
            refine ⟨8937104639914425388479601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916139519885900517972801 8937104639914425388479601)
            ·
              refine ⟨6702828479935819041359701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937104639914425388479601 6702828479935819041359701)
              ·
                refine ⟨39274385624623939695467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6702828479935819041359701 39274385624623939695467)
                ·
                  rfl

theorem cell23_2065138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_2065138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065138 prefixEnd_2065138 := by exact prefixLift 2065138
  have htrace : WordTrace (prefixWord ++ tailWord_2065138) baseStart_2065138 baseEnd_2065138 := by
    simpa [prefixWord, tailWord_2065138, baseEnd_2065138] using wordTrace_append hprefix tailTrace_2065138
  have hstable : (prefixWord ++ tailWord_2065138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065138).length < 2 ^ (prefixWord ++ tailWord_2065138).sum := by decide
  have hdescent : baseEnd_2065138 < baseStart_2065138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065149 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_2065149 : Nat := 118140960795 + 2065149 * 2 ^ 59
def prefixEnd_2065149 : Nat := 4983230072969 + 3 ^ 40 * 2065149 * 2
def baseEnd_2065149 : Nat := 1060414060152045828740059

theorem tailTrace_2065149 : CollatzResearch.WordTrace tailWord_2065149 prefixEnd_2065149 1060414060152045828740059 := by
  unfold tailWord_2065149
  simp only [CollatzResearch.WordTrace]
  refine ⟨75322171995325347214478501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50214781330216898142985667 75322171995325347214478501)
  ·
    refine ⟨14122907249123502602714719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75322171995325347214478501 14122907249123502602714719)
    ·
      refine ⟨21184360873685253904072079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14122907249123502602714719 21184360873685253904072079)
      ·
        refine ⟨31776541310527880856108119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21184360873685253904072079 31776541310527880856108119)
        ·
          refine ⟨47664811965791821284162179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31776541310527880856108119 47664811965791821284162179)
          ·
            refine ⟨71497217948687731926243269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47664811965791821284162179 71497217948687731926243269)
            ·
              refine ⟨13405728365378949736170613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71497217948687731926243269 13405728365378949736170613)
              ·
                refine ⟨1256787034254276537765995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13405728365378949736170613 1256787034254276537765995)
                ·
                  refine ⟨1885180551381414806648993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256787034254276537765995 1885180551381414806648993)
                  ·
                    refine ⟨1413885413536061104986745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1885180551381414806648993 1413885413536061104986745)
                    ·
                      refine ⟨1060414060152045828740059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413885413536061104986745 1060414060152045828740059)
                      ·
                        rfl

theorem cell23_2065149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_2065149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065149 prefixEnd_2065149 := by exact prefixLift 2065149
  have htrace : WordTrace (prefixWord ++ tailWord_2065149) baseStart_2065149 baseEnd_2065149 := by
    simpa [prefixWord, tailWord_2065149, baseEnd_2065149] using wordTrace_append hprefix tailTrace_2065149
  have hstable : (prefixWord ++ tailWord_2065149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065149).length < 2 ^ (prefixWord ++ tailWord_2065149).sum := by decide
  have hdescent : baseEnd_2065149 < baseStart_2065149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065192 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_2065192 : Nat := 118140960795 + 2065192 * 2 ^ 59
def prefixEnd_2065192 : Nat := 4983230072969 + 3 ^ 40 * 2065192 * 2
def baseEnd_2065192 : Nat := 1060436139820189160502361

theorem tailTrace_2065192 : CollatzResearch.WordTrace tailWord_2065192 prefixEnd_2065192 1060436139820189160502361 := by
  unfold tailWord_2065192
  simp only [CollatzResearch.WordTrace]
  refine ⟨37661870167084782779146915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50215826889446377038862553 37661870167084782779146915)
  ·
    refine ⟨56492805250627174168720373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37661870167084782779146915 56492805250627174168720373)
    ·
      refine ⟨5296200492246297578317535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56492805250627174168720373 5296200492246297578317535)
      ·
        refine ⟨7944300738369446367476303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296200492246297578317535 7944300738369446367476303)
        ·
          refine ⟨11916451107554169551214455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944300738369446367476303 11916451107554169551214455)
          ·
            refine ⟨17874676661331254326821683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11916451107554169551214455 17874676661331254326821683)
            ·
              refine ⟨26812014991996881490232525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17874676661331254326821683 26812014991996881490232525)
              ·
                refine ⟨10054505621998830558837197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26812014991996881490232525 10054505621998830558837197)
                ·
                  refine ⟨3770439608249561459563949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10054505621998830558837197 3770439608249561459563949)
                  ·
                    refine ⟨1413914853093585547336481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3770439608249561459563949 1413914853093585547336481)
                    ·
                      refine ⟨1060436139820189160502361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413914853093585547336481 1060436139820189160502361)
                      ·
                        rfl

theorem cell23_2065192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_2065192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065192 prefixEnd_2065192 := by exact prefixLift 2065192
  have htrace : WordTrace (prefixWord ++ tailWord_2065192) baseStart_2065192 baseEnd_2065192 := by
    simpa [prefixWord, tailWord_2065192, baseEnd_2065192] using wordTrace_append hprefix tailTrace_2065192
  have hstable : (prefixWord ++ tailWord_2065192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065192).length < 2 ^ (prefixWord ++ tailWord_2065192).sum := by decide
  have hdescent : baseEnd_2065192 < baseStart_2065192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065208 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_2065208 : Nat := 118140960795 + 2065208 * 2 ^ 59
def prefixEnd_2065208 : Nat := 4983230072969 + 3 ^ 40 * 2065208 * 2
def baseEnd_2065208 : Nat := 1060444355510661097902287

theorem tailTrace_2065208 : CollatzResearch.WordTrace tailWord_2065208 prefixEnd_2065208 1060444355510661097902287 := by
  unfold tailWord_2065208
  simp only [CollatzResearch.WordTrace]
  refine ⟨37662161951055800145438139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50216215934741066860584185 37662161951055800145438139)
  ·
    refine ⟨56493242926583700218157209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37662161951055800145438139 56493242926583700218157209)
    ·
      refine ⟨42369932194937775163617907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56493242926583700218157209 42369932194937775163617907)
      ·
        refine ⟨63554898292406662745426861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42369932194937775163617907 63554898292406662745426861)
        ·
          refine ⟨23833086859652498529535073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63554898292406662745426861 23833086859652498529535073)
          ·
            refine ⟨17874815144739373897151305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23833086859652498529535073 17874815144739373897151305)
            ·
              refine ⟨13406111358554530422863479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17874815144739373897151305 13406111358554530422863479)
              ·
                refine ⟨20109167037831795634295219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13406111358554530422863479 20109167037831795634295219)
                ·
                  refine ⟨30163750556747693451442829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20109167037831795634295219 30163750556747693451442829)
                  ·
                    refine ⟨11311406458780385044291061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30163750556747693451442829 11311406458780385044291061)
                    ·
                      refine ⟨1060444355510661097902287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11311406458780385044291061 1060444355510661097902287)
                      ·
                        rfl

theorem cell23_2065208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_2065208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065208 prefixEnd_2065208 := by exact prefixLift 2065208
  have htrace : WordTrace (prefixWord ++ tailWord_2065208) baseStart_2065208 baseEnd_2065208 := by
    simpa [prefixWord, tailWord_2065208, baseEnd_2065208] using wordTrace_append hprefix tailTrace_2065208
  have hstable : (prefixWord ++ tailWord_2065208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065208).length < 2 ^ (prefixWord ++ tailWord_2065208).sum := by decide
  have hdescent : baseEnd_2065208 < baseStart_2065208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065239 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 1, 4, 2]
def baseStart_2065239 : Nat := 118140960795 + 2065239 * 2 ^ 59
def prefixEnd_2065239 : Nat := 4983230072969 + 3 ^ 40 * 2065239 * 2
def baseEnd_2065239 : Nat := 1060460273410950476614645

theorem tailTrace_2065239 : CollatzResearch.WordTrace tailWord_2065239 prefixEnd_2065239 1060460273410950476614645 := by
  unfold tailWord_2065239
  simp only [CollatzResearch.WordTrace]
  refine ⟨75325454564999292585254771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50216969709999528390169847 75325454564999292585254771)
  ·
    refine ⟨112988181847498938877882157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75325454564999292585254771 112988181847498938877882157)
    ·
      refine ⟨42370568192812102079205809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112988181847498938877882157 42370568192812102079205809)
      ·
        refine ⟨31777926144609076559404357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42370568192812102079205809 31777926144609076559404357)
        ·
          refine ⟨5958361152114201854888317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31777926144609076559404357 5958361152114201854888317)
          ·
            refine ⟨2234385432042825695583119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5958361152114201854888317 2234385432042825695583119)
            ·
              refine ⟨3351578148064238543374679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234385432042825695583119 3351578148064238543374679)
              ·
                refine ⟨5027367222096357815062019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351578148064238543374679 5027367222096357815062019)
                ·
                  refine ⟨7541050833144536722593029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027367222096357815062019 7541050833144536722593029)
                  ·
                    refine ⟨1413947031214600635486193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541050833144536722593029 1413947031214600635486193)
                    ·
                      refine ⟨1060460273410950476614645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1413947031214600635486193 1060460273410950476614645)
                      ·
                        rfl

theorem cell23_2065239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_2065239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065239 prefixEnd_2065239 := by exact prefixLift 2065239
  have htrace : WordTrace (prefixWord ++ tailWord_2065239) baseStart_2065239 baseEnd_2065239 := by
    simpa [prefixWord, tailWord_2065239, baseEnd_2065239] using wordTrace_append hprefix tailTrace_2065239
  have hstable : (prefixWord ++ tailWord_2065239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065239).length < 2 ^ (prefixWord ++ tailWord_2065239).sum := by decide
  have hdescent : baseEnd_2065239 < baseStart_2065239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065285 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_2065285 : Nat := 118140960795 + 2065285 * 2 ^ 59
def prefixEnd_2065285 : Nat := 4983230072969 + 3 ^ 40 * 2065285 * 2
def baseEnd_2065285 : Nat := 1060483893521057296639433

theorem tailTrace_2065285 : CollatzResearch.WordTrace tailWord_2065285 prefixEnd_2065285 1060483893521057296639433 := by
  unfold tailWord_2065285
  simp only [CollatzResearch.WordTrace]
  refine ⟨75327132322832642441429309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50218088215221761627619539 75327132322832642441429309)
  ·
    refine ⟨28247674621062240915535991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75327132322832642441429309 28247674621062240915535991)
    ·
      refine ⟨42371511931593361373303987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28247674621062240915535991 42371511931593361373303987)
      ·
        refine ⟨63557267897390042059955981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42371511931593361373303987 63557267897390042059955981)
        ·
          refine ⟨23833975461521265772483493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63557267897390042059955981 23833975461521265772483493)
          ·
            refine ⟨4468870399035237332340655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23833975461521265772483493 4468870399035237332340655)
            ·
              refine ⟨6703305598552855998510983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468870399035237332340655 6703305598552855998510983)
              ·
                refine ⟨10054958397829283997766475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703305598552855998510983 10054958397829283997766475)
                ·
                  refine ⟨15082437596743925996649713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054958397829283997766475 15082437596743925996649713)
                  ·
                    refine ⟨11311828197557944497487285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15082437596743925996649713 11311828197557944497487285)
                    ·
                      refine ⟨1060483893521057296639433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11311828197557944497487285 1060483893521057296639433)
                      ·
                        rfl

theorem cell23_2065285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_2065285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065285 prefixEnd_2065285 := by exact prefixLift 2065285
  have htrace : WordTrace (prefixWord ++ tailWord_2065285) baseStart_2065285 baseEnd_2065285 := by
    simpa [prefixWord, tailWord_2065285, baseEnd_2065285] using wordTrace_append hprefix tailTrace_2065285
  have hstable : (prefixWord ++ tailWord_2065285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065285).length < 2 ^ (prefixWord ++ tailWord_2065285).sum := by decide
  have hdescent : baseEnd_2065285 < baseStart_2065285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065305 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 5, 4]
def baseStart_2065305 : Nat := 118140960795 + 2065305 * 2 ^ 59
def prefixEnd_2065305 : Nat := 4983230072969 + 3 ^ 40 * 2065305 * 2
def baseEnd_2065305 : Nat := 353498054378049072796447

theorem tailTrace_2065305 : CollatzResearch.WordTrace tailWord_2065305 prefixEnd_2065305 353498054378049072796447 := by
  unfold tailWord_2065305
  simp only [CollatzResearch.WordTrace]
  refine ⟨75327861782760185857157369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50218574521840123904771579 75327861782760185857157369)
  ·
    refine ⟨56495896337070139392868027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75327861782760185857157369 56495896337070139392868027)
    ·
      refine ⟨84743844505605209089302041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56495896337070139392868027 84743844505605209089302041)
      ·
        refine ⟨63557883379203906816976531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84743844505605209089302041 63557883379203906816976531)
        ·
          refine ⟨95336825068805860225464797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63557883379203906816976531 95336825068805860225464797)
          ·
            refine ⟨35751309400802197584549299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95336825068805860225464797 35751309400802197584549299)
            ·
              refine ⟨53626964101203296376823949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35751309400802197584549299 53626964101203296376823949)
              ·
                refine ⟨20110111537951236141308981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53626964101203296376823949 20110111537951236141308981)
                ·
                  refine ⟨1885322956682928388247717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20110111537951236141308981 1885322956682928388247717)
                  ·
                    refine ⟨353498054378049072796447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885322956682928388247717 353498054378049072796447)
                    ·
                      rfl

theorem cell23_2065305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_2065305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065305 prefixEnd_2065305 := by exact prefixLift 2065305
  have htrace : WordTrace (prefixWord ++ tailWord_2065305) baseStart_2065305 baseEnd_2065305 := by
    simpa [prefixWord, tailWord_2065305, baseEnd_2065305] using wordTrace_append hprefix tailTrace_2065305
  have hstable : (prefixWord ++ tailWord_2065305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065305).length < 2 ^ (prefixWord ++ tailWord_2065305).sum := by decide
  have hdescent : baseEnd_2065305 < baseStart_2065305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065315 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 3]
def baseStart_2065315 : Nat := 118140960795 + 2065315 * 2 ^ 59
def prefixEnd_2065315 : Nat := 4983230072969 + 3 ^ 40 * 2065315 * 2
def baseEnd_2065315 : Nat := 1060499297940692179264295

theorem tailTrace_2065315 : CollatzResearch.WordTrace tailWord_2065315 prefixEnd_2065315 1060499297940692179264295 := by
  unfold tailWord_2065315
  simp only [CollatzResearch.WordTrace]
  refine ⟨75328226512723957565021399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50218817675149305043347599 75328226512723957565021399)
  ·
    refine ⟨112992339769085936347532099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75328226512723957565021399 112992339769085936347532099)
    ·
      refine ⟨169488509653628904521298149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112992339769085936347532099 169488509653628904521298149)
      ·
        refine ⟨31779095560055419597743403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169488509653628904521298149 31779095560055419597743403)
        ·
          refine ⟨47668643340083129396615105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31779095560055419597743403 47668643340083129396615105)
          ·
            refine ⟨35751482505062347047461329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47668643340083129396615105 35751482505062347047461329)
            ·
              refine ⟨26813611878796760285595997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35751482505062347047461329 26813611878796760285595997)
              ·
                refine ⟨10055104454548785107098499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26813611878796760285595997 10055104454548785107098499)
                ·
                  refine ⟨15082656681823177660647749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10055104454548785107098499 15082656681823177660647749)
                  ·
                    refine ⟨2827998127841845811371453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15082656681823177660647749 2827998127841845811371453)
                    ·
                      refine ⟨1060499297940692179264295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2827998127841845811371453 1060499297940692179264295)
                      ·
                        rfl

theorem cell23_2065315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_2065315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065315 prefixEnd_2065315 := by exact prefixLift 2065315
  have htrace : WordTrace (prefixWord ++ tailWord_2065315) baseStart_2065315 baseEnd_2065315 := by
    simpa [prefixWord, tailWord_2065315, baseEnd_2065315] using wordTrace_append hprefix tailTrace_2065315
  have hstable : (prefixWord ++ tailWord_2065315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065315).length < 2 ^ (prefixWord ++ tailWord_2065315).sum := by decide
  have hdescent : baseEnd_2065315 < baseStart_2065315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065335 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 6]
def baseStart_2065335 : Nat := 118140960795 + 2065335 * 2 ^ 59
def prefixEnd_2065335 : Nat := 4983230072969 + 3 ^ 40 * 2065335 * 2
def baseEnd_2065335 : Nat := 117834396394864677890467

theorem tailTrace_2065335 : CollatzResearch.WordTrace tailWord_2065335 prefixEnd_2065335 117834396394864677890467 := by
  unfold tailWord_2065335
  simp only [CollatzResearch.WordTrace]
  refine ⟨75328955972651500980749459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50219303981767667320499639 75328955972651500980749459)
  ·
    refine ⟨112993433958977251471124189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75328955972651500980749459 112993433958977251471124189)
    ·
      refine ⟨42372537734616469301671571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112993433958977251471124189 42372537734616469301671571)
      ·
        refine ⟨63558806601924703952507357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42372537734616469301671571 63558806601924703952507357)
        ·
          refine ⟨23834552475721763982190259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63558806601924703952507357 23834552475721763982190259)
          ·
            refine ⟨35751828713582645973285389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23834552475721763982190259 35751828713582645973285389)
            ·
              refine ⟨13406935767593492239982021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35751828713582645973285389 13406935767593492239982021)
              ·
                refine ⟨2513800456423779794996629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13406935767593492239982021 2513800456423779794996629)
                ·
                  refine ⟨117834396394864677890467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2513800456423779794996629 117834396394864677890467)
                  ·
                    rfl

theorem cell23_2065335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 6].length) (baseStart_2065335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065335 prefixEnd_2065335 := by exact prefixLift 2065335
  have htrace : WordTrace (prefixWord ++ tailWord_2065335) baseStart_2065335 baseEnd_2065335 := by
    simpa [prefixWord, tailWord_2065335, baseEnd_2065335] using wordTrace_append hprefix tailTrace_2065335
  have hstable : (prefixWord ++ tailWord_2065335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065335).length < 2 ^ (prefixWord ++ tailWord_2065335).sum := by decide
  have hdescent : baseEnd_2065335 < baseStart_2065335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065366 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2065366 : Nat := 118140960795 + 2065366 * 2 ^ 59
def prefixEnd_2065366 : Nat := 4983230072969 + 3 ^ 40 * 2065366 * 2
def baseEnd_2065366 : Nat := 1060525485454071479726561

theorem tailTrace_2065366 : CollatzResearch.WordTrace tailWord_2065366 prefixEnd_2065366 1060525485454071479726561 := by
  unfold tailWord_2065366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708130414721199579695497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50220057757026128850085301 4708130414721199579695497)
  ·
    refine ⟨3531097811040899684771623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4708130414721199579695497 3531097811040899684771623)
    ·
      refine ⟨5296646716561349527157435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531097811040899684771623 5296646716561349527157435)
      ·
        refine ⟨7944970074842024290736153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296646716561349527157435 7944970074842024290736153)
        ·
          refine ⟨5958727556131518218052115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7944970074842024290736153 5958727556131518218052115)
          ·
            refine ⟨8938091334197277327078173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958727556131518218052115 8938091334197277327078173)
            ·
              refine ⟨3351784250323978997654315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8938091334197277327078173 3351784250323978997654315)
              ·
                refine ⟨5027676375485968496481473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351784250323978997654315 5027676375485968496481473)
                ·
                  refine ⟨3770757281614476372361105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027676375485968496481473 3770757281614476372361105)
                  ·
                    refine ⟨2828067961210857279270829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3770757281614476372361105 2828067961210857279270829)
                    ·
                      refine ⟨1060525485454071479726561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828067961210857279270829 1060525485454071479726561)
                      ·
                        rfl

theorem cell23_2065366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2065366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065366 prefixEnd_2065366 := by exact prefixLift 2065366
  have htrace : WordTrace (prefixWord ++ tailWord_2065366) baseStart_2065366 baseEnd_2065366 := by
    simpa [prefixWord, tailWord_2065366, baseEnd_2065366] using wordTrace_append hprefix tailTrace_2065366
  have hstable : (prefixWord ++ tailWord_2065366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065366).length < 2 ^ (prefixWord ++ tailWord_2065366).sum := by decide
  have hdescent : baseEnd_2065366 < baseStart_2065366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065419 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 4]
def baseStart_2065419 : Nat := 118140960795 + 2065419 * 2 ^ 59
def prefixEnd_2065419 : Nat := 4983230072969 + 3 ^ 40 * 2065419 * 2
def baseEnd_2065419 : Nat := 1060552699928759772363817

theorem tailTrace_2065419 : CollatzResearch.WordTrace tailWord_2065419 prefixEnd_2065419 1060552699928759772363817 := by
  unfold tailWord_2065419
  simp only [CollatzResearch.WordTrace]
  refine ⟨75332019704347183326807311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50221346469564788884538207 75332019704347183326807311)
  ·
    refine ⟨112998029556520774990210967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75332019704347183326807311 112998029556520774990210967)
    ·
      refine ⟨169497044334781162485316451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112998029556520774990210967 169497044334781162485316451)
      ·
        refine ⟨254245566502171743727974677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169497044334781162485316451 254245566502171743727974677)
        ·
          refine ⟨11917760929789300487248813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 254245566502171743727974677 11917760929789300487248813)
          ·
            refine ⟨4469160348670987682718305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11917760929789300487248813 4469160348670987682718305)
            ·
              refine ⟨3351870261503240762038729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469160348670987682718305 3351870261503240762038729)
              ·
                refine ⟨2513902696127430571529047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351870261503240762038729 2513902696127430571529047)
                ·
                  refine ⟨3770854044191145857293571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513902696127430571529047 3770854044191145857293571)
                  ·
                    refine ⟨5656281066286718785940357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3770854044191145857293571 5656281066286718785940357)
                    ·
                      refine ⟨1060552699928759772363817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5656281066286718785940357 1060552699928759772363817)
                      ·
                        rfl

theorem cell23_2065419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 4].length) (baseStart_2065419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065419 prefixEnd_2065419 := by exact prefixLift 2065419
  have htrace : WordTrace (prefixWord ++ tailWord_2065419) baseStart_2065419 baseEnd_2065419 := by
    simpa [prefixWord, tailWord_2065419, baseEnd_2065419] using wordTrace_append hprefix tailTrace_2065419
  have hstable : (prefixWord ++ tailWord_2065419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065419).length < 2 ^ (prefixWord ++ tailWord_2065419).sum := by decide
  have hdescent : baseEnd_2065419 < baseStart_2065419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065439 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 3]
def baseStart_2065439 : Nat := 118140960795 + 2065439 * 2 ^ 59
def prefixEnd_2065439 : Nat := 4983230072969 + 3 ^ 40 * 2065439 * 2
def baseEnd_2065439 : Nat := 1060562969541849694113725

theorem tailTrace_2065439 : CollatzResearch.WordTrace tailWord_2065439 prefixEnd_2065439 1060562969541849694113725 := by
  unfold tailWord_2065439
  simp only [CollatzResearch.WordTrace]
  refine ⟨75332749164274726742535371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50221832776183151161690247 75332749164274726742535371)
  ·
    refine ⟨112999123746412090113803057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75332749164274726742535371 112999123746412090113803057)
    ·
      refine ⟨84749342809809067585352293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112999123746412090113803057 84749342809809067585352293)
      ·
        refine ⟨15890501776839200172253555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84749342809809067585352293 15890501776839200172253555)
        ·
          refine ⟨23835752665258800258380333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15890501776839200172253555 23835752665258800258380333)
          ·
            refine ⟨8938407249472050096892625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23835752665258800258380333 8938407249472050096892625)
            ·
              refine ⟨6703805437104037572669469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938407249472050096892625 6703805437104037572669469)
              ·
                refine ⟨2513927038914014089751051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6703805437104037572669469 2513927038914014089751051)
                ·
                  refine ⟨3770890558371021134626577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513927038914014089751051 3770890558371021134626577)
                  ·
                    refine ⟨2828167918778265850969933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3770890558371021134626577 2828167918778265850969933)
                    ·
                      refine ⟨1060562969541849694113725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828167918778265850969933 1060562969541849694113725)
                      ·
                        rfl

theorem cell23_2065439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_2065439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065439 prefixEnd_2065439 := by exact prefixLift 2065439
  have htrace : WordTrace (prefixWord ++ tailWord_2065439) baseStart_2065439 baseEnd_2065439 := by
    simpa [prefixWord, tailWord_2065439, baseEnd_2065439] using wordTrace_append hprefix tailTrace_2065439
  have hstable : (prefixWord ++ tailWord_2065439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065439).length < 2 ^ (prefixWord ++ tailWord_2065439).sum := by decide
  have hdescent : baseEnd_2065439 < baseStart_2065439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065442 : List Nat := [3, 3, 1, 1, 1, 5, 9]
def baseStart_2065442 : Nat := 118140960795 + 2065442 * 2 ^ 59
def prefixEnd_2065442 : Nat := 4983230072969 + 3 ^ 40 * 2065442 * 2
def baseEnd_2065442 : Nat := 13093389012145841757731

theorem tailTrace_2065442 : CollatzResearch.WordTrace tailWord_2065442 prefixEnd_2065442 13093389012145841757731 := by
  unfold tailWord_2065442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833214645815964563723645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50221905722175905503263053 18833214645815964563723645)
  ·
    refine ⟨7062455492180986711396367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18833214645815964563723645 7062455492180986711396367)
    ·
      refine ⟨10593683238271480067094551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7062455492180986711396367 10593683238271480067094551)
      ·
        refine ⟨15890524857407220100641827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10593683238271480067094551 15890524857407220100641827)
        ·
          refine ⟨23835787286110830150962741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15890524857407220100641827 23835787286110830150962741)
          ·
            refine ⟨2234605058072890326652757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23835787286110830150962741 2234605058072890326652757)
            ·
              refine ⟨13093389012145841757731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2234605058072890326652757 13093389012145841757731)
              ·
                rfl

theorem cell23_2065442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 9].length) (baseStart_2065442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065442 prefixEnd_2065442 := by exact prefixLift 2065442
  have htrace : WordTrace (prefixWord ++ tailWord_2065442) baseStart_2065442 baseEnd_2065442 := by
    simpa [prefixWord, tailWord_2065442, baseEnd_2065442] using wordTrace_append hprefix tailTrace_2065442
  have hstable : (prefixWord ++ tailWord_2065442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065442).length < 2 ^ (prefixWord ++ tailWord_2065442).sum := by decide
  have hdescent : baseEnd_2065442 < baseStart_2065442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065473 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2065473 : Nat := 118140960795 + 2065473 * 2 ^ 59
def prefixEnd_2065473 : Nat := 4983230072969 + 3 ^ 40 * 2065473 * 2
def baseEnd_2065473 : Nat := 1060580427884102561088569

theorem tailTrace_2065473 : CollatzResearch.WordTrace tailWord_2065473 prefixEnd_2065473 1060580427884102561088569 := by
  unfold tailWord_2065473
  simp only [CollatzResearch.WordTrace]
  refine ⟨75333989246151550549273073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50222659497434367032848715 75333989246151550549273073)
  ·
    refine ⟨56500491934613662911954805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75333989246151550549273073 56500491934613662911954805)
    ·
      refine ⟨5296921118870030897995763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56500491934613662911954805 5296921118870030897995763)
      ·
        refine ⟨7945381678305046346993645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296921118870030897995763 7945381678305046346993645)
        ·
          refine ⟨2979518129364392380122617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7945381678305046346993645 2979518129364392380122617)
          ·
            refine ⟨2234638597023294285091963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979518129364392380122617 2234638597023294285091963)
            ·
              refine ⟨3351957895534941427637945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234638597023294285091963 3351957895534941427637945)
              ·
                refine ⟨2513968421651206070728459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351957895534941427637945 2513968421651206070728459)
                ·
                  refine ⟨3770952632476809106092689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513968421651206070728459 3770952632476809106092689)
                  ·
                    refine ⟨2828214474357606829569517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3770952632476809106092689 2828214474357606829569517)
                    ·
                      refine ⟨1060580427884102561088569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828214474357606829569517 1060580427884102561088569)
                      ·
                        rfl

theorem cell23_2065473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2065473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065473 prefixEnd_2065473 := by exact prefixLift 2065473
  have htrace : WordTrace (prefixWord ++ tailWord_2065473) baseStart_2065473 baseEnd_2065473 := by
    simpa [prefixWord, tailWord_2065473, baseEnd_2065473] using wordTrace_append hprefix tailTrace_2065473
  have hstable : (prefixWord ++ tailWord_2065473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065473).length < 2 ^ (prefixWord ++ tailWord_2065473).sum := by decide
  have hdescent : baseEnd_2065473 < baseStart_2065473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065509 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 3, 4, 2]
def baseStart_2065509 : Nat := 118140960795 + 2065509 * 2 ^ 59
def prefixEnd_2065509 : Nat := 4983230072969 + 3 ^ 40 * 2065509 * 2
def baseEnd_2065509 : Nat := 1060598913187664420238403

theorem tailTrace_2065509 : CollatzResearch.WordTrace tailWord_2065509 prefixEnd_2065509 1060598913187664420238403 := by
  unfold tailWord_2065509
  simp only [CollatzResearch.WordTrace]
  refine ⟨75335302274021128697583581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50223534849347419131722387 75335302274021128697583581)
  ·
    refine ⟨28250738352757923261593843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75335302274021128697583581 28250738352757923261593843)
    ·
      refine ⟨42376107529136884892390765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28250738352757923261593843 42376107529136884892390765)
      ·
        refine ⟨15891040323426331834646537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42376107529136884892390765 15891040323426331834646537)
        ·
          refine ⟨11918280242569748875984903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15891040323426331834646537 11918280242569748875984903)
          ·
            refine ⟨17877420363854623313977355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918280242569748875984903 17877420363854623313977355)
            ·
              refine ⟨26816130545781934970966033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17877420363854623313977355 26816130545781934970966033)
              ·
                refine ⟨20112097909336451228224525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26816130545781934970966033 20112097909336451228224525)
                ·
                  refine ⟨7542036716001169210584197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20112097909336451228224525 7542036716001169210584197)
                  ·
                    refine ⟨1414131884250219226984537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542036716001169210584197 1414131884250219226984537)
                    ·
                      refine ⟨1060598913187664420238403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414131884250219226984537 1060598913187664420238403)
                      ·
                        rfl

theorem cell23_2065509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_2065509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065509 prefixEnd_2065509 := by exact prefixLift 2065509
  have htrace : WordTrace (prefixWord ++ tailWord_2065509) baseStart_2065509 baseEnd_2065509 := by
    simpa [prefixWord, tailWord_2065509, baseEnd_2065509] using wordTrace_append hprefix tailTrace_2065509
  have hstable : (prefixWord ++ tailWord_2065509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065509).length < 2 ^ (prefixWord ++ tailWord_2065509).sum := by decide
  have hdescent : baseEnd_2065509 < baseStart_2065509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065515 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 13]
def baseStart_2065515 : Nat := 118140960795 + 2065515 * 2 ^ 59
def prefixEnd_2065515 : Nat := 4983230072969 + 3 ^ 40 * 2065515 * 2
def baseEnd_2065515 : Nat := 117844666007954599640375

theorem tailTrace_2065515 : CollatzResearch.WordTrace tailWord_2065515 prefixEnd_2065515 117844666007954599640375 := by
  unfold tailWord_2065515
  simp only [CollatzResearch.WordTrace]
  refine ⟨75335521111999391722301999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50223680741332927814867999 75335521111999391722301999)
  ·
    refine ⟨113003281667999087583452999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75335521111999391722301999 113003281667999087583452999)
    ·
      refine ⟨169504922501998631375179499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113003281667999087583452999 169504922501998631375179499)
      ·
        refine ⟨254257383752997947062769249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169504922501998631375179499 254257383752997947062769249)
        ·
          refine ⟨190693037814748460297076937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254257383752997947062769249 190693037814748460297076937)
          ·
            refine ⟨143019778361061345222807703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190693037814748460297076937 143019778361061345222807703)
            ·
              refine ⟨214529667541592017834211555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143019778361061345222807703 214529667541592017834211555)
              ·
                refine ⟨321794501312388026751317333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214529667541592017834211555 321794501312388026751317333)
                ·
                  refine ⟨117844666007954599640375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 321794501312388026751317333 117844666007954599640375)
                  ·
                    rfl

theorem cell23_2065515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 13].length) (baseStart_2065515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065515 prefixEnd_2065515 := by exact prefixLift 2065515
  have htrace : WordTrace (prefixWord ++ tailWord_2065515) baseStart_2065515 baseEnd_2065515 := by
    simpa [prefixWord, tailWord_2065515, baseEnd_2065515] using wordTrace_append hprefix tailTrace_2065515
  have hstable : (prefixWord ++ tailWord_2065515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065515).length < 2 ^ (prefixWord ++ tailWord_2065515).sum := by decide
  have hdescent : baseEnd_2065515 < baseStart_2065515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065532 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 7]
def baseStart_2065532 : Nat := 118140960795 + 2065532 * 2 ^ 59
def prefixEnd_2065532 : Nat := 4983230072969 + 3 ^ 40 * 2065532 * 2
def baseEnd_2065532 : Nat := 117845635915857536694533

theorem tailTrace_2065532 : CollatzResearch.WordTrace tailWord_2065532 prefixEnd_2065532 117845635915857536694533 := by
  unfold tailWord_2065532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37668070576468901812835425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50224094101958535750447233 37668070576468901812835425)
  ·
    refine ⟨28251052932351676359626569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37668070576468901812835425 28251052932351676359626569)
    ·
      refine ⟨21188289699263757269719927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28251052932351676359626569 21188289699263757269719927)
      ·
        refine ⟨31782434548895635904579891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21188289699263757269719927 31782434548895635904579891)
        ·
          refine ⟨47673651823343453856869837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31782434548895635904579891 47673651823343453856869837)
          ·
            refine ⟨17877619433753795196326189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47673651823343453856869837 17877619433753795196326189)
            ·
              refine ⟨6704107287657673198622321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17877619433753795196326189 6704107287657673198622321)
              ·
                refine ⟨5028080465743254898966741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6704107287657673198622321 5028080465743254898966741)
                ·
                  refine ⟨117845635915857536694533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5028080465743254898966741 117845635915857536694533)
                  ·
                    rfl

theorem cell23_2065532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_2065532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065532 prefixEnd_2065532 := by exact prefixLift 2065532
  have htrace : WordTrace (prefixWord ++ tailWord_2065532) baseStart_2065532 baseEnd_2065532 := by
    simpa [prefixWord, tailWord_2065532, baseEnd_2065532] using wordTrace_append hprefix tailTrace_2065532
  have hstable : (prefixWord ++ tailWord_2065532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065532).length < 2 ^ (prefixWord ++ tailWord_2065532).sum := by decide
  have hdescent : baseEnd_2065532 < baseStart_2065532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065559 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_2065559 : Nat := 118140960795 + 2065559 * 2 ^ 59
def prefixEnd_2065559 : Nat := 4983230072969 + 3 ^ 40 * 2065559 * 2
def baseEnd_2065559 : Nat := 1060624587220389224613173

theorem tailTrace_2065559 : CollatzResearch.WordTrace tailWord_2065559 prefixEnd_2065559 1060624587220389224613173 := by
  unfold tailWord_2065559
  simp only [CollatzResearch.WordTrace]
  refine ⟨75337125923839987236903731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50224750615893324824602487 75337125923839987236903731)
  ·
    refine ⟨113005688885759980855355597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75337125923839987236903731 113005688885759980855355597)
    ·
      refine ⟨42377133332159992820758349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113005688885759980855355597 42377133332159992820758349)
      ·
        refine ⟨15891424999559997307784381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42377133332159992820758349 15891424999559997307784381)
        ·
          refine ⟨5959284374834998990419143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15891424999559997307784381 5959284374834998990419143)
          ·
            refine ⟨8938926562252498485628715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959284374834998990419143 8938926562252498485628715)
            ·
              refine ⟨13408389843378747728443073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938926562252498485628715 13408389843378747728443073)
              ·
                refine ⟨10056292382534060796332305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13408389843378747728443073 10056292382534060796332305)
                ·
                  refine ⟨7542219286900545597249229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056292382534060796332305 7542219286900545597249229)
                  ·
                    refine ⟨2828332232587704598968461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7542219286900545597249229 2828332232587704598968461)
                    ·
                      refine ⟨1060624587220389224613173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828332232587704598968461 1060624587220389224613173)
                      ·
                        rfl

theorem cell23_2065559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_2065559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065559 prefixEnd_2065559 := by exact prefixLift 2065559
  have htrace : WordTrace (prefixWord ++ tailWord_2065559) baseStart_2065559 baseEnd_2065559 := by
    simpa [prefixWord, tailWord_2065559, baseEnd_2065559] using wordTrace_append hprefix tailTrace_2065559
  have hstable : (prefixWord ++ tailWord_2065559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065559).length < 2 ^ (prefixWord ++ tailWord_2065559).sum := by decide
  have hdescent : baseEnd_2065559 < baseStart_2065559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065560 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2065560 : Nat := 118140960795 + 2065560 * 2 ^ 59
def prefixEnd_2065560 : Nat := 4983230072969 + 3 ^ 40 * 2065560 * 2
def baseEnd_2065560 : Nat := 1060625100701043720700669

theorem tailTrace_2065560 : CollatzResearch.WordTrace tailWord_2065560 prefixEnd_2065560 1060625100701043720700669 := by
  unfold tailWord_2065560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37668581198418182203845067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50224774931224242938460089 37668581198418182203845067)
  ·
    refine ⟨56502871797627273305767601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37668581198418182203845067 56502871797627273305767601)
    ·
      refine ⟨42377153848220454979325701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56502871797627273305767601 42377153848220454979325701)
      ·
        refine ⟨7945716346541335308623569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42377153848220454979325701 7945716346541335308623569)
        ·
          refine ⟨5959287259906001481467677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7945716346541335308623569 5959287259906001481467677)
          ·
            refine ⟨2234732722464750555550379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5959287259906001481467677 2234732722464750555550379)
            ·
              refine ⟨3352099083697125833325569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234732722464750555550379 3352099083697125833325569)
              ·
                refine ⟨2514074312772844374994177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352099083697125833325569 2514074312772844374994177)
                ·
                  refine ⟨1885555734579633281245633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514074312772844374994177 1885555734579633281245633)
                  ·
                    refine ⟨1414166800934724960934225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1885555734579633281245633 1414166800934724960934225)
                    ·
                      refine ⟨1060625100701043720700669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414166800934724960934225 1060625100701043720700669)
                      ·
                        rfl

theorem cell23_2065560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2065560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065560 prefixEnd_2065560 := by exact prefixLift 2065560
  have htrace : WordTrace (prefixWord ++ tailWord_2065560) baseStart_2065560 baseEnd_2065560 := by
    simpa [prefixWord, tailWord_2065560, baseEnd_2065560] using wordTrace_append hprefix tailTrace_2065560
  have hstable : (prefixWord ++ tailWord_2065560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065560).length < 2 ^ (prefixWord ++ tailWord_2065560).sum := by decide
  have hdescent : baseEnd_2065560 < baseStart_2065560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065566 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2065566 : Nat := 118140960795 + 2065566 * 2 ^ 59
def prefixEnd_2065566 : Nat := 4983230072969 + 3 ^ 40 * 2065566 * 2
def baseEnd_2065566 : Nat := 117847575731663410802849

theorem tailTrace_2065566 : CollatzResearch.WordTrace tailWord_2065566 prefixEnd_2065566 117847575731663410802849 := by
  unfold tailWord_2065566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417172654351828429051069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50224920823209751621605701 9417172654351828429051069)
  ·
    refine ⟨3531439745381935660894151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9417172654351828429051069 3531439745381935660894151)
    ·
      refine ⟨5297159618072903491341227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531439745381935660894151 5297159618072903491341227)
      ·
        refine ⟨7945739427109355237011841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297159618072903491341227 7945739427109355237011841)
        ·
          refine ⟨5959304570332016427758881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7945739427109355237011841 5959304570332016427758881)
          ·
            refine ⟨4469478427749012320819161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5959304570332016427758881 4469478427749012320819161)
            ·
              refine ⟨3352108820811759240614371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469478427749012320819161 3352108820811759240614371)
              ·
                refine ⟨5028163231217638860921557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352108820811759240614371 5028163231217638860921557)
                ·
                  refine ⟨117847575731663410802849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5028163231217638860921557 117847575731663410802849)
                  ·
                    rfl

theorem cell23_2065566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2065566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065566 prefixEnd_2065566 := by exact prefixLift 2065566
  have htrace : WordTrace (prefixWord ++ tailWord_2065566) baseStart_2065566 baseEnd_2065566 := by
    simpa [prefixWord, tailWord_2065566, baseEnd_2065566] using wordTrace_append hprefix tailTrace_2065566
  have hstable : (prefixWord ++ tailWord_2065566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065566).length < 2 ^ (prefixWord ++ tailWord_2065566).sum := by decide
  have hdescent : baseEnd_2065566 < baseStart_2065566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065599 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 6, 2]
def baseStart_2065599 : Nat := 118140960795 + 2065599 * 2 ^ 59
def prefixEnd_2065599 : Nat := 4983230072969 + 3 ^ 40 * 2065599 * 2
def baseEnd_2065599 : Nat := 1060645126446569068112989

theorem tailTrace_2065599 : CollatzResearch.WordTrace tailWord_2065599 prefixEnd_2065599 1060645126446569068112989 := by
  unfold tailWord_2065599
  simp only [CollatzResearch.WordTrace]
  refine ⟨75338584843695074068359851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50225723229130049378906567 75338584843695074068359851)
  ·
    refine ⟨113007877265542611102539777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75338584843695074068359851 113007877265542611102539777)
    ·
      refine ⟨84755907949156958326904833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113007877265542611102539777 84755907949156958326904833)
      ·
        refine ⟨63566930961867718745178625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84755907949156958326904833 63566930961867718745178625)
        ·
          refine ⟨47675198221400789058883969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63566930961867718745178625 47675198221400789058883969)
          ·
            refine ⟨35756398666050591794162977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47675198221400789058883969 35756398666050591794162977)
            ·
              refine ⟨26817298999537943845622233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35756398666050591794162977 26817298999537943845622233)
              ·
                refine ⟨20112974249653457884216675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26817298999537943845622233 20112974249653457884216675)
                ·
                  refine ⟨30169461374480186826325013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20112974249653457884216675 30169461374480186826325013)
                  ·
                    refine ⟨1414193501928758757483985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30169461374480186826325013 1414193501928758757483985)
                    ·
                      refine ⟨1060645126446569068112989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414193501928758757483985 1060645126446569068112989)
                      ·
                        rfl

theorem cell23_2065599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_2065599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065599 prefixEnd_2065599 := by exact prefixLift 2065599
  have htrace : WordTrace (prefixWord ++ tailWord_2065599) baseStart_2065599 baseEnd_2065599 := by
    simpa [prefixWord, tailWord_2065599, baseEnd_2065599] using wordTrace_append hprefix tailTrace_2065599
  have hstable : (prefixWord ++ tailWord_2065599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065599).length < 2 ^ (prefixWord ++ tailWord_2065599).sum := by decide
  have hdescent : baseEnd_2065599 < baseStart_2065599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065619 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 3]
def baseStart_2065619 : Nat := 118140960795 + 2065619 * 2 ^ 59
def prefixEnd_2065619 : Nat := 4983230072969 + 3 ^ 40 * 2065619 * 2
def baseEnd_2065619 : Nat := 1060655396059658989862897

theorem tailTrace_2065619 : CollatzResearch.WordTrace tailWord_2065619 prefixEnd_2065619 1060655396059658989862897 := by
  unfold tailWord_2065619
  simp only [CollatzResearch.WordTrace]
  refine ⟨75339314303622617484087911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50226209535748411656058607 75339314303622617484087911)
  ·
    refine ⟨113008971455433926226131867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75339314303622617484087911 113008971455433926226131867)
    ·
      refine ⟨169513457183150889339197801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113008971455433926226131867 169513457183150889339197801)
      ·
        refine ⟨127135092887363167004398351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169513457183150889339197801 127135092887363167004398351)
        ·
          refine ⟨190702639331044750506597527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127135092887363167004398351 190702639331044750506597527)
          ·
            refine ⟨286053958996567125759896291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190702639331044750506597527 286053958996567125759896291)
            ·
              refine ⟨429080938494850688639844437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286053958996567125759896291 429080938494850688639844437)
              ·
                refine ⟨5028292247986531507498177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 429080938494850688639844437 5028292247986531507498177)
                ·
                  refine ⟨3771219185989898630623633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5028292247986531507498177 3771219185989898630623633)
                  ·
                    refine ⟨2828414389492423972967725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3771219185989898630623633 2828414389492423972967725)
                    ·
                      refine ⟨1060655396059658989862897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828414389492423972967725 1060655396059658989862897)
                      ·
                        rfl

theorem cell23_2065619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_2065619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065619 prefixEnd_2065619 := by exact prefixLift 2065619
  have htrace : WordTrace (prefixWord ++ tailWord_2065619) baseStart_2065619 baseEnd_2065619 := by
    simpa [prefixWord, tailWord_2065619, baseEnd_2065619] using wordTrace_append hprefix tailTrace_2065619
  have hstable : (prefixWord ++ tailWord_2065619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065619).length < 2 ^ (prefixWord ++ tailWord_2065619).sum := by decide
  have hdescent : baseEnd_2065619 < baseStart_2065619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065699 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 1, 6]
def baseStart_2065699 : Nat := 118140960795 + 2065699 * 2 ^ 59
def prefixEnd_2065699 : Nat := 4983230072969 + 3 ^ 40 * 2065699 * 2
def baseEnd_2065699 : Nat := 353565491504006225620843

theorem tailTrace_2065699 : CollatzResearch.WordTrace tailWord_2065699 prefixEnd_2065699 353565491504006225620843 := by
  unfold tailWord_2065699
  simp only [CollatzResearch.WordTrace]
  refine ⟨75342232143332791147000151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50228154762221860764666767 75342232143332791147000151)
  ·
    refine ⟨113013348214999186720500227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75342232143332791147000151 113013348214999186720500227)
    ·
      refine ⟨169520022322498780080750341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113013348214999186720500227 169520022322498780080750341)
      ·
        refine ⟨31785004185468521265140689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169520022322498780080750341 31785004185468521265140689)
        ·
          refine ⟨23838753139101390948855517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31785004185468521265140689 23838753139101390948855517)
          ·
            refine ⟨8939532427163021605820819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23838753139101390948855517 8939532427163021605820819)
            ·
              refine ⟨13409298640744532408731229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939532427163021605820819 13409298640744532408731229)
              ·
                refine ⟨5028486990279199653274211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13409298640744532408731229 5028486990279199653274211)
                ·
                  refine ⟨7542730485418799479911317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028486990279199653274211 7542730485418799479911317)
                  ·
                    refine ⟨353565491504006225620843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7542730485418799479911317 353565491504006225620843)
                    ·
                      rfl

theorem cell23_2065699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 6].length) (baseStart_2065699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065699 prefixEnd_2065699 := by exact prefixLift 2065699
  have htrace : WordTrace (prefixWord ++ tailWord_2065699) baseStart_2065699 baseEnd_2065699 := by
    simpa [prefixWord, tailWord_2065699, baseEnd_2065699] using wordTrace_append hprefix tailTrace_2065699
  have hstable : (prefixWord ++ tailWord_2065699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065699).length < 2 ^ (prefixWord ++ tailWord_2065699).sum := by decide
  have hdescent : baseEnd_2065699 < baseStart_2065699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065716 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2065716 : Nat := 118140960795 + 2065716 * 2 ^ 59
def prefixEnd_2065716 : Nat := 4983230072969 + 3 ^ 40 * 2065716 * 2
def baseEnd_2065716 : Nat := 353568401227715036783317

theorem tailTrace_2065716 : CollatzResearch.WordTrace tailWord_2065716 prefixEnd_2065716 353568401227715036783317 := by
  unfold tailWord_2065716
  simp only [CollatzResearch.WordTrace]
  refine ⟨37671426092135601525184501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50228568122847468700246001 37671426092135601525184501)
  ·
    refine ⟨3531696196137712642986047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37671426092135601525184501 3531696196137712642986047)
    ·
      refine ⟨5297544294206568964479071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531696196137712642986047 5297544294206568964479071)
      ·
        refine ⟨7946316441309853446718607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297544294206568964479071 7946316441309853446718607)
        ·
          refine ⟨11919474661964780170077911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7946316441309853446718607 11919474661964780170077911)
          ·
            refine ⟨17879211992947170255116867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919474661964780170077911 17879211992947170255116867)
            ·
              refine ⟨26818817989420755382675301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879211992947170255116867 26818817989420755382675301)
              ·
                refine ⟨5028528373016391634251619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26818817989420755382675301 5028528373016391634251619)
                ·
                  refine ⟨7542792559524587451377429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028528373016391634251619 7542792559524587451377429)
                  ·
                    refine ⟨353568401227715036783317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7542792559524587451377429 353568401227715036783317)
                    ·
                      rfl

theorem cell23_2065716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2065716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065716 prefixEnd_2065716 := by exact prefixLift 2065716
  have htrace : WordTrace (prefixWord ++ tailWord_2065716) baseStart_2065716 baseEnd_2065716 := by
    simpa [prefixWord, tailWord_2065716, baseEnd_2065716] using wordTrace_append hprefix tailTrace_2065716
  have hstable : (prefixWord ++ tailWord_2065716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065716).length < 2 ^ (prefixWord ++ tailWord_2065716).sum := by decide
  have hdescent : baseEnd_2065716 < baseStart_2065716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065726 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2065726 : Nat := 118140960795 + 2065726 * 2 ^ 59
def prefixEnd_2065726 : Nat := 4983230072969 + 3 ^ 40 * 2065726 * 2
def baseEnd_2065726 : Nat := 1060710338489690071224905

theorem tailTrace_2065726 : CollatzResearch.WordTrace tailWord_2065726 prefixEnd_2065726 1060710338489690071224905 := by
  unfold tailWord_2065726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417902114279371844779129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50228811276156649838822021 9417902114279371844779129)
  ·
    refine ⟨7063426585709528883584347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9417902114279371844779129 7063426585709528883584347)
    ·
      refine ⟨10595139878564293325376521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7063426585709528883584347 10595139878564293325376521)
      ·
        refine ⟨7946354908923219994032391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10595139878564293325376521 7946354908923219994032391)
        ·
          refine ⟨11919532363384829991048587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7946354908923219994032391 11919532363384829991048587)
          ·
            refine ⟨17879298545077244986572881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11919532363384829991048587 17879298545077244986572881)
            ·
              refine ⟨13409473908807933739929661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17879298545077244986572881 13409473908807933739929661)
              ·
                refine ⟨5028552715802975152473623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13409473908807933739929661 5028552715802975152473623)
                ·
                  refine ⟨7542829073704462728710435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028552715802975152473623 7542829073704462728710435)
                  ·
                    refine ⟨11314243610556694093065653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7542829073704462728710435 11314243610556694093065653)
                    ·
                      refine ⟨1060710338489690071224905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11314243610556694093065653 1060710338489690071224905)
                      ·
                        rfl

theorem cell23_2065726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2065726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065726 prefixEnd_2065726 := by exact prefixLift 2065726
  have htrace : WordTrace (prefixWord ++ tailWord_2065726) baseStart_2065726 baseEnd_2065726 := by
    simpa [prefixWord, tailWord_2065726, baseEnd_2065726] using wordTrace_append hprefix tailTrace_2065726
  have hstable : (prefixWord ++ tailWord_2065726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065726).length < 2 ^ (prefixWord ++ tailWord_2065726).sum := by decide
  have hdescent : baseEnd_2065726 < baseStart_2065726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065734 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2065734 : Nat := 118140960795 + 2065734 * 2 ^ 59
def prefixEnd_2065734 : Nat := 4983230072969 + 3 ^ 40 * 2065734 * 2
def baseEnd_2065734 : Nat := 1060714446334926039924869

theorem tailTrace_2065734 : CollatzResearch.WordTrace tailWord_2065734 prefixEnd_2065734 1060714446334926039924869 := by
  unfold tailWord_2065734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354484646818937253891383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50229005798803994749682837 2354484646818937253891383)
  ·
    refine ⟨3531726970228405880837075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2354484646818937253891383 3531726970228405880837075)
    ·
      refine ⟨5297590455342608821255613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531726970228405880837075 5297590455342608821255613)
      ·
        refine ⟨1986596420753478307970855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5297590455342608821255613 1986596420753478307970855)
        ·
          refine ⟨2979894631130217461956283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986596420753478307970855 2979894631130217461956283)
          ·
            refine ⟨4469841946695326192934425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979894631130217461956283 4469841946695326192934425)
            ·
              refine ⟨3352381460021494644700819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469841946695326192934425 3352381460021494644700819)
              ·
                refine ⟨5028572190032241967051229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352381460021494644700819 5028572190032241967051229)
                ·
                  refine ⟨1885714571262090737644211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5028572190032241967051229 1885714571262090737644211)
                  ·
                    refine ⟨2828571856893136106466317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1885714571262090737644211 2828571856893136106466317)
                    ·
                      refine ⟨1060714446334926039924869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828571856893136106466317 1060714446334926039924869)
                      ·
                        rfl

theorem cell23_2065734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2065734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065734 prefixEnd_2065734 := by exact prefixLift 2065734
  have htrace : WordTrace (prefixWord ++ tailWord_2065734) baseStart_2065734 baseEnd_2065734 := by
    simpa [prefixWord, tailWord_2065734, baseEnd_2065734] using wordTrace_append hprefix tailTrace_2065734
  have hstable : (prefixWord ++ tailWord_2065734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065734).length < 2 ^ (prefixWord ++ tailWord_2065734).sum := by decide
  have hdescent : baseEnd_2065734 < baseStart_2065734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065740 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2065740 : Nat := 118140960795 + 2065740 * 2 ^ 59
def prefixEnd_2065740 : Nat := 4983230072969 + 3 ^ 40 * 2065740 * 2
def baseEnd_2065740 : Nat := 1060717527218853016449841

theorem tailTrace_2065740 : CollatzResearch.WordTrace tailWord_2065740 prefixEnd_2065740 1060717527218853016449841 := by
  unfold tailWord_2065740
  simp only [CollatzResearch.WordTrace]
  refine ⟨37671863768092127574621337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50229151690789503432828449 37671863768092127574621337)
  ·
    refine ⟨28253897826069095680966003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37671863768092127574621337 28253897826069095680966003)
    ·
      refine ⟨42380846739103643521449005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28253897826069095680966003 42380846739103643521449005)
      ·
        refine ⟨15892817527163866320543377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42380846739103643521449005 15892817527163866320543377)
        ·
          refine ⟨11919613145372899740407533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15892817527163866320543377 11919613145372899740407533)
          ·
            refine ⟨4469854929514837402652825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11919613145372899740407533 4469854929514837402652825)
            ·
              refine ⟨3352391197136128051989619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469854929514837402652825 3352391197136128051989619)
              ·
                refine ⟨5028586795704192077984429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352391197136128051989619 5028586795704192077984429)
                ·
                  refine ⟨1885720048389072029244161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5028586795704192077984429 1885720048389072029244161)
                  ·
                    refine ⟨1414290036291804021933121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1885720048389072029244161 1414290036291804021933121)
                    ·
                      refine ⟨1060717527218853016449841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414290036291804021933121 1060717527218853016449841)
                      ·
                        rfl

theorem cell23_2065740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2065740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065740 prefixEnd_2065740 := by exact prefixLift 2065740
  have htrace : WordTrace (prefixWord ++ tailWord_2065740) baseStart_2065740 baseEnd_2065740 := by
    simpa [prefixWord, tailWord_2065740, baseEnd_2065740] using wordTrace_append hprefix tailTrace_2065740
  have hstable : (prefixWord ++ tailWord_2065740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065740).length < 2 ^ (prefixWord ++ tailWord_2065740).sum := by decide
  have hdescent : baseEnd_2065740 < baseStart_2065740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065773 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2065773 : Nat := 118140960795 + 2065773 * 2 ^ 59
def prefixEnd_2065773 : Nat := 4983230072969 + 3 ^ 40 * 2065773 * 2
def baseEnd_2065773 : Nat := 1060734472080451387337189

theorem tailTrace_2065773 : CollatzResearch.WordTrace tailWord_2065773 prefixEnd_2065773 1060734472080451387337189 := by
  unfold tailWord_2065773
  simp only [CollatzResearch.WordTrace]
  refine ⟨75344931145064701785193973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50229954096709801190129315 75344931145064701785193973)
  ·
    refine ⟨7063587294849815792361935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75344931145064701785193973 7063587294849815792361935)
    ·
      refine ⟨10595380942274723688542903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7063587294849815792361935 10595380942274723688542903)
      ·
        refine ⟨15893071413412085532814355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10595380942274723688542903 15893071413412085532814355)
        ·
          refine ⟨23839607120118128299221533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15893071413412085532814355 23839607120118128299221533)
          ·
            refine ⟨8939852670044298112208075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23839607120118128299221533 8939852670044298112208075)
            ·
              refine ⟨13409779005066447168312113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939852670044298112208075 13409779005066447168312113)
              ·
                refine ⟨10057334253799835376234085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13409779005066447168312113 10057334253799835376234085)
                ·
                  refine ⟨1885750172587469133043891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10057334253799835376234085 1885750172587469133043891)
                  ·
                    refine ⟨2828625258881203699565837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1885750172587469133043891 2828625258881203699565837)
                    ·
                      refine ⟨1060734472080451387337189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828625258881203699565837 1060734472080451387337189)
                      ·
                        rfl

theorem cell23_2065773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2065773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065773 prefixEnd_2065773 := by exact prefixLift 2065773
  have htrace : WordTrace (prefixWord ++ tailWord_2065773) baseStart_2065773 baseEnd_2065773 := by
    simpa [prefixWord, tailWord_2065773, baseEnd_2065773] using wordTrace_append hprefix tailTrace_2065773
  have hstable : (prefixWord ++ tailWord_2065773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065773).length < 2 ^ (prefixWord ++ tailWord_2065773).sum := by decide
  have hdescent : baseEnd_2065773 < baseStart_2065773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065783 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 1, 3, 2]
def baseStart_2065783 : Nat := 118140960795 + 2065783 * 2 ^ 59
def prefixEnd_2065783 : Nat := 4983230072969 + 3 ^ 40 * 2065783 * 2
def baseEnd_2065783 : Nat := 1060739606886996348212143

theorem tailTrace_2065783 : CollatzResearch.WordTrace tailWord_2065783 prefixEnd_2065783 1060739606886996348212143 := by
  unfold tailWord_2065783
  simp only [CollatzResearch.WordTrace]
  refine ⟨75345295875028473493058003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50230197250018982328705335 75345295875028473493058003)
  ·
    refine ⟨113017943812542710239587005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75345295875028473493058003 113017943812542710239587005)
    ·
      refine ⟨42381728929703516339845127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113017943812542710239587005 42381728929703516339845127)
      ·
        refine ⟨63572593394555274509767691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42381728929703516339845127 63572593394555274509767691)
        ·
          refine ⟨95358890091832911764651537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63572593394555274509767691 95358890091832911764651537)
          ·
            refine ⟨71519167568874683823488653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95358890091832911764651537 71519167568874683823488653)
            ·
              refine ⟨26819687838328006433808245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71519167568874683823488653 26819687838328006433808245)
              ·
                refine ⟨2514345734843250603169523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26819687838328006433808245 2514345734843250603169523)
                ·
                  refine ⟨3771518602264875904754285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514345734843250603169523 3771518602264875904754285)
                  ·
                    refine ⟨1414319475849328464282857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3771518602264875904754285 1414319475849328464282857)
                    ·
                      refine ⟨1060739606886996348212143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414319475849328464282857 1060739606886996348212143)
                      ·
                        rfl

theorem cell23_2065783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_2065783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065783 prefixEnd_2065783 := by exact prefixLift 2065783
  have htrace : WordTrace (prefixWord ++ tailWord_2065783) baseStart_2065783 baseEnd_2065783 := by
    simpa [prefixWord, tailWord_2065783, baseEnd_2065783] using wordTrace_append hprefix tailTrace_2065783
  have hstable : (prefixWord ++ tailWord_2065783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065783).length < 2 ^ (prefixWord ++ tailWord_2065783).sum := by decide
  have hdescent : baseEnd_2065783 < baseStart_2065783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065829 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_2065829 : Nat := 118140960795 + 2065829 * 2 ^ 59
def prefixEnd_2065829 : Nat := 4983230072969 + 3 ^ 40 * 2065829 * 2
def baseEnd_2065829 : Nat := 1060763226997103168236931

theorem tailTrace_2065829 : CollatzResearch.WordTrace tailWord_2065829 prefixEnd_2065829 1060763226997103168236931 := by
  unfold tailWord_2065829
  simp only [CollatzResearch.WordTrace]
  refine ⟨75346973632861823349232541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50231315755241215566155027 75346973632861823349232541)
  ·
    refine ⟨28255115112323183755962203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75346973632861823349232541 28255115112323183755962203)
    ·
      refine ⟨42382672668484775633943305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28255115112323183755962203 42382672668484775633943305)
      ·
        refine ⟨31787004501363581725457479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42382672668484775633943305 31787004501363581725457479)
        ·
          refine ⟨47680506752045372588186219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31787004501363581725457479 47680506752045372588186219)
          ·
            refine ⟨71520760128068058882279329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47680506752045372588186219 71520760128068058882279329)
            ·
              refine ⟨53640570096051044161709497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71520760128068058882279329 53640570096051044161709497)
              ·
                refine ⟨40230427572038283121282123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53640570096051044161709497 40230427572038283121282123)
                ·
                  refine ⟨60345641358057424681923185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40230427572038283121282123 60345641358057424681923185)
                  ·
                    refine ⟨45259231018543068511442389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60345641358057424681923185 45259231018543068511442389)
                    ·
                      refine ⟨1060763226997103168236931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45259231018543068511442389 1060763226997103168236931)
                      ·
                        rfl

theorem cell23_2065829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_2065829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065829 prefixEnd_2065829 := by exact prefixLift 2065829
  have htrace : WordTrace (prefixWord ++ tailWord_2065829) baseStart_2065829 baseEnd_2065829 := by
    simpa [prefixWord, tailWord_2065829, baseEnd_2065829] using wordTrace_append hprefix tailTrace_2065829
  have hstable : (prefixWord ++ tailWord_2065829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065829).length < 2 ^ (prefixWord ++ tailWord_2065829).sum := by decide
  have hdescent : baseEnd_2065829 < baseStart_2065829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065853 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 5]
def baseStart_2065853 : Nat := 118140960795 + 2065853 * 2 ^ 59
def prefixEnd_2065853 : Nat := 4983230072969 + 3 ^ 40 * 2065853 * 2
def baseEnd_2065853 : Nat := 117863950059201230481869

theorem tailTrace_2065853 : CollatzResearch.WordTrace tailWord_2065853 prefixEnd_2065853 117863950059201230481869 := by
  unfold tailWord_2065853
  simp only [CollatzResearch.WordTrace]
  refine ⟨75347848984774875448106213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50231899323183250298737475 75347848984774875448106213)
  ·
    refine ⟨14127721684645289146519915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75347848984774875448106213 14127721684645289146519915)
    ·
      refine ⟨21191582526967933719779873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14127721684645289146519915 21191582526967933719779873)
      ·
        refine ⟨15893686895225950289834905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21191582526967933719779873 15893686895225950289834905)
        ·
          refine ⟨11920265171419462717376179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15893686895225950289834905 11920265171419462717376179)
          ·
            refine ⟨17880397757129194076064269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920265171419462717376179 17880397757129194076064269)
            ·
              refine ⟨6705149158923447778524101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17880397757129194076064269 6705149158923447778524101)
              ·
                refine ⟨1257215467298146458473269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6705149158923447778524101 1257215467298146458473269)
                ·
                  refine ⟨117863950059201230481869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1257215467298146458473269 117863950059201230481869)
                  ·
                    rfl

theorem cell23_2065853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_2065853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065853 prefixEnd_2065853 := by exact prefixLift 2065853
  have htrace : WordTrace (prefixWord ++ tailWord_2065853) baseStart_2065853 baseEnd_2065853 := by
    simpa [prefixWord, tailWord_2065853, baseEnd_2065853] using wordTrace_append hprefix tailTrace_2065853
  have hstable : (prefixWord ++ tailWord_2065853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065853).length < 2 ^ (prefixWord ++ tailWord_2065853).sum := by decide
  have hdescent : baseEnd_2065853 < baseStart_2065853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065903 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 2, 4, 2]
def baseStart_2065903 : Nat := 118140960795 + 2065903 * 2 ^ 59
def prefixEnd_2065903 : Nat := 4983230072969 + 3 ^ 40 * 2065903 * 2
def baseEnd_2065903 : Nat := 1060801224565535878711591

theorem tailTrace_2065903 : CollatzResearch.WordTrace tailWord_2065903 prefixEnd_2065903 1060801224565535878711591 := by
  unfold tailWord_2065903
  simp only [CollatzResearch.WordTrace]
  refine ⟨75349672634593733987426363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50233115089729155991617575 75349672634593733987426363)
  ·
    refine ⟨113024508951890600981139545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75349672634593733987426363 113024508951890600981139545)
    ·
      refine ⟨84768381713917950735854659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113024508951890600981139545 84768381713917950735854659)
      ·
        refine ⟨127152572570876926103781989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84768381713917950735854659 127152572570876926103781989)
        ·
          refine ⟨23841107357039423644459123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127152572570876926103781989 23841107357039423644459123)
          ·
            refine ⟨35761661035559135466688685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23841107357039423644459123 35761661035559135466688685)
            ·
              refine ⟨13410622888334675800008257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35761661035559135466688685 13410622888334675800008257)
              ·
                refine ⟨10057967166251006850006193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13410622888334675800008257 10057967166251006850006193)
                ·
                  refine ⟨7543475374688255137504645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10057967166251006850006193 7543475374688255137504645)
                  ·
                    refine ⟨1414401632754047838282121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543475374688255137504645 1414401632754047838282121)
                    ·
                      refine ⟨1060801224565535878711591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414401632754047838282121 1060801224565535878711591)
                      ·
                        rfl

theorem cell23_2065903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 4, 2].length) (baseStart_2065903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065903 prefixEnd_2065903 := by exact prefixLift 2065903
  have htrace : WordTrace (prefixWord ++ tailWord_2065903) baseStart_2065903 baseEnd_2065903 := by
    simpa [prefixWord, tailWord_2065903, baseEnd_2065903] using wordTrace_append hprefix tailTrace_2065903
  have hstable : (prefixWord ++ tailWord_2065903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065903).length < 2 ^ (prefixWord ++ tailWord_2065903).sum := by decide
  have hdescent : baseEnd_2065903 < baseStart_2065903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065993 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 6, 2]
def baseStart_2065993 : Nat := 118140960795 + 2065993 * 2 ^ 59
def prefixEnd_2065993 : Nat := 4983230072969 + 3 ^ 40 * 2065993 * 2
def baseEnd_2065993 : Nat := 1060847437824440526586177

theorem tailTrace_2065993 : CollatzResearch.WordTrace tailWord_2065993 prefixEnd_2065993 1060847437824440526586177 := by
  unfold tailWord_2065993
  simp only [CollatzResearch.WordTrace]
  refine ⟨75352955204267679358202633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50235303469511786238801755 75352955204267679358202633)
  ·
    refine ⟨56514716403200759518651975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75352955204267679358202633 56514716403200759518651975)
    ·
      refine ⟨84772074604801139277977963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56514716403200759518651975 84772074604801139277977963)
      ·
        refine ⟨127158111907201708916966945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84772074604801139277977963 127158111907201708916966945)
        ·
          refine ⟨95368583930401281687725209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127158111907201708916966945 95368583930401281687725209)
          ·
            refine ⟨71526437947800961265793907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95368583930401281687725209 71526437947800961265793907)
            ·
              refine ⟨107289656921701441898690861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71526437947800961265793907 107289656921701441898690861)
              ·
                refine ⟨40233621345638040712009073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107289656921701441898690861 40233621345638040712009073)
                ·
                  refine ⟨30175216009228530534006805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40233621345638040712009073 30175216009228530534006805)
                  ·
                    refine ⟨1414463250432587368781569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30175216009228530534006805 1414463250432587368781569)
                    ·
                      refine ⟨1060847437824440526586177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414463250432587368781569 1060847437824440526586177)
                      ·
                        rfl

theorem cell23_2065993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 6, 2].length) (baseStart_2065993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2065993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2065993 prefixEnd_2065993 := by exact prefixLift 2065993
  have htrace : WordTrace (prefixWord ++ tailWord_2065993) baseStart_2065993 baseEnd_2065993 := by
    simpa [prefixWord, tailWord_2065993, baseEnd_2065993] using wordTrace_append hprefix tailTrace_2065993
  have hstable : (prefixWord ++ tailWord_2065993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065993).length < 2 ^ (prefixWord ++ tailWord_2065993).sum := by decide
  have hdescent : baseEnd_2065993 < baseStart_2065993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066020 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_2066020 : Nat := 118140960795 + 2066020 * 2 ^ 59
def prefixEnd_2066020 : Nat := 4983230072969 + 3 ^ 40 * 2066020 * 2
def baseEnd_2066020 : Nat := 353620433934037306982851

theorem tailTrace_2066020 : CollatzResearch.WordTrace tailWord_2066020 prefixEnd_2066020 353620433934037306982851 := by
  unfold tailWord_2066020
  simp only [CollatzResearch.WordTrace]
  refine ⟨37676969987584931484717757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50235959983446575312957009 37676969987584931484717757)
  ·
    refine ⟨14128863745344349306769159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37676969987584931484717757 14128863745344349306769159)
    ·
      refine ⟨21193295618016523960153739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14128863745344349306769159 21193295618016523960153739)
      ·
        refine ⟨31789943427024785940230609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21193295618016523960153739 31789943427024785940230609)
        ·
          refine ⟨23842457570268589455172957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31789943427024785940230609 23842457570268589455172957)
          ·
            refine ⟨8940921588850721045689859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23842457570268589455172957 8940921588850721045689859)
            ·
              refine ⟨13411382383276081568534789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940921588850721045689859 13411382383276081568534789)
              ·
                refine ⟨2514634196864265294100273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13411382383276081568534789 2514634196864265294100273)
                ·
                  refine ⟨1885975647648198970575205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514634196864265294100273 1885975647648198970575205)
                  ·
                    refine ⟨353620433934037306982851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885975647648198970575205 353620433934037306982851)
                    ·
                      rfl

theorem cell23_2066020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_2066020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066020 prefixEnd_2066020 := by exact prefixLift 2066020
  have htrace : WordTrace (prefixWord ++ tailWord_2066020) baseStart_2066020 baseEnd_2066020 := by
    simpa [prefixWord, tailWord_2066020, baseEnd_2066020] using wordTrace_append hprefix tailTrace_2066020
  have hstable : (prefixWord ++ tailWord_2066020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066020).length < 2 ^ (prefixWord ++ tailWord_2066020).sum := by decide
  have hdescent : baseEnd_2066020 < baseStart_2066020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066021 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 1, 1, 3]
def baseStart_2066021 : Nat := 118140960795 + 2066021 * 2 ^ 59
def prefixEnd_2066021 : Nat := 4983230072969 + 3 ^ 40 * 2066021 * 2
def baseEnd_2066021 : Nat := 1060861815282766417036049

theorem tailTrace_2066021 : CollatzResearch.WordTrace tailWord_2066021 prefixEnd_2066021 1060861815282766417036049 := by
  unfold tailWord_2066021
  simp only [CollatzResearch.WordTrace]
  refine ⟨75353976448166240140221917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50235984298777493426814611 75353976448166240140221917)
  ·
    refine ⟨28257741168062340052583219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75353976448166240140221917 28257741168062340052583219)
    ·
      refine ⟨42386611752093510078874829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28257741168062340052583219 42386611752093510078874829)
      ·
        refine ⟨15894979407035066279578061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42386611752093510078874829 15894979407035066279578061)
        ·
          refine ⟨5960617277638149854841773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15894979407035066279578061 5960617277638149854841773)
          ·
            refine ⟨2235231479114306195565665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5960617277638149854841773 2235231479114306195565665)
            ·
              refine ⟨1676423609335729646674249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235231479114306195565665 1676423609335729646674249)
              ·
                refine ⟨1257317707001797235005687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676423609335729646674249 1257317707001797235005687)
                ·
                  refine ⟨1885976560502695852508531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257317707001797235005687 1885976560502695852508531)
                  ·
                    refine ⟨2828964840754043778762797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1885976560502695852508531 2828964840754043778762797)
                    ·
                      refine ⟨1060861815282766417036049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2828964840754043778762797 1060861815282766417036049)
                      ·
                        rfl

theorem cell23_2066021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_2066021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066021 prefixEnd_2066021 := by exact prefixLift 2066021
  have htrace : WordTrace (prefixWord ++ tailWord_2066021) baseStart_2066021 baseEnd_2066021 := by
    simpa [prefixWord, tailWord_2066021, baseEnd_2066021] using wordTrace_append hprefix tailTrace_2066021
  have hstable : (prefixWord ++ tailWord_2066021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066021).length < 2 ^ (prefixWord ++ tailWord_2066021).sum := by decide
  have hdescent : baseEnd_2066021 < baseStart_2066021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066037 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2066037 : Nat := 118140960795 + 2066037 * 2 ^ 59
def prefixEnd_2066037 : Nat := 4983230072969 + 3 ^ 40 * 2066037 * 2
def baseEnd_2066037 : Nat := 353623343657746118145325

theorem tailTrace_2066037 : CollatzResearch.WordTrace tailWord_2066037 prefixEnd_2066037 353623343657746118145325 := by
  unfold tailWord_2066037
  simp only [CollatzResearch.WordTrace]
  refine ⟨75354560016108274872804365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50236373344072183248536243 75354560016108274872804365)
  ·
    refine ⟨28257960006040603077301637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75354560016108274872804365 28257960006040603077301637)
    ·
      refine ⟨5298367501132613076994057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28257960006040603077301637 5298367501132613076994057)
      ·
        refine ⟨3973775625849459807745543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5298367501132613076994057 3973775625849459807745543)
        ·
          refine ⟨5960663438774189711618315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973775625849459807745543 5960663438774189711618315)
          ·
            refine ⟨8940995158161284567427473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960663438774189711618315 8940995158161284567427473)
            ·
              refine ⟨6705746368620963425570605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8940995158161284567427473 6705746368620963425570605)
              ·
                refine ⟨2514654888232861284588977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6705746368620963425570605 2514654888232861284588977)
                ·
                  refine ⟨1885991166174645963441733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514654888232861284588977 1885991166174645963441733)
                  ·
                    refine ⟨353623343657746118145325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1885991166174645963441733 353623343657746118145325)
                    ·
                      rfl

theorem cell23_2066037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2066037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066037 prefixEnd_2066037 := by exact prefixLift 2066037
  have htrace : WordTrace (prefixWord ++ tailWord_2066037) baseStart_2066037 baseEnd_2066037 := by
    simpa [prefixWord, tailWord_2066037, baseEnd_2066037] using wordTrace_append hprefix tailTrace_2066037
  have hstable : (prefixWord ++ tailWord_2066037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066037).length < 2 ^ (prefixWord ++ tailWord_2066037).sum := by decide
  have hdescent : baseEnd_2066037 < baseStart_2066037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066060 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_2066060 : Nat := 118140960795 + 2066060 * 2 ^ 59
def prefixEnd_2066060 : Nat := 4983230072969 + 3 ^ 40 * 2066060 * 2
def baseEnd_2066060 : Nat := 1060881841028291764448369

theorem tailTrace_2066060 : CollatzResearch.WordTrace tailWord_2066060 prefixEnd_2066060 1060881841028291764448369 := by
  unfold tailWord_2066060
  simp only [CollatzResearch.WordTrace]
  refine ⟨37677699447512474900445817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50236932596683299867261089 37677699447512474900445817)
  ·
    refine ⟨28258274585634356175334363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37677699447512474900445817 28258274585634356175334363)
    ·
      refine ⟨42387411878451534263001545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28258274585634356175334363 42387411878451534263001545)
      ·
        refine ⟨31790558908838650697251159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42387411878451534263001545 31790558908838650697251159)
        ·
          refine ⟨47685838363257976045876739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31790558908838650697251159 47685838363257976045876739)
          ·
            refine ⟨71528757544886964068815109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47685838363257976045876739 71528757544886964068815109)
            ·
              refine ⟨13411642039666305762902833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71528757544886964068815109 13411642039666305762902833)
              ·
                refine ⟨10058731529749729322177125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13411642039666305762902833 10058731529749729322177125)
                ·
                  refine ⟨1886012161828074247908211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10058731529749729322177125 1886012161828074247908211)
                  ·
                    refine ⟨2829018242742111371862317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1886012161828074247908211 2829018242742111371862317)
                    ·
                      refine ⟨1060881841028291764448369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2829018242742111371862317 1060881841028291764448369)
                      ·
                        rfl

theorem cell23_2066060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_2066060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066060 prefixEnd_2066060 := by exact prefixLift 2066060
  have htrace : WordTrace (prefixWord ++ tailWord_2066060) baseStart_2066060 baseEnd_2066060 := by
    simpa [prefixWord, tailWord_2066060, baseEnd_2066060] using wordTrace_append hprefix tailTrace_2066060
  have hstable : (prefixWord ++ tailWord_2066060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066060).length < 2 ^ (prefixWord ++ tailWord_2066060).sum := by decide
  have hdescent : baseEnd_2066060 < baseStart_2066060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066088 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2066088 : Nat := 118140960795 + 2066088 * 2 ^ 59
def prefixEnd_2066088 : Nat := 4983230072969 + 3 ^ 40 * 2066088 * 2
def baseEnd_2066088 : Nat := 353632072828872551632747

theorem tailTrace_2066088 : CollatzResearch.WordTrace tailWord_2066088 prefixEnd_2066088 353632072828872551632747 := by
  unfold tailWord_2066088
  simp only [CollatzResearch.WordTrace]
  refine ⟨37678210069461755291455459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50237613425949007055273945 37678210069461755291455459)
  ·
    refine ⟨56517315104192632937183189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37678210069461755291455459 56517315104192632937183189)
    ·
      refine ⟨1324624572754514834465231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56517315104192632937183189 1324624572754514834465231)
      ·
        refine ⟨1986936859131772251697847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324624572754514834465231 1986936859131772251697847)
        ·
          refine ⟨2980405288697658377546771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986936859131772251697847 2980405288697658377546771)
          ·
            refine ⟨4470607933046487566320157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980405288697658377546771 4470607933046487566320157)
            ·
              refine ⟨1676477974892432837370059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4470607933046487566320157 1676477974892432837370059)
              ·
                refine ⟨2514716962338649256055089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676477974892432837370059 2514716962338649256055089)
                ·
                  refine ⟨1886037721753986942041317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514716962338649256055089 1886037721753986942041317)
                  ·
                    refine ⟨353632072828872551632747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886037721753986942041317 353632072828872551632747)
                    ·
                      rfl

theorem cell23_2066088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2066088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066088 prefixEnd_2066088 := by exact prefixLift 2066088
  have htrace : WordTrace (prefixWord ++ tailWord_2066088) baseStart_2066088 baseEnd_2066088 := by
    simpa [prefixWord, tailWord_2066088, baseEnd_2066088] using wordTrace_append hprefix tailTrace_2066088
  have hstable : (prefixWord ++ tailWord_2066088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066088).length < 2 ^ (prefixWord ++ tailWord_2066088).sum := by decide
  have hdescent : baseEnd_2066088 < baseStart_2066088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066153 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_2066153 : Nat := 118140960795 + 2066153 * 2 ^ 59
def prefixEnd_2066153 : Nat := 4983230072969 + 3 ^ 40 * 2066153 * 2
def baseEnd_2066153 : Nat := 353643198243053300195147

theorem tailTrace_2066153 : CollatzResearch.WordTrace tailWord_2066153 prefixEnd_2066153 353643198243053300195147 := by
  unfold tailWord_2066153
  simp only [CollatzResearch.WordTrace]
  refine ⟨75358790883688026684027113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50239193922458684456018075 75358790883688026684027113)
  ·
    refine ⟨56519093162766020013020335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75358790883688026684027113 56519093162766020013020335)
    ·
      refine ⟨84778639744149030019530503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56519093162766020013020335 84778639744149030019530503)
      ·
        refine ⟨127167959616223545029295755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84778639744149030019530503 127167959616223545029295755)
        ·
          refine ⟨190751939424335317543943633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127167959616223545029295755 190751939424335317543943633)
          ·
            refine ⟨143063954568251488157957725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190751939424335317543943633 143063954568251488157957725)
            ·
              refine ⟨53648982963094308059234147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143063954568251488157957725 53648982963094308059234147)
              ·
                refine ⟨80473474444641462088851221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53648982963094308059234147 80473474444641462088851221)
                ·
                  refine ⟨3772194114592568535414901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80473474444641462088851221 3772194114592568535414901)
                  ·
                    refine ⟨353643198243053300195147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3772194114592568535414901 353643198243053300195147)
                    ·
                      rfl

theorem cell23_2066153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_2066153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066153 prefixEnd_2066153 := by exact prefixLift 2066153
  have htrace : WordTrace (prefixWord ++ tailWord_2066153) baseStart_2066153 baseEnd_2066153 := by
    simpa [prefixWord, tailWord_2066153, baseEnd_2066153] using wordTrace_append hprefix tailTrace_2066153
  have hstable : (prefixWord ++ tailWord_2066153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066153).length < 2 ^ (prefixWord ++ tailWord_2066153).sum := by decide
  have hdescent : baseEnd_2066153 < baseStart_2066153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066160 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 4, 5, 2]
def baseStart_2066160 : Nat := 118140960795 + 2066160 * 2 ^ 59
def prefixEnd_2066160 : Nat := 4983230072969 + 3 ^ 40 * 2066160 * 2
def baseEnd_2066160 : Nat := 1060933189093741373197909

theorem tailTrace_2066160 : CollatzResearch.WordTrace tailWord_2066160 prefixEnd_2066160 1060933189093741373197909 := by
  unfold tailWord_2066160
  simp only [CollatzResearch.WordTrace]
  refine ⟨37679523097331333439765967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50239364129775111253021289 37679523097331333439765967)
  ·
    refine ⟨56519284645997000159648951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37679523097331333439765967 56519284645997000159648951)
    ·
      refine ⟨84778926968995500239473427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56519284645997000159648951 84778926968995500239473427)
      ·
        refine ⟨127168390453493250359210141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84778926968995500239473427 127168390453493250359210141)
        ·
          refine ⟨47688146420059968884703803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127168390453493250359210141 47688146420059968884703803)
          ·
            refine ⟨71532219630089953327055705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47688146420059968884703803 71532219630089953327055705)
            ·
              refine ⟨53649164722567464995291779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71532219630089953327055705 53649164722567464995291779)
              ·
                refine ⟨80473747083851197492937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53649164722567464995291779 80473747083851197492937669)
                ·
                  refine ⟨15088827578222099529925813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80473747083851197492937669 15088827578222099529925813)
                  ·
                    refine ⟨1414577585458321830930545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15088827578222099529925813 1414577585458321830930545)
                    ·
                      refine ⟨1060933189093741373197909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414577585458321830930545 1060933189093741373197909)
                      ·
                        rfl

theorem cell23_2066160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 5, 2].length) (baseStart_2066160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066160 prefixEnd_2066160 := by exact prefixLift 2066160
  have htrace : WordTrace (prefixWord ++ tailWord_2066160) baseStart_2066160 baseEnd_2066160 := by
    simpa [prefixWord, tailWord_2066160, baseEnd_2066160] using wordTrace_append hprefix tailTrace_2066160
  have hstable : (prefixWord ++ tailWord_2066160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066160).length < 2 ^ (prefixWord ++ tailWord_2066160).sum := by decide
  have hdescent : baseEnd_2066160 < baseStart_2066160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066180 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2066180 : Nat := 118140960795 + 2066180 * 2 ^ 59
def prefixEnd_2066180 : Nat := 4983230072969 + 3 ^ 40 * 2066180 * 2
def baseEnd_2066180 : Nat := 1060943458706831294947817

theorem tailTrace_2066180 : CollatzResearch.WordTrace tailWord_2066180 prefixEnd_2066180 1060943458706831294947817 := by
  unfold tailWord_2066180
  simp only [CollatzResearch.WordTrace]
  refine ⟨37679887827295105147629997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50239850436393473530173329 37679887827295105147629997)
  ·
    refine ⟨14129957935235664430361249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37679887827295105147629997 14129957935235664430361249)
    ·
      refine ⟨10597468451426748322770937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14129957935235664430361249 10597468451426748322770937)
      ·
        refine ⟨7948101338570061242078203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10597468451426748322770937 7948101338570061242078203)
        ·
          refine ⟨11922152007855091863117305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7948101338570061242078203 11922152007855091863117305)
          ·
            refine ⟨8941614005891318897337979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11922152007855091863117305 8941614005891318897337979)
            ·
              refine ⟨13412421008836978346006969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941614005891318897337979 13412421008836978346006969)
              ·
                refine ⟨10059315756627733759505227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13412421008836978346006969 10059315756627733759505227)
                ·
                  refine ⟨15088973634941600639257841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10059315756627733759505227 15088973634941600639257841)
                  ·
                    refine ⟨11316730226206200479443381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15088973634941600639257841 11316730226206200479443381)
                    ·
                      refine ⟨1060943458706831294947817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11316730226206200479443381 1060943458706831294947817)
                      ·
                        rfl

theorem cell23_2066180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2066180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066180 prefixEnd_2066180 := by exact prefixLift 2066180
  have htrace : WordTrace (prefixWord ++ tailWord_2066180) baseStart_2066180 baseEnd_2066180 := by
    simpa [prefixWord, tailWord_2066180, baseEnd_2066180] using wordTrace_append hprefix tailTrace_2066180
  have hstable : (prefixWord ++ tailWord_2066180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066180).length < 2 ^ (prefixWord ++ tailWord_2066180).sum := by decide
  have hdescent : baseEnd_2066180 < baseStart_2066180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066193 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_2066193 : Nat := 118140960795 + 2066193 * 2 ^ 59
def prefixEnd_2066193 : Nat := 4983230072969 + 3 ^ 40 * 2066193 * 2
def baseEnd_2066193 : Nat := 1060950133955339744085257

theorem tailTrace_2066193 : CollatzResearch.WordTrace tailWord_2066193 prefixEnd_2066193 1060950133955339744085257 := by
  unfold tailWord_2066193
  simp only [CollatzResearch.WordTrace]
  refine ⟨75360249803543113515483233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50240166535695409010322155 75360249803543113515483233)
  ·
    refine ⟨56520187352657335136612425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75360249803543113515483233 56520187352657335136612425)
    ·
      refine ⟨42390140514493001352459319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56520187352657335136612425 42390140514493001352459319)
      ·
        refine ⟨63585210771739502028688979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42390140514493001352459319 63585210771739502028688979)
        ·
          refine ⟨95377816157609253043033469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63585210771739502028688979 95377816157609253043033469)
          ·
            refine ⟨35766681059103469891137551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95377816157609253043033469 35766681059103469891137551)
            ·
              refine ⟨53650021588655204836706327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35766681059103469891137551 53650021588655204836706327)
              ·
                refine ⟨80475032382982807255059491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53650021588655204836706327 80475032382982807255059491)
                ·
                  refine ⟨120712548574474210882589237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80475032382982807255059491 120712548574474210882589237)
                  ·
                    refine ⟨11316801428856957270242741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120712548574474210882589237 11316801428856957270242741)
                    ·
                      refine ⟨1060950133955339744085257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11316801428856957270242741 1060950133955339744085257)
                      ·
                        rfl

theorem cell23_2066193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_2066193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066193 prefixEnd_2066193 := by exact prefixLift 2066193
  have htrace : WordTrace (prefixWord ++ tailWord_2066193) baseStart_2066193 baseEnd_2066193 := by
    simpa [prefixWord, tailWord_2066193, baseEnd_2066193] using wordTrace_append hprefix tailTrace_2066193
  have hstable : (prefixWord ++ tailWord_2066193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066193).length < 2 ^ (prefixWord ++ tailWord_2066193).sum := by decide
  have hdescent : baseEnd_2066193 < baseStart_2066193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066194 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2066194 : Nat := 118140960795 + 2066194 * 2 ^ 59
def prefixEnd_2066194 : Nat := 4983230072969 + 3 ^ 40 * 2066194 * 2
def baseEnd_2066194 : Nat := 1060950647435994240172753

theorem tailTrace_2066194 : CollatzResearch.WordTrace tailWord_2066194 prefixEnd_2066194 1060950647435994240172753 := by
  unfold tailWord_2066194
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840071569134872671567409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50240190851026327124179757 18840071569134872671567409)
  ·
    refine ⟨14130053676851154503675557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18840071569134872671567409 14130053676851154503675557)
    ·
      refine ⟨2649385064409591469439167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14130053676851154503675557 2649385064409591469439167)
      ·
        refine ⟨3974077596614387204158751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649385064409591469439167 3974077596614387204158751)
        ·
          refine ⟨5961116394921580806238127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974077596614387204158751 5961116394921580806238127)
          ·
            refine ⟨8941674592382371209357191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961116394921580806238127 8941674592382371209357191)
            ·
              refine ⟨13412511888573556814035787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941674592382371209357191 13412511888573556814035787)
              ·
                refine ⟨20118767832860335221053681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13412511888573556814035787 20118767832860335221053681)
                ·
                  refine ⟨15089075874645251415790261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20118767832860335221053681 15089075874645251415790261)
                  ·
                    refine ⟨1414600863247992320230337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15089075874645251415790261 1414600863247992320230337)
                    ·
                      refine ⟨1060950647435994240172753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414600863247992320230337 1060950647435994240172753)
                      ·
                        rfl

theorem cell23_2066194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2066194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066194 prefixEnd_2066194 := by exact prefixLift 2066194
  have htrace : WordTrace (prefixWord ++ tailWord_2066194) baseStart_2066194 baseEnd_2066194 := by
    simpa [prefixWord, tailWord_2066194, baseEnd_2066194] using wordTrace_append hprefix tailTrace_2066194
  have hstable : (prefixWord ++ tailWord_2066194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066194).length < 2 ^ (prefixWord ++ tailWord_2066194).sum := by decide
  have hdescent : baseEnd_2066194 < baseStart_2066194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066203 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_2066203 : Nat := 118140960795 + 2066203 * 2 ^ 59
def prefixEnd_2066203 : Nat := 4983230072969 + 3 ^ 40 * 2066203 * 2
def baseEnd_2066203 : Nat := 1060955268761884704960211

theorem tailTrace_2066203 : CollatzResearch.WordTrace tailWord_2066203 prefixEnd_2066203 1060955268761884704960211 := by
  unfold tailWord_2066203
  simp only [CollatzResearch.WordTrace]
  refine ⟨75360614533506885223347263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50240409689004590148898175 75360614533506885223347263)
  ·
    refine ⟨113040921800260327835020895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75360614533506885223347263 113040921800260327835020895)
    ·
      refine ⟨169561382700390491752531343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113040921800260327835020895 169561382700390491752531343)
      ·
        refine ⟨254342074050585737628797015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169561382700390491752531343 254342074050585737628797015)
        ·
          refine ⟨381513111075878606443195523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254342074050585737628797015 381513111075878606443195523)
          ·
            refine ⟨572269666613817909664793285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381513111075878606443195523 572269666613817909664793285)
            ·
              refine ⟨107300562490090858062148741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 572269666613817909664793285 107300562490090858062148741)
              ·
                refine ⟨20118855466892035886652889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107300562490090858062148741 20118855466892035886652889)
                ·
                  refine ⟨15089141600169026914989667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20118855466892035886652889 15089141600169026914989667)
                  ·
                    refine ⟨22633712400253540372484501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15089141600169026914989667 22633712400253540372484501)
                    ·
                      refine ⟨1060955268761884704960211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22633712400253540372484501 1060955268761884704960211)
                      ·
                        rfl

theorem cell23_2066203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_2066203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066203 prefixEnd_2066203 := by exact prefixLift 2066203
  have htrace : WordTrace (prefixWord ++ tailWord_2066203) baseStart_2066203 baseEnd_2066203 := by
    simpa [prefixWord, tailWord_2066203, baseEnd_2066203] using wordTrace_append hprefix tailTrace_2066203
  have hstable : (prefixWord ++ tailWord_2066203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066203).length < 2 ^ (prefixWord ++ tailWord_2066203).sum := by decide
  have hdescent : baseEnd_2066203 < baseStart_2066203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066207 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 2, 4, 2]
def baseStart_2066207 : Nat := 118140960795 + 2066207 * 2 ^ 59
def prefixEnd_2066207 : Nat := 4983230072969 + 3 ^ 40 * 2066207 * 2
def baseEnd_2066207 : Nat := 1060957322684502689310193

theorem tailTrace_2066207 : CollatzResearch.WordTrace tailWord_2066207 prefixEnd_2066207 1060957322684502689310193 := by
  unfold tailWord_2066207
  simp only [CollatzResearch.WordTrace]
  refine ⟨75360760425492393906492875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50240506950328262604328583 75360760425492393906492875)
  ·
    refine ⟨113041140638238590859739313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75360760425492393906492875 113041140638238590859739313)
    ·
      refine ⟨84780855478678943144804485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113041140638238590859739313 84780855478678943144804485)
      ·
        refine ⟨15896410402252301839650841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84780855478678943144804485 15896410402252301839650841)
        ·
          refine ⟨11922307801689226379738131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15896410402252301839650841 11922307801689226379738131)
          ·
            refine ⟨17883461702533839569607197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11922307801689226379738131 17883461702533839569607197)
            ·
              refine ⟨6706298138450189838602699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17883461702533839569607197 6706298138450189838602699)
              ·
                refine ⟨10059447207675284757904049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706298138450189838602699 10059447207675284757904049)
                ·
                  refine ⟨7544585405756463568428037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10059447207675284757904049 7544585405756463568428037)
                  ·
                    refine ⟨1414609763579336919080257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7544585405756463568428037 1414609763579336919080257)
                    ·
                      refine ⟨1060957322684502689310193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414609763579336919080257 1060957322684502689310193)
                      ·
                        rfl

theorem cell23_2066207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_2066207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066207 prefixEnd_2066207 := by exact prefixLift 2066207
  have htrace : WordTrace (prefixWord ++ tailWord_2066207) baseStart_2066207 baseEnd_2066207 := by
    simpa [prefixWord, tailWord_2066207, baseEnd_2066207] using wordTrace_append hprefix tailTrace_2066207
  have hstable : (prefixWord ++ tailWord_2066207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066207).length < 2 ^ (prefixWord ++ tailWord_2066207).sum := by decide
  have hdescent : baseEnd_2066207 < baseStart_2066207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066227 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 3]
def baseStart_2066227 : Nat := 118140960795 + 2066227 * 2 ^ 59
def prefixEnd_2066227 : Nat := 4983230072969 + 3 ^ 40 * 2066227 * 2
def baseEnd_2066227 : Nat := 1060967592297592611060101

theorem tailTrace_2066227 : CollatzResearch.WordTrace tailWord_2066227 prefixEnd_2066227 1060967592297592611060101 := by
  unfold tailWord_2066227
  simp only [CollatzResearch.WordTrace]
  refine ⟨75361489885419937322220935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50240993256946624881480623 75361489885419937322220935)
  ·
    refine ⟨113042234828129905983331403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75361489885419937322220935 113042234828129905983331403)
    ·
      refine ⟨169563352242194858974997105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113042234828129905983331403 169563352242194858974997105)
      ·
        refine ⟨127172514181646144231247829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169563352242194858974997105 127172514181646144231247829)
        ·
          refine ⟨2980605801132331505419871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127172514181646144231247829 2980605801132331505419871)
          ·
            refine ⟨4470908701698497258129807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980605801132331505419871 4470908701698497258129807)
            ·
              refine ⟨6706363052547745887194711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470908701698497258129807 6706363052547745887194711)
              ·
                refine ⟨10059544578821618830792067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706363052547745887194711 10059544578821618830792067)
                ·
                  refine ⟨15089316868232428246188101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10059544578821618830792067 15089316868232428246188101)
                  ·
                    refine ⟨2829246912793580296160269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15089316868232428246188101 2829246912793580296160269)
                    ·
                      refine ⟨1060967592297592611060101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2829246912793580296160269 1060967592297592611060101)
                      ·
                        rfl

theorem cell23_2066227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_2066227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066227 prefixEnd_2066227 := by exact prefixLift 2066227
  have htrace : WordTrace (prefixWord ++ tailWord_2066227) baseStart_2066227 baseEnd_2066227 := by
    simpa [prefixWord, tailWord_2066227, baseEnd_2066227] using wordTrace_append hprefix tailTrace_2066227
  have hstable : (prefixWord ++ tailWord_2066227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066227).length < 2 ^ (prefixWord ++ tailWord_2066227).sum := by decide
  have hdescent : baseEnd_2066227 < baseStart_2066227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066234 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_2066234 : Nat := 118140960795 + 2066234 * 2 ^ 59
def prefixEnd_2066234 : Nat := 4983230072969 + 3 ^ 40 * 2066234 * 2
def baseEnd_2066234 : Nat := 353657062220724694557523

theorem tailTrace_2066234 : CollatzResearch.WordTrace tailWord_2066234 prefixEnd_2066234 353657062220724694557523 := by
  unfold tailWord_2066234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840436299098644379431439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50241163464263051678483837 18840436299098644379431439)
  ·
    refine ⟨28260654448647966569147159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18840436299098644379431439 28260654448647966569147159)
    ·
      refine ⟨42390981672971949853720739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28260654448647966569147159 42390981672971949853720739)
      ·
        refine ⟨63586472509457924780581109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42390981672971949853720739 63586472509457924780581109)
        ·
          refine ⟨5961231797761680448179479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63586472509457924780581109 5961231797761680448179479)
          ·
            refine ⟨8941847696642520672269219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961231797761680448179479 8941847696642520672269219)
            ·
              refine ⟨13412771544963781008403829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8941847696642520672269219 13412771544963781008403829)
              ·
                refine ⟨1257447332340354469537859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13412771544963781008403829 1257447332340354469537859)
                ·
                  refine ⟨1886170998510531704306789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257447332340354469537859 1886170998510531704306789)
                  ·
                    refine ⟨353657062220724694557523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886170998510531704306789 353657062220724694557523)
                    ·
                      rfl

theorem cell23_2066234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_2066234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066234 prefixEnd_2066234 := by exact prefixLift 2066234
  have htrace : WordTrace (prefixWord ++ tailWord_2066234) baseStart_2066234 baseEnd_2066234 := by
    simpa [prefixWord, tailWord_2066234, baseEnd_2066234] using wordTrace_append hprefix tailTrace_2066234
  have hstable : (prefixWord ++ tailWord_2066234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066234).length < 2 ^ (prefixWord ++ tailWord_2066234).sum := by decide
  have hdescent : baseEnd_2066234 < baseStart_2066234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066290 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_2066290 : Nat := 118140960795 + 2066290 * 2 ^ 59
def prefixEnd_2066290 : Nat := 4983230072969 + 3 ^ 40 * 2066290 * 2
def baseEnd_2066290 : Nat := 353666647192941954857437

theorem tailTrace_2066290 : CollatzResearch.WordTrace tailWord_2066290 prefixEnd_2066290 353666647192941954857437 := by
  unfold tailWord_2066290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840946921047924770441081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50242525122794466054509549 18840946921047924770441081)
  ·
    refine ⟨14130710190785943577830811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18840946921047924770441081 14130710190785943577830811)
    ·
      refine ⟨21196065286178915366746217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14130710190785943577830811 21196065286178915366746217)
      ·
        refine ⟨15897048964634186525059663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21196065286178915366746217 15897048964634186525059663)
        ·
          refine ⟨23845573446951279787589495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15897048964634186525059663 23845573446951279787589495)
          ·
            refine ⟨35768360170426919681384243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23845573446951279787589495 35768360170426919681384243)
            ·
              refine ⟨53652540255640379522076365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35768360170426919681384243 53652540255640379522076365)
              ·
                refine ⟨20119702595865142320778637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53652540255640379522076365 20119702595865142320778637)
                ·
                  refine ⟨7544888473449428370291989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20119702595865142320778637 7544888473449428370291989)
                  ·
                    refine ⟨353666647192941954857437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7544888473449428370291989 353666647192941954857437)
                    ·
                      rfl

theorem cell23_2066290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_2066290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066290 prefixEnd_2066290 := by exact prefixLift 2066290
  have htrace : WordTrace (prefixWord ++ tailWord_2066290) baseStart_2066290 baseEnd_2066290 := by
    simpa [prefixWord, tailWord_2066290, baseEnd_2066290] using wordTrace_append hprefix tailTrace_2066290
  have hstable : (prefixWord ++ tailWord_2066290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066290).length < 2 ^ (prefixWord ++ tailWord_2066290).sum := by decide
  have hdescent : baseEnd_2066290 < baseStart_2066290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066297 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 4]
def baseStart_2066297 : Nat := 118140960795 + 2066297 * 2 ^ 59
def prefixEnd_2066297 : Nat := 4983230072969 + 3 ^ 40 * 2066297 * 2
def baseEnd_2066297 : Nat := 1061003535943407337184779

theorem tailTrace_2066297 : CollatzResearch.WordTrace tailWord_2066297 prefixEnd_2066297 1061003535943407337184779 := by
  unfold tailWord_2066297
  simp only [CollatzResearch.WordTrace]
  refine ⟨75364042995166339277269145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50242695330110892851512763 75364042995166339277269145)
  ·
    refine ⟨56523032246374754457951859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75364042995166339277269145 56523032246374754457951859)
    ·
      refine ⟨84784548369562131686927789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56523032246374754457951859 84784548369562131686927789)
      ·
        refine ⟨31794205638585799382597921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84784548369562131686927789 31794205638585799382597921)
        ·
          refine ⟨23845654228939349536948441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31794205638585799382597921 23845654228939349536948441)
          ·
            refine ⟨17884240671704512152711331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23845654228939349536948441 17884240671704512152711331)
            ·
              refine ⟨26826361007556768229066997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17884240671704512152711331 26826361007556768229066997)
              ·
                refine ⟨2514971344458447021475031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26826361007556768229066997 2514971344458447021475031)
                ·
                  refine ⟨3772457016687670532212547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514971344458447021475031 3772457016687670532212547)
                  ·
                    refine ⟨5658685525031505798318821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3772457016687670532212547 5658685525031505798318821)
                    ·
                      refine ⟨1061003535943407337184779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5658685525031505798318821 1061003535943407337184779)
                      ·
                        rfl

theorem cell23_2066297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_2066297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066297 prefixEnd_2066297 := by exact prefixLift 2066297
  have htrace : WordTrace (prefixWord ++ tailWord_2066297) baseStart_2066297 baseEnd_2066297 := by
    simpa [prefixWord, tailWord_2066297, baseEnd_2066297] using wordTrace_append hprefix tailTrace_2066297
  have hstable : (prefixWord ++ tailWord_2066297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066297).length < 2 ^ (prefixWord ++ tailWord_2066297).sum := by decide
  have hdescent : baseEnd_2066297 < baseStart_2066297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066307 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 4, 4]
def baseStart_2066307 : Nat := 118140960795 + 2066307 * 2 ^ 59
def prefixEnd_2066307 : Nat := 4983230072969 + 3 ^ 40 * 2066307 * 2
def baseEnd_2066307 : Nat := 353669556916650766019911

theorem tailTrace_2066307 : CollatzResearch.WordTrace tailWord_2066307 prefixEnd_2066307 353669556916650766019911 := by
  unfold tailWord_2066307
  simp only [CollatzResearch.WordTrace]
  refine ⟨75364407725130110985133175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50242938483420073990088783 75364407725130110985133175)
  ·
    refine ⟨113046611587695166477699763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75364407725130110985133175 113046611587695166477699763)
    ·
      refine ⟨169569917381542749716549645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113046611587695166477699763 169569917381542749716549645)
      ·
        refine ⟨63588719018078531143706117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169569917381542749716549645 63588719018078531143706117)
        ·
          refine ⟨11922884815889724589444897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63588719018078531143706117 11922884815889724589444897)
          ·
            refine ⟨8942163611917293442083673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11922884815889724589444897 8942163611917293442083673)
            ·
              refine ⟨6706622708937970081562755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8942163611917293442083673 6706622708937970081562755)
              ·
                refine ⟨10059934063406955122344133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706622708937970081562755 10059934063406955122344133)
                ·
                  refine ⟨1886237636888804085439525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10059934063406955122344133 1886237636888804085439525)
                  ·
                    refine ⟨353669556916650766019911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886237636888804085439525 353669556916650766019911)
                    ·
                      rfl

theorem cell23_2066307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 4].length) (baseStart_2066307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066307 prefixEnd_2066307 := by exact prefixLift 2066307
  have htrace : WordTrace (prefixWord ++ tailWord_2066307) baseStart_2066307 baseEnd_2066307 := by
    simpa [prefixWord, tailWord_2066307, baseEnd_2066307] using wordTrace_append hprefix tailTrace_2066307
  have hstable : (prefixWord ++ tailWord_2066307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066307).length < 2 ^ (prefixWord ++ tailWord_2066307).sum := by decide
  have hdescent : baseEnd_2066307 < baseStart_2066307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066328 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 1, 5]
def baseStart_2066328 : Nat := 118140960795 + 2066328 * 2 ^ 59
def prefixEnd_2066328 : Nat := 4983230072969 + 3 ^ 40 * 2066328 * 2
def baseEnd_2066328 : Nat := 353673151281232238632379

theorem tailTrace_2066328 : CollatzResearch.WordTrace tailWord_2066328 prefixEnd_2066328 353673151281232238632379 := by
  unfold tailWord_2066328
  simp only [CollatzResearch.WordTrace]
  refine ⟨37682586829027015785823819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50243449105369354381098425 37682586829027015785823819)
  ·
    refine ⟨56523880243540523678735729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37682586829027015785823819 56523880243540523678735729)
    ·
      refine ⟨42392910182655392759051797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56523880243540523678735729 42392910182655392759051797)
      ·
        refine ⟨1987167664811971535580553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42392910182655392759051797 1987167664811971535580553)
        ·
          refine ⟨1490375748608978651685415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1987167664811971535580553 1490375748608978651685415)
          ·
            refine ⟨2235563622913467977528123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490375748608978651685415 2235563622913467977528123)
            ·
              refine ⟨3353345434370201966292185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235563622913467977528123 3353345434370201966292185)
              ·
                refine ⟨2515009075777651474719139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353345434370201966292185 2515009075777651474719139)
                ·
                  refine ⟨3772513613666477212078709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515009075777651474719139 3772513613666477212078709)
                  ·
                    refine ⟨353673151281232238632379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3772513613666477212078709 353673151281232238632379)
                    ·
                      rfl

theorem cell23_2066328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_2066328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066328 prefixEnd_2066328 := by exact prefixLift 2066328
  have htrace : WordTrace (prefixWord ++ tailWord_2066328) baseStart_2066328 baseEnd_2066328 := by
    simpa [prefixWord, tailWord_2066328, baseEnd_2066328] using wordTrace_append hprefix tailTrace_2066328
  have hstable : (prefixWord ++ tailWord_2066328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066328).length < 2 ^ (prefixWord ++ tailWord_2066328).sum := by decide
  have hdescent : baseEnd_2066328 < baseStart_2066328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066365 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_2066365 : Nat := 118140960795 + 2066365 * 2 ^ 59
def prefixEnd_2066365 : Nat := 4983230072969 + 3 ^ 40 * 2066365 * 2
def baseEnd_2066365 : Nat := 1061038452627913071134467

theorem tailTrace_2066365 : CollatzResearch.WordTrace tailWord_2066365 prefixEnd_2066365 1061038452627913071134467 := by
  unfold tailWord_2066365
  simp only [CollatzResearch.WordTrace]
  refine ⟨75366523158919986890744549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50244348772613324593829699 75366523158919986890744549)
  ·
    refine ⟨14131223092297497542014603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75366523158919986890744549 14131223092297497542014603)
    ·
      refine ⟨21196834638446246313021905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131223092297497542014603 21196834638446246313021905)
      ·
        refine ⟨15897625978834684734766429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21196834638446246313021905 15897625978834684734766429)
        ·
          refine ⟨5961609742063006775537411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15897625978834684734766429 5961609742063006775537411)
          ·
            refine ⟨8942414613094510163306117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961609742063006775537411 8942414613094510163306117)
            ·
              refine ⟨1676702739955220655619897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8942414613094510163306117 1676702739955220655619897)
              ·
                refine ⟨1257527054966415491714923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676702739955220655619897 1257527054966415491714923)
                ·
                  refine ⟨1886290582449623237572385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257527054966415491714923 1886290582449623237572385)
                  ·
                    refine ⟨1414717936837217428179289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1886290582449623237572385 1414717936837217428179289)
                    ·
                      refine ⟨1061038452627913071134467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414717936837217428179289 1061038452627913071134467)
                      ·
                        rfl

theorem cell23_2066365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_2066365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066365 prefixEnd_2066365 := by exact prefixLift 2066365
  have htrace : WordTrace (prefixWord ++ tailWord_2066365) baseStart_2066365 baseEnd_2066365 := by
    simpa [prefixWord, tailWord_2066365, baseEnd_2066365] using wordTrace_append hprefix tailTrace_2066365
  have hstable : (prefixWord ++ tailWord_2066365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066365).length < 2 ^ (prefixWord ++ tailWord_2066365).sum := by decide
  have hdescent : baseEnd_2066365 < baseStart_2066365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066402 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2066402 : Nat := 118140960795 + 2066402 * 2 ^ 59
def prefixEnd_2066402 : Nat := 4983230072969 + 3 ^ 40 * 2066402 * 2
def baseEnd_2066402 : Nat := 1061057451412129426371797

theorem tailTrace_2066402 : CollatzResearch.WordTrace tailWord_2066402 prefixEnd_2066402 1061057451412129426371797 := by
  unfold tailWord_2066402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18841968164946485552460365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50245248439857294806560973 18841968164946485552460365)
  ·
    refine ⟨7065738061854932082172637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18841968164946485552460365 7065738061854932082172637)
    ·
      refine ⟨2649651773195599530814739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7065738061854932082172637 2649651773195599530814739)
      ·
        refine ⟨3974477659793399296222109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649651773195599530814739 3974477659793399296222109)
        ·
          refine ⟨1490429122422524736083291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3974477659793399296222109 1490429122422524736083291)
          ·
            refine ⟨2235643683633787104124937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490429122422524736083291 2235643683633787104124937)
            ·
              refine ⟨1676732762725340328093703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235643683633787104124937 1676732762725340328093703)
              ·
                refine ⟨2515099144088010492140555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676732762725340328093703 2515099144088010492140555)
                ·
                  refine ⟨3772648716132015738210833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515099144088010492140555 3772648716132015738210833)
                  ·
                    refine ⟨2829486537099011803658125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3772648716132015738210833 2829486537099011803658125)
                    ·
                      refine ⟨1061057451412129426371797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2829486537099011803658125 1061057451412129426371797)
                      ·
                        rfl

theorem cell23_2066402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2066402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066402 prefixEnd_2066402 := by exact prefixLift 2066402
  have htrace : WordTrace (prefixWord ++ tailWord_2066402) baseStart_2066402 baseEnd_2066402 := by
    simpa [prefixWord, tailWord_2066402, baseEnd_2066402] using wordTrace_append hprefix tailTrace_2066402
  have hstable : (prefixWord ++ tailWord_2066402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066402).length < 2 ^ (prefixWord ++ tailWord_2066402).sum := by decide
  have hdescent : baseEnd_2066402 < baseStart_2066402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066404 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_2066404 : Nat := 118140960795 + 2066404 * 2 ^ 59
def prefixEnd_2066404 : Nat := 4983230072969 + 3 ^ 40 * 2066404 * 2
def baseEnd_2066404 : Nat := 1061058478373438418546787

theorem tailTrace_2066404 : CollatzResearch.WordTrace tailWord_2066404 prefixEnd_2066404 1061058478373438418546787 := by
  unfold tailWord_2066404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683972802889348275707133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50245297070519131034276177 37683972802889348275707133)
  ·
    refine ⟨14131489801083505603390175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37683972802889348275707133 14131489801083505603390175)
    ·
      refine ⟨21197234701625258405085263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131489801083505603390175 21197234701625258405085263)
      ·
        refine ⟨31795852052437887607627895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21197234701625258405085263 31795852052437887607627895)
        ·
          refine ⟨47693778078656831411441843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31795852052437887607627895 47693778078656831411441843)
          ·
            refine ⟨71540667117985247117162765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47693778078656831411441843 71540667117985247117162765)
            ·
              refine ⟨26827750169244467668936037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71540667117985247117162765 26827750169244467668936037)
              ·
                refine ⟨5030203156733337687925507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26827750169244467668936037 5030203156733337687925507)
                ·
                  refine ⟨7545304735100006531888261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030203156733337687925507 7545304735100006531888261)
                  ·
                    refine ⟨1414744637831251224729049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7545304735100006531888261 1414744637831251224729049)
                    ·
                      refine ⟨1061058478373438418546787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414744637831251224729049 1061058478373438418546787)
                      ·
                        rfl

theorem cell23_2066404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_2066404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066404 prefixEnd_2066404 := by exact prefixLift 2066404
  have htrace : WordTrace (prefixWord ++ tailWord_2066404) baseStart_2066404 baseEnd_2066404 := by
    simpa [prefixWord, tailWord_2066404, baseEnd_2066404] using wordTrace_append hprefix tailTrace_2066404
  have hstable : (prefixWord ++ tailWord_2066404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066404).length < 2 ^ (prefixWord ++ tailWord_2066404).sum := by decide
  have hdescent : baseEnd_2066404 < baseStart_2066404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066457 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_2066457 : Nat := 118140960795 + 2066457 * 2 ^ 59
def prefixEnd_2066457 : Nat := 4983230072969 + 3 ^ 40 * 2066457 * 2
def baseEnd_2066457 : Nat := 353695230949375570394681

theorem tailTrace_2066457 : CollatzResearch.WordTrace tailWord_2066457 prefixEnd_2066457 353695230949375570394681 := by
  unfold tailWord_2066457
  simp only [CollatzResearch.WordTrace]
  refine ⟨75369878674586686603093625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50246585783057791068729083 75369878674586686603093625)
  ·
    refine ⟨56527409005940014952320219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75369878674586686603093625 56527409005940014952320219)
    ·
      refine ⟨84791113508910022428480329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56527409005940014952320219 84791113508910022428480329)
      ·
        refine ⟨63593335131682516821360247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84791113508910022428480329 63593335131682516821360247)
        ·
          refine ⟨95390002697523775232040371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63593335131682516821360247 95390002697523775232040371)
          ·
            refine ⟨143085004046285662848060557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95390002697523775232040371 143085004046285662848060557)
            ·
              refine ⟨53656876517357123568022709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143085004046285662848060557 53656876517357123568022709)
              ·
                refine ⟨5030332173502230334502129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53656876517357123568022709 5030332173502230334502129)
                ·
                  refine ⟨3772749130126672750876597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030332173502230334502129 3772749130126672750876597)
                  ·
                    refine ⟨353695230949375570394681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3772749130126672750876597 353695230949375570394681)
                    ·
                      rfl

theorem cell23_2066457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_2066457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066457 prefixEnd_2066457 := by exact prefixLift 2066457
  have htrace : WordTrace (prefixWord ++ tailWord_2066457) baseStart_2066457 baseEnd_2066457 := by
    simpa [prefixWord, tailWord_2066457, baseEnd_2066457] using wordTrace_append hprefix tailTrace_2066457
  have hstable : (prefixWord ++ tailWord_2066457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066457).length < 2 ^ (prefixWord ++ tailWord_2066457).sum := by decide
  have hdescent : baseEnd_2066457 < baseStart_2066457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066461 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 5]
def baseStart_2066461 : Nat := 118140960795 + 2066461 * 2 ^ 59
def prefixEnd_2066461 : Nat := 4983230072969 + 3 ^ 40 * 2066461 * 2
def baseEnd_2066461 : Nat := 117898638530082743948225

theorem tailTrace_2066461 : CollatzResearch.WordTrace tailWord_2066461 prefixEnd_2066461 117898638530082743948225 := by
  unfold tailWord_2066461
  simp only [CollatzResearch.WordTrace]
  refine ⟨75370024566572195286239237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50246683044381463524159491 75370024566572195286239237)
  ·
    refine ⟨14131879606232286616169857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75370024566572195286239237 14131879606232286616169857)
    ·
      refine ⟨10598909704674214962127393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14131879606232286616169857 10598909704674214962127393)
      ·
        refine ⟨7949182278505661221595545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10598909704674214962127393 7949182278505661221595545)
        ·
          refine ⟨5961886708879245916196659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949182278505661221595545 5961886708879245916196659)
          ·
            refine ⟨8942830063318868874294989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961886708879245916196659 8942830063318868874294989)
            ·
              refine ⟨3353561273744575827860621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8942830063318868874294989 3353561273744575827860621)
              ·
                refine ⟨1257585477654215935447733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3353561273744575827860621 1257585477654215935447733)
                ·
                  refine ⟨117898638530082743948225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1257585477654215935447733 117898638530082743948225)
                  ·
                    rfl

theorem cell23_2066461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_2066461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066461 prefixEnd_2066461 := by exact prefixLift 2066461
  have htrace : WordTrace (prefixWord ++ tailWord_2066461) baseStart_2066461 baseEnd_2066461 := by
    simpa [prefixWord, tailWord_2066461, baseEnd_2066461] using wordTrace_append hprefix tailTrace_2066461
  have hstable : (prefixWord ++ tailWord_2066461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066461).length < 2 ^ (prefixWord ++ tailWord_2066461).sum := by decide
  have hdescent : baseEnd_2066461 < baseStart_2066461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066467 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5]
def baseStart_2066467 : Nat := 118140960795 + 2066467 * 2 ^ 59
def prefixEnd_2066467 : Nat := 4983230072969 + 3 ^ 40 * 2066467 * 2
def baseEnd_2066467 : Nat := 1061090827654671672058997

theorem tailTrace_2066467 : CollatzResearch.WordTrace tailWord_2066467 prefixEnd_2066467 1061090827654671672058997 := by
  unfold tailWord_2066467
  simp only [CollatzResearch.WordTrace]
  refine ⟨75370243404550458310957655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50246828936366972207305103 75370243404550458310957655)
  ·
    refine ⟨113055365106825687466436483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75370243404550458310957655 113055365106825687466436483)
    ·
      refine ⟨169583047660238531199654725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113055365106825687466436483 169583047660238531199654725)
      ·
        refine ⟨31796821436294724599935261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169583047660238531199654725 31796821436294724599935261)
        ·
          refine ⟨11923808038610521724975723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31796821436294724599935261 11923808038610521724975723)
          ·
            refine ⟨17885712057915782587463585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923808038610521724975723 17885712057915782587463585)
            ·
              refine ⟨13414284043436836940597689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17885712057915782587463585 13414284043436836940597689)
              ·
                refine ⟨10060713032577627705448267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13414284043436836940597689 10060713032577627705448267)
                ·
                  refine ⟨15091069548866441558172401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10060713032577627705448267 15091069548866441558172401)
                  ·
                    refine ⟨11318302161649831168629301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15091069548866441558172401 11318302161649831168629301)
                    ·
                      refine ⟨1061090827654671672058997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11318302161649831168629301 1061090827654671672058997)
                      ·
                        rfl

theorem cell23_2066467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_2066467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066467 prefixEnd_2066467 := by exact prefixLift 2066467
  have htrace : WordTrace (prefixWord ++ tailWord_2066467) baseStart_2066467 baseEnd_2066467 := by
    simpa [prefixWord, tailWord_2066467, baseEnd_2066467] using wordTrace_append hprefix tailTrace_2066467
  have hstable : (prefixWord ++ tailWord_2066467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066467).length < 2 ^ (prefixWord ++ tailWord_2066467).sum := by decide
  have hdescent : baseEnd_2066467 < baseStart_2066467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066474 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2066474 : Nat := 118140960795 + 2066474 * 2 ^ 59
def prefixEnd_2066474 : Nat := 4983230072969 + 3 ^ 40 * 2066474 * 2
def baseEnd_2066474 : Nat := 353698140673084381557155

theorem tailTrace_2066474 : CollatzResearch.WordTrace tailWord_2066474 prefixEnd_2066474 353698140673084381557155 := by
  unfold tailWord_2066474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842624678881274626615619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50246999143683399004308317 18842624678881274626615619)
  ·
    refine ⟨28263937018321911939923429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18842624678881274626615619 28263937018321911939923429)
    ·
      refine ⟨5299488190935358488735643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28263937018321911939923429 5299488190935358488735643)
      ·
        refine ⟨7949232286403037733103465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299488190935358488735643 7949232286403037733103465)
        ·
          refine ⟨5961924214802278299827599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949232286403037733103465 5961924214802278299827599)
          ·
            refine ⟨8942886322203417449741399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961924214802278299827599 8942886322203417449741399)
            ·
              refine ⟨13414329483305126174612099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942886322203417449741399 13414329483305126174612099)
              ·
                refine ⟨20121494224957689261918149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13414329483305126174612099 20121494224957689261918149)
                ·
                  refine ⟨3772780167179566736609653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20121494224957689261918149 3772780167179566736609653)
                  ·
                    refine ⟨353698140673084381557155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3772780167179566736609653 353698140673084381557155)
                    ·
                      rfl

theorem cell23_2066474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2066474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066474 prefixEnd_2066474 := by exact prefixLift 2066474
  have htrace : WordTrace (prefixWord ++ tailWord_2066474) baseStart_2066474 baseEnd_2066474 := by
    simpa [prefixWord, tailWord_2066474, baseEnd_2066474] using wordTrace_append hprefix tailTrace_2066474
  have hstable : (prefixWord ++ tailWord_2066474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066474).length < 2 ^ (prefixWord ++ tailWord_2066474).sum := by decide
  have hdescent : baseEnd_2066474 < baseStart_2066474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066478 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_2066478 : Nat := 118140960795 + 2066478 * 2 ^ 59
def prefixEnd_2066478 : Nat := 4983230072969 + 3 ^ 40 * 2066478 * 2
def baseEnd_2066478 : Nat := 117899608437985681002383

theorem tailTrace_2066478 : CollatzResearch.WordTrace tailWord_2066478 prefixEnd_2066478 117899608437985681002383 := by
  unfold tailWord_2066478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421330575938825898701011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50247096405007071459738725 9421330575938825898701011)
  ·
    refine ⟨14131995863908238848051517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9421330575938825898701011 14131995863908238848051517)
    ·
      refine ⟨5299498448965589568019319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14131995863908238848051517 5299498448965589568019319)
      ·
        refine ⟨7949247673448384352028979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299498448965589568019319 7949247673448384352028979)
        ·
          refine ⟨11923871510172576528043469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949247673448384352028979 11923871510172576528043469)
          ·
            refine ⟨4471451816314716198016301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11923871510172576528043469 4471451816314716198016301)
            ·
              refine ⟨1676794431118018574256113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4471451816314716198016301 1676794431118018574256113)
              ·
                refine ⟨1257595823338513930692085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676794431118018574256113 1257595823338513930692085)
                ·
                  refine ⟨117899608437985681002383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1257595823338513930692085 117899608437985681002383)
                  ·
                    rfl

theorem cell23_2066478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_2066478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066478 prefixEnd_2066478 := by exact prefixLift 2066478
  have htrace : WordTrace (prefixWord ++ tailWord_2066478) baseStart_2066478 baseEnd_2066478 := by
    simpa [prefixWord, tailWord_2066478, baseEnd_2066478] using wordTrace_append hprefix tailTrace_2066478
  have hstable : (prefixWord ++ tailWord_2066478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066478).length < 2 ^ (prefixWord ++ tailWord_2066478).sum := by decide
  have hdescent : baseEnd_2066478 < baseStart_2066478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066521 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 1, 4]
def baseStart_2066521 : Nat := 118140960795 + 2066521 * 2 ^ 59
def prefixEnd_2066521 : Nat := 4983230072969 + 3 ^ 40 * 2066521 * 2
def baseEnd_2066521 : Nat := 353706185203338153594583

theorem tailTrace_2066521 : CollatzResearch.WordTrace tailWord_2066521 prefixEnd_2066521 353706185203338153594583 := by
  unfold tailWord_2066521
  simp only [CollatzResearch.WordTrace]
  refine ⟨75372212946354825533423417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50248141964236550355615611 75372212946354825533423417)
  ·
    refine ⟨56529159709766119150067563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75372212946354825533423417 56529159709766119150067563)
    ·
      refine ⟨84793739564649178725101345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56529159709766119150067563 84793739564649178725101345)
      ·
        refine ⟨63595304673486884043826009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84793739564649178725101345 63595304673486884043826009)
        ·
          refine ⟨47696478505115163032869507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63595304673486884043826009 47696478505115163032869507)
          ·
            refine ⟨71544717757672744549304261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47696478505115163032869507 71544717757672744549304261)
            ·
              refine ⟨13414634579563639602994549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71544717757672744549304261 13414634579563639602994549)
              ·
                refine ⟨1257621991834091212780739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13414634579563639602994549 1257621991834091212780739)
                ·
                  refine ⟨1886432987751136819171109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257621991834091212780739 1886432987751136819171109)
                  ·
                    refine ⟨353706185203338153594583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886432987751136819171109 353706185203338153594583)
                    ·
                      rfl

theorem cell23_2066521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 4].length) (baseStart_2066521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066521 prefixEnd_2066521 := by exact prefixLift 2066521
  have htrace : WordTrace (prefixWord ++ tailWord_2066521) baseStart_2066521 baseEnd_2066521 := by
    simpa [prefixWord, tailWord_2066521, baseEnd_2066521] using wordTrace_append hprefix tailTrace_2066521
  have hstable : (prefixWord ++ tailWord_2066521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066521).length < 2 ^ (prefixWord ++ tailWord_2066521).sum := by decide
  have hdescent : baseEnd_2066521 < baseStart_2066521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066537 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_2066537 : Nat := 118140960795 + 2066537 * 2 ^ 59
def prefixEnd_2066537 : Nat := 4983230072969 + 3 ^ 40 * 2066537 * 2
def baseEnd_2066537 : Nat := 1061126771300486398183675

theorem tailTrace_2066537 : CollatzResearch.WordTrace tailWord_2066537 prefixEnd_2066537 1061126771300486398183675 := by
  unfold tailWord_2066537
  simp only [CollatzResearch.WordTrace]
  refine ⟨75372796514296860266005865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50248531009531240177337243 75372796514296860266005865)
  ·
    refine ⟨56529597385722645199504399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75372796514296860266005865 56529597385722645199504399)
    ·
      refine ⟨84794396078583967799256599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56529597385722645199504399 84794396078583967799256599)
      ·
        refine ⟨127191594117875951698884899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84794396078583967799256599 127191594117875951698884899)
        ·
          refine ⟨190787391176813927548327349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127191594117875951698884899 190787391176813927548327349)
          ·
            refine ⟨17886317922826305707655689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190787391176813927548327349 17886317922826305707655689)
            ·
              refine ⟨13414738442119729280741767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17886317922826305707655689 13414738442119729280741767)
              ·
                refine ⟨20122107663179593921112651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13414738442119729280741767 20122107663179593921112651)
                ·
                  refine ⟨30183161494769390881668977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20122107663179593921112651 30183161494769390881668977)
                  ·
                    refine ⟨22637371121077043161251733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30183161494769390881668977 22637371121077043161251733)
                    ·
                      refine ⟨1061126771300486398183675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22637371121077043161251733 1061126771300486398183675)
                      ·
                        rfl

theorem cell23_2066537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_2066537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066537 prefixEnd_2066537 := by exact prefixLift 2066537
  have htrace : WordTrace (prefixWord ++ tailWord_2066537) baseStart_2066537 baseEnd_2066537 := by
    simpa [prefixWord, tailWord_2066537, baseEnd_2066537] using wordTrace_append hprefix tailTrace_2066537
  have hstable : (prefixWord ++ tailWord_2066537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066537).length < 2 ^ (prefixWord ++ tailWord_2066537).sum := by decide
  have hdescent : baseEnd_2066537 < baseStart_2066537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066564 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_2066564 : Nat := 118140960795 + 2066564 * 2 ^ 59
def prefixEnd_2066564 : Nat := 4983230072969 + 3 ^ 40 * 2066564 * 2
def baseEnd_2066564 : Nat := 353713545092719264182017

theorem tailTrace_2066564 : CollatzResearch.WordTrace tailWord_2066564 prefixEnd_2066564 353713545092719264182017 := by
  unfold tailWord_2066564
  simp only [CollatzResearch.WordTrace]
  refine ⟨37686890642599521938619373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50249187523466029251492497 37686890642599521938619373)
  ·
    refine ⟨14132583990974820726982265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37686890642599521938619373 14132583990974820726982265)
    ·
      refine ⟨10599437993231115545236699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14132583990974820726982265 10599437993231115545236699)
      ·
        refine ⟨15899156989846673317855049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599437993231115545236699 15899156989846673317855049)
        ·
          refine ⟨11924367742385004988391287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15899156989846673317855049 11924367742385004988391287)
          ·
            refine ⟨17886551613577507482586931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924367742385004988391287 17886551613577507482586931)
            ·
              refine ⟨26829827420366261223880397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17886551613577507482586931 26829827420366261223880397)
              ·
                refine ⟨10061185282637347958955149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26829827420366261223880397 10061185282637347958955149)
                ·
                  refine ⟨3772944480989005484608181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10061185282637347958955149 3772944480989005484608181)
                  ·
                    refine ⟨353713545092719264182017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3772944480989005484608181 353713545092719264182017)
                    ·
                      rfl

theorem cell23_2066564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_2066564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066564 prefixEnd_2066564 := by exact prefixLift 2066564
  have htrace : WordTrace (prefixWord ++ tailWord_2066564) baseStart_2066564 baseEnd_2066564 := by
    simpa [prefixWord, tailWord_2066564, baseEnd_2066564] using wordTrace_append hprefix tailTrace_2066564
  have hstable : (prefixWord ++ tailWord_2066564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066564).length < 2 ^ (prefixWord ++ tailWord_2066564).sum := by decide
  have hdescent : baseEnd_2066564 < baseStart_2066564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066607 : List Nat := [1, 1, 2, 1, 2, 3, 1, 12]
def baseStart_2066607 : Nat := 118140960795 + 2066607 * 2 ^ 59
def prefixEnd_2066607 : Nat := 4983230072969 + 3 ^ 40 * 2066607 * 2
def baseEnd_2066607 : Nat := 39302322775788930529939

theorem tailTrace_2066607 : CollatzResearch.WordTrace tailWord_2066607 prefixEnd_2066607 39302322775788930529939 := by
  unfold tailWord_2066607
  simp only [CollatzResearch.WordTrace]
  refine ⟨75375349624043262221054075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50250233082695508147369383 75375349624043262221054075)
  ·
    refine ⟨113063024436064893331581113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75375349624043262221054075 113063024436064893331581113)
    ·
      refine ⟨84797268327048669998685835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113063024436064893331581113 84797268327048669998685835)
      ·
        refine ⟨127195902490573004998028753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84797268327048669998685835 127195902490573004998028753)
        ·
          refine ⟨95396926867929753748521565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127195902490573004998028753 95396926867929753748521565)
          ·
            refine ⟨35773847575473657655695587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95396926867929753748521565 35773847575473657655695587)
            ·
              refine ⟨53660771363210486483543381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35773847575473657655695587 53660771363210486483543381)
              ·
                refine ⟨39302322775788930529939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 53660771363210486483543381 39302322775788930529939)
                ·
                  rfl

theorem cell23_2066607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 12].length) (baseStart_2066607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066607 prefixEnd_2066607 := by exact prefixLift 2066607
  have htrace : WordTrace (prefixWord ++ tailWord_2066607) baseStart_2066607 baseEnd_2066607 := by
    simpa [prefixWord, tailWord_2066607, baseEnd_2066607] using wordTrace_append hprefix tailTrace_2066607
  have hstable : (prefixWord ++ tailWord_2066607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066607).length < 2 ^ (prefixWord ++ tailWord_2066607).sum := by decide
  have hdescent : baseEnd_2066607 < baseStart_2066607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066618 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2]
def baseStart_2066618 : Nat := 118140960795 + 2066618 * 2 ^ 59
def prefixEnd_2066618 : Nat := 4983230072969 + 3 ^ 40 * 2066618 * 2
def baseEnd_2066618 : Nat := 1061168363233500581270803

theorem tailTrace_2066618 : CollatzResearch.WordTrace tailWord_2066618 prefixEnd_2066618 1061168363233500581270803 := by
  unfold tailWord_2066618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843937706750852774926127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50250500551335607399803005 18843937706750852774926127)
  ·
    refine ⟨28265906560126279162389191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18843937706750852774926127 28265906560126279162389191)
    ·
      refine ⟨42398859840189418743583787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28265906560126279162389191 42398859840189418743583787)
      ·
        refine ⟨63598289760284128115375681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42398859840189418743583787 63598289760284128115375681)
        ·
          refine ⟨47698717320213096086531761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63598289760284128115375681 47698717320213096086531761)
          ·
            refine ⟨35774037990159822064898821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47698717320213096086531761 35774037990159822064898821)
            ·
              refine ⟨6707632123154966637168529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35774037990159822064898821 6707632123154966637168529)
              ·
                refine ⟨5030724092366224977876397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707632123154966637168529 5030724092366224977876397)
                ·
                  refine ⟨1886521534637334366703649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5030724092366224977876397 1886521534637334366703649)
                  ·
                    refine ⟨1414891150978000775027737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1886521534637334366703649 1414891150978000775027737)
                    ·
                      refine ⟨1061168363233500581270803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414891150978000775027737 1061168363233500581270803)
                      ·
                        rfl

theorem cell23_2066618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_2066618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066618 prefixEnd_2066618 := by exact prefixLift 2066618
  have htrace : WordTrace (prefixWord ++ tailWord_2066618) baseStart_2066618 baseEnd_2066618 := by
    simpa [prefixWord, tailWord_2066618, baseEnd_2066618] using wordTrace_append hprefix tailTrace_2066618
  have hstable : (prefixWord ++ tailWord_2066618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066618).length < 2 ^ (prefixWord ++ tailWord_2066618).sum := by decide
  have hdescent : baseEnd_2066618 < baseStart_2066618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066624 : List Nat := [2, 1, 1, 2, 5, 2, 1, 9]
def baseStart_2066624 : Nat := 118140960795 + 2066624 * 2 ^ 59
def prefixEnd_2066624 : Nat := 4983230072969 + 3 ^ 40 * 2066624 * 2
def baseEnd_2066624 : Nat := 39302646078423242881325

theorem tailTrace_2066624 : CollatzResearch.WordTrace tailWord_2066624 prefixEnd_2066624 39302646078423242881325 := by
  unfold tailWord_2066624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37687984832490837062211463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50250646443321116082948617 37687984832490837062211463)
  ·
    refine ⟨56531977248736255593317195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37687984832490837062211463 56531977248736255593317195)
    ·
      refine ⟨84797965873104383389975793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56531977248736255593317195 84797965873104383389975793)
      ·
        refine ⟨63598474404828287542481845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84797965873104383389975793 63598474404828287542481845)
        ·
          refine ⟨5962356975452651957107673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63598474404828287542481845 5962356975452651957107673)
          ·
            refine ⟨4471767731589488967830755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962356975452651957107673 4471767731589488967830755)
            ·
              refine ⟨6707651597384233451746133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471767731589488967830755 6707651597384233451746133)
              ·
                refine ⟨39302646078423242881325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6707651597384233451746133 39302646078423242881325)
                ·
                  rfl

theorem cell23_2066624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 9].length) (baseStart_2066624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066624 prefixEnd_2066624 := by exact prefixLift 2066624
  have htrace : WordTrace (prefixWord ++ tailWord_2066624) baseStart_2066624 baseEnd_2066624 := by
    simpa [prefixWord, tailWord_2066624, baseEnd_2066624] using wordTrace_append hprefix tailTrace_2066624
  have hstable : (prefixWord ++ tailWord_2066624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066624).length < 2 ^ (prefixWord ++ tailWord_2066624).sum := by decide
  have hdescent : baseEnd_2066624 < baseStart_2066624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066638 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_2066638 : Nat := 118140960795 + 2066638 * 2 ^ 59
def prefixEnd_2066638 : Nat := 4983230072969 + 3 ^ 40 * 2066638 * 2
def baseEnd_2066638 : Nat := 1061178632846590503020711

theorem tailTrace_2066638 : CollatzResearch.WordTrace tailWord_2066638 prefixEnd_2066638 1061178632846590503020711 := by
  unfold tailWord_2066638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422060035866369314429071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50250986857953969676955045 9422060035866369314429071)
  ·
    refine ⟨14133090053799553971643607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422060035866369314429071 14133090053799553971643607)
    ·
      refine ⟨21199635080699330957465411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14133090053799553971643607 21199635080699330957465411)
      ·
        refine ⟨31799452621048996436198117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21199635080699330957465411 31799452621048996436198117)
        ·
          refine ⟨5962397366446686831787147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31799452621048996436198117 5962397366446686831787147)
          ·
            refine ⟨8943596049670030247680721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962397366446686831787147 8943596049670030247680721)
            ·
              refine ⟨6707697037252522685760541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8943596049670030247680721 6707697037252522685760541)
              ·
                refine ⟨2515386388969696007160203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707697037252522685760541 2515386388969696007160203)
                ·
                  refine ⟨3773079583454544010740305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515386388969696007160203 3773079583454544010740305)
                  ·
                    refine ⟨2829809687590908008055229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3773079583454544010740305 2829809687590908008055229)
                    ·
                      refine ⟨1061178632846590503020711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2829809687590908008055229 1061178632846590503020711)
                      ·
                        rfl

theorem cell23_2066638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_2066638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066638 prefixEnd_2066638 := by exact prefixLift 2066638
  have htrace : WordTrace (prefixWord ++ tailWord_2066638) baseStart_2066638 baseEnd_2066638 := by
    simpa [prefixWord, tailWord_2066638, baseEnd_2066638] using wordTrace_append hprefix tailTrace_2066638
  have hstable : (prefixWord ++ tailWord_2066638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066638).length < 2 ^ (prefixWord ++ tailWord_2066638).sum := by decide
  have hdescent : baseEnd_2066638 < baseStart_2066638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066668 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_2066668 : Nat := 118140960795 + 2066668 * 2 ^ 59
def prefixEnd_2066668 : Nat := 4983230072969 + 3 ^ 40 * 2066668 * 2
def baseEnd_2066668 : Nat := 1061194037266225385645573

theorem tailTrace_2066668 : CollatzResearch.WordTrace tailWord_2066668 prefixEnd_2066668 1061194037266225385645573 := by
  unfold tailWord_2066668
  simp only [CollatzResearch.WordTrace]
  refine ⟨37688787238411134819512329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50251716317881513092683105 37688787238411134819512329)
  ·
    refine ⟨28266590428808351114634247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37688787238411134819512329 28266590428808351114634247)
    ·
      refine ⟨42399885643212526671951371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28266590428808351114634247 42399885643212526671951371)
      ·
        refine ⟨63599828464818790007927057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42399885643212526671951371 63599828464818790007927057)
        ·
          refine ⟨47699871348614092505945293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63599828464818790007927057 47699871348614092505945293)
          ·
            refine ⟨17887451755730284689729485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47699871348614092505945293 17887451755730284689729485)
            ·
              refine ⟨6707794408398856758648557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17887451755730284689729485 6707794408398856758648557)
              ·
                refine ⟨2515422903149571284493209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707794408398856758648557 2515422903149571284493209)
                ·
                  refine ⟨1886567177362178463369907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515422903149571284493209 1886567177362178463369907)
                  ·
                    refine ⟨2829850766043267695054861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1886567177362178463369907 2829850766043267695054861)
                    ·
                      refine ⟨1061194037266225385645573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2829850766043267695054861 1061194037266225385645573)
                      ·
                        rfl

theorem cell23_2066668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_2066668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066668 prefixEnd_2066668 := by exact prefixLift 2066668
  have htrace : WordTrace (prefixWord ++ tailWord_2066668) baseStart_2066668 baseEnd_2066668 := by
    simpa [prefixWord, tailWord_2066668, baseEnd_2066668] using wordTrace_append hprefix tailTrace_2066668
  have hstable : (prefixWord ++ tailWord_2066668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066668).length < 2 ^ (prefixWord ++ tailWord_2066668).sum := by decide
  have hdescent : baseEnd_2066668 < baseStart_2066668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066711 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2066711 : Nat := 118140960795 + 2066711 * 2 ^ 59
def prefixEnd_2066711 : Nat := 4983230072969 + 3 ^ 40 * 2066711 * 2
def baseEnd_2066711 : Nat := 1061216116934368717407875

theorem tailTrace_2066711 : CollatzResearch.WordTrace tailWord_2066711 prefixEnd_2066711 1061216116934368717407875 := by
  unfold tailWord_2066711
  simp only [CollatzResearch.WordTrace]
  refine ⟨75379142815666487982839987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50252761877110991988559991 75379142815666487982839987)
  ·
    refine ⟨113068714223499731974259981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75379142815666487982839987 113068714223499731974259981)
    ·
      refine ⟨42400767833812399490347493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113068714223499731974259981 42400767833812399490347493)
      ·
        refine ⟨7950143968839824904440155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42400767833812399490347493 7950143968839824904440155)
        ·
          refine ⟨11925215953259737356660233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7950143968839824904440155 11925215953259737356660233)
          ·
            refine ⟨8943911964944803017495175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925215953259737356660233 8943911964944803017495175)
            ·
              refine ⟨13415867947417204526242763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8943911964944803017495175 13415867947417204526242763)
              ·
                refine ⟨20123801921125806789364145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13415867947417204526242763 20123801921125806789364145)
                ·
                  refine ⟨15092851440844355092023109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20123801921125806789364145 15092851440844355092023109)
                  ·
                    refine ⟨2829909645158316579754333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15092851440844355092023109 2829909645158316579754333)
                    ·
                      refine ⟨1061216116934368717407875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2829909645158316579754333 1061216116934368717407875)
                      ·
                        rfl

theorem cell23_2066711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2066711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066711 prefixEnd_2066711 := by exact prefixLift 2066711
  have htrace : WordTrace (prefixWord ++ tailWord_2066711) baseStart_2066711 baseEnd_2066711 := by
    simpa [prefixWord, tailWord_2066711, baseEnd_2066711] using wordTrace_append hprefix tailTrace_2066711
  have hstable : (prefixWord ++ tailWord_2066711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066711).length < 2 ^ (prefixWord ++ tailWord_2066711).sum := by decide
  have hdescent : baseEnd_2066711 < baseStart_2066711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066718 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2066718 : Nat := 118140960795 + 2066718 * 2 ^ 59
def prefixEnd_2066718 : Nat := 4983230072969 + 3 ^ 40 * 2066718 * 2
def baseEnd_2066718 : Nat := 353739903766316730006781

theorem tailTrace_2066718 : CollatzResearch.WordTrace tailWord_2066718 prefixEnd_2066718 353739903766316730006781 := by
  unfold tailWord_2066718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422424765830141022293101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50252932084427418785563205 9422424765830141022293101)
  ·
    refine ⟨3533409287186302883359913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9422424765830141022293101 3533409287186302883359913)
    ·
      refine ⟨2650056965389727162519935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3533409287186302883359913 2650056965389727162519935)
      ·
        refine ⟨3975085448084590743779903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650056965389727162519935 3975085448084590743779903)
        ·
          refine ⟨5962628172126886115669855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975085448084590743779903 5962628172126886115669855)
          ·
            refine ⟨8943942258190329173504783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962628172126886115669855 8943942258190329173504783)
            ·
              refine ⟨13415913387285493760257175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8943942258190329173504783 13415913387285493760257175)
              ·
                refine ⟨20123870080928240640385763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13415913387285493760257175 20123870080928240640385763)
                ·
                  refine ⟨30185805121392360960578645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20123870080928240640385763 30185805121392360960578645)
                  ·
                    refine ⟨353739903766316730006781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30185805121392360960578645 353739903766316730006781)
                    ·
                      rfl

theorem cell23_2066718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2066718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066718 prefixEnd_2066718 := by exact prefixLift 2066718
  have htrace : WordTrace (prefixWord ++ tailWord_2066718) baseStart_2066718 baseEnd_2066718 := by
    simpa [prefixWord, tailWord_2066718, baseEnd_2066718] using wordTrace_append hprefix tailTrace_2066718
  have hstable : (prefixWord ++ tailWord_2066718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066718).length < 2 ^ (prefixWord ++ tailWord_2066718).sum := by decide
  have hdescent : baseEnd_2066718 < baseStart_2066718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066725 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 1, 4, 2]
def baseStart_2066725 : Nat := 118140960795 + 2066725 * 2 ^ 59
def prefixEnd_2066725 : Nat := 4983230072969 + 3 ^ 40 * 2066725 * 2
def baseEnd_2066725 : Nat := 1061223305663531662632811

theorem tailTrace_2066725 : CollatzResearch.WordTrace tailWord_2066725 prefixEnd_2066725 1061223305663531662632811 := by
  unfold tailWord_2066725
  simp only [CollatzResearch.WordTrace]
  refine ⟨75379653437615768373849629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50253102291743845582566419 75379653437615768373849629)
  ·
    refine ⟨28267370039105913140193611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75379653437615768373849629 28267370039105913140193611)
    ·
      refine ⟨42401055058658869710290417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28267370039105913140193611 42401055058658869710290417)
      ·
        refine ⟨31800791293994152282717813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42401055058658869710290417 31800791293994152282717813)
        ·
          refine ⟨2981324183811951776504795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31800791293994152282717813 2981324183811951776504795)
          ·
            refine ⟨4471986275717927664757193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981324183811951776504795 4471986275717927664757193)
            ·
              refine ⟨3353989706788445748567895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4471986275717927664757193 3353989706788445748567895)
              ·
                refine ⟨5030984560182668622851843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353989706788445748567895 5030984560182668622851843)
                ·
                  refine ⟨7546476840274002934277765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030984560182668622851843 7546476840274002934277765)
                  ·
                    refine ⟨1414964407551375550177081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546476840274002934277765 1414964407551375550177081)
                    ·
                      refine ⟨1061223305663531662632811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1414964407551375550177081 1061223305663531662632811)
                      ·
                        rfl

theorem cell23_2066725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_2066725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066725 prefixEnd_2066725 := by exact prefixLift 2066725
  have htrace : WordTrace (prefixWord ++ tailWord_2066725) baseStart_2066725 baseEnd_2066725 := by
    simpa [prefixWord, tailWord_2066725, baseEnd_2066725] using wordTrace_append hprefix tailTrace_2066725
  have hstable : (prefixWord ++ tailWord_2066725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066725).length < 2 ^ (prefixWord ++ tailWord_2066725).sum := by decide
  have hdescent : baseEnd_2066725 < baseStart_2066725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066741 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2066741 : Nat := 118140960795 + 2066741 * 2 ^ 59
def prefixEnd_2066741 : Nat := 4983230072969 + 3 ^ 40 * 2066741 * 2
def baseEnd_2066741 : Nat := 1061231521354003600032737

theorem tailTrace_2066741 : CollatzResearch.WordTrace tailWord_2066741 prefixEnd_2066741 1061231521354003600032737 := by
  unfold tailWord_2066741
  simp only [CollatzResearch.WordTrace]
  refine ⟨75380237005557803106432077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50253491337038535404288051 75380237005557803106432077)
  ·
    refine ⟨28267588877084176164912029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75380237005557803106432077 28267588877084176164912029)
    ·
      refine ⟨10600345828906566061842011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28267588877084176164912029 10600345828906566061842011)
      ·
        refine ⟨15900518743359849092763017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600345828906566061842011 15900518743359849092763017)
        ·
          refine ⟨11925389057519886819572263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15900518743359849092763017 11925389057519886819572263)
          ·
            refine ⟨17888083586279830229358395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11925389057519886819572263 17888083586279830229358395)
            ·
              refine ⟨26832125379419745344037593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17888083586279830229358395 26832125379419745344037593)
              ·
                refine ⟨20124094034564809008028195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26832125379419745344037593 20124094034564809008028195)
                ·
                  refine ⟨30186141051847213512042293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20124094034564809008028195 30186141051847213512042293)
                  ·
                    refine ⟨2829950723610676266753965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30186141051847213512042293 2829950723610676266753965)
                    ·
                      refine ⟨1061231521354003600032737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2829950723610676266753965 1061231521354003600032737)
                      ·
                        rfl

theorem cell23_2066741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2066741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066741 prefixEnd_2066741 := by exact prefixLift 2066741
  have htrace : WordTrace (prefixWord ++ tailWord_2066741) baseStart_2066741 baseEnd_2066741 := by
    simpa [prefixWord, tailWord_2066741, baseEnd_2066741] using wordTrace_append hprefix tailTrace_2066741
  have hstable : (prefixWord ++ tailWord_2066741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066741).length < 2 ^ (prefixWord ++ tailWord_2066741).sum := by decide
  have hdescent : baseEnd_2066741 < baseStart_2066741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066748 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 5]
def baseStart_2066748 : Nat := 118140960795 + 2066748 * 2 ^ 59
def prefixEnd_2066748 : Nat := 4983230072969 + 3 ^ 40 * 2066748 * 2
def baseEnd_2066748 : Nat := 117915012857620563627245

theorem tailTrace_2066748 : CollatzResearch.WordTrace tailWord_2066748 prefixEnd_2066748 117915012857620563627245 := by
  unfold tailWord_2066748
  simp only [CollatzResearch.WordTrace]
  refine ⟨37690246158266221650968449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50253661544354962201291265 37690246158266221650968449)
  ·
    refine ⟨28267684618699666238226337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37690246158266221650968449 28267684618699666238226337)
    ·
      refine ⟨21200763464024749678669753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28267684618699666238226337 21200763464024749678669753)
      ·
        refine ⟨15900572598018562259002315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21200763464024749678669753 15900572598018562259002315)
        ·
          refine ⟨23850858897027843388503473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900572598018562259002315 23850858897027843388503473)
          ·
            refine ⟨17888144172770882541377605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23850858897027843388503473 17888144172770882541377605)
            ·
              refine ⟨3354027032394540476508301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17888144172770882541377605 3354027032394540476508301)
              ·
                refine ⟨1257760137147952678690613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3354027032394540476508301 1257760137147952678690613)
                ·
                  refine ⟨117915012857620563627245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1257760137147952678690613 117915012857620563627245)
                  ·
                    rfl

theorem cell23_2066748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_2066748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066748 prefixEnd_2066748 := by exact prefixLift 2066748
  have htrace : WordTrace (prefixWord ++ tailWord_2066748) baseStart_2066748 baseEnd_2066748 := by
    simpa [prefixWord, tailWord_2066748, baseEnd_2066748] using wordTrace_append hprefix tailTrace_2066748
  have hstable : (prefixWord ++ tailWord_2066748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066748).length < 2 ^ (prefixWord ++ tailWord_2066748).sum := by decide
  have hdescent : baseEnd_2066748 < baseStart_2066748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066821 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 6]
def baseStart_2066821 : Nat := 118140960795 + 2066821 * 2 ^ 59
def prefixEnd_2066821 : Nat := 4983230072969 + 3 ^ 40 * 2066821 * 2
def baseEnd_2066821 : Nat := 117919177756262587448041

theorem tailTrace_2066821 : CollatzResearch.WordTrace tailWord_2066821 prefixEnd_2066821 117919177756262587448041 := by
  unfold tailWord_2066821
  simp only [CollatzResearch.WordTrace]
  refine ⟨75383154845267976769344317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50255436563511984512896211 75383154845267976769344317)
  ·
    refine ⟨28268683066975491288504119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75383154845267976769344317 28268683066975491288504119)
    ·
      refine ⟨42403024600463236932756179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28268683066975491288504119 42403024600463236932756179)
      ·
        refine ⟨63604536900694855399134269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42403024600463236932756179 63604536900694855399134269)
        ·
          refine ⟨23851701337760570774675351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63604536900694855399134269 23851701337760570774675351)
          ·
            refine ⟨35777552006640856162013027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23851701337760570774675351 35777552006640856162013027)
            ·
              refine ⟨53666328009961284243019541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35777552006640856162013027 53666328009961284243019541)
              ·
                refine ⟨2515609125466935198891541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53666328009961284243019541 2515609125466935198891541)
                ·
                  refine ⟨117919177756262587448041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2515609125466935198891541 117919177756262587448041)
                  ·
                    rfl

theorem cell23_2066821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_2066821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066821 prefixEnd_2066821 := by exact prefixLift 2066821
  have htrace : WordTrace (prefixWord ++ tailWord_2066821) baseStart_2066821 baseEnd_2066821 := by
    simpa [prefixWord, tailWord_2066821, baseEnd_2066821] using wordTrace_append hprefix tailTrace_2066821
  have hstable : (prefixWord ++ tailWord_2066821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066821).length < 2 ^ (prefixWord ++ tailWord_2066821).sum := by decide
  have hdescent : baseEnd_2066821 < baseStart_2066821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066825 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 3, 4]
def baseStart_2066825 : Nat := 118140960795 + 2066825 * 2 ^ 59
def prefixEnd_2066825 : Nat := 4983230072969 + 3 ^ 40 * 2066825 * 2
def baseEnd_2066825 : Nat := 353758217909660423794117

theorem tailTrace_2066825 : CollatzResearch.WordTrace tailWord_2066825 prefixEnd_2066825 353758217909660423794117 := by
  unfold tailWord_2066825
  simp only [CollatzResearch.WordTrace]
  refine ⟨75383300737253485452489929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50255533824835656968326619 75383300737253485452489929)
  ·
    refine ⟨56537475552940114089367447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75383300737253485452489929 56537475552940114089367447)
    ·
      refine ⟨84806213329410171134051171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56537475552940114089367447 84806213329410171134051171)
      ·
        refine ⟨127209319994115256701076757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84806213329410171134051171 127209319994115256701076757)
        ·
          refine ⟨5962936874724152657862973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127209319994115256701076757 5962936874724152657862973)
          ·
            refine ⟨2236101328021557246698615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5962936874724152657862973 2236101328021557246698615)
            ·
              refine ⟨3354151992032335870047923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236101328021557246698615 3354151992032335870047923)
              ·
                refine ⟨5031227988048503805071885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354151992032335870047923 5031227988048503805071885)
                ·
                  refine ⟨1886710495518188926901957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5031227988048503805071885 1886710495518188926901957)
                  ·
                    refine ⟨353758217909660423794117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886710495518188926901957 353758217909660423794117)
                    ·
                      rfl

theorem cell23_2066825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_2066825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066825 prefixEnd_2066825 := by exact prefixLift 2066825
  have htrace : WordTrace (prefixWord ++ tailWord_2066825) baseStart_2066825 baseEnd_2066825 := by
    simpa [prefixWord, tailWord_2066825, baseEnd_2066825] using wordTrace_append hprefix tailTrace_2066825
  have hstable : (prefixWord ++ tailWord_2066825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066825).length < 2 ^ (prefixWord ++ tailWord_2066825).sum := by decide
  have hdescent : baseEnd_2066825 < baseStart_2066825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066888 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_2066888 : Nat := 118140960795 + 2066888 * 2 ^ 59
def prefixEnd_2066888 : Nat := 4983230072969 + 3 ^ 40 * 2066888 * 2
def baseEnd_2066888 : Nat := 1061307003010214524894561

theorem tailTrace_2066888 : CollatzResearch.WordTrace tailWord_2066888 prefixEnd_2066888 1061307003010214524894561 := by
  unfold tailWord_2066888
  simp only [CollatzResearch.WordTrace]
  refine ⟨37692799268012623606016659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50257065690683498141355545 37692799268012623606016659)
  ·
    refine ⟨56539198902018935409024989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37692799268012623606016659 56539198902018935409024989)
    ·
      refine ⟨21202199588257100778384371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56539198902018935409024989 21202199588257100778384371)
      ·
        refine ⟨31803299382385651167576557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21202199588257100778384371 31803299382385651167576557)
        ·
          refine ⟨11926237268394619187841209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31803299382385651167576557 11926237268394619187841209)
          ·
            refine ⟨8944677951295964390880907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11926237268394619187841209 8944677951295964390880907)
            ·
              refine ⟨13417016926943946586321361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944677951295964390880907 13417016926943946586321361)
              ·
                refine ⟨10062762695207959939741021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13417016926943946586321361 10062762695207959939741021)
                ·
                  refine ⟨3773536010702984977402883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10062762695207959939741021 3773536010702984977402883)
                  ·
                    refine ⟨5660304016054477466104325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773536010702984977402883 5660304016054477466104325)
                    ·
                      refine ⟨1061307003010214524894561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5660304016054477466104325 1061307003010214524894561)
                      ·
                        rfl

theorem cell23_2066888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_2066888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066888 prefixEnd_2066888 := by exact prefixLift 2066888
  have htrace : WordTrace (prefixWord ++ tailWord_2066888) baseStart_2066888 baseEnd_2066888 := by
    simpa [prefixWord, tailWord_2066888, baseEnd_2066888] using wordTrace_append hprefix tailTrace_2066888
  have hstable : (prefixWord ++ tailWord_2066888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066888).length < 2 ^ (prefixWord ++ tailWord_2066888).sum := by decide
  have hdescent : baseEnd_2066888 < baseStart_2066888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066891 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5]
def baseStart_2066891 : Nat := 118140960795 + 2066891 * 2 ^ 59
def prefixEnd_2066891 : Nat := 4983230072969 + 3 ^ 40 * 2066891 * 2
def baseEnd_2066891 : Nat := 1061308543452178013157047

theorem tailTrace_2066891 : CollatzResearch.WordTrace tailWord_2066891 prefixEnd_2066891 1061308543452178013157047 := by
  unfold tailWord_2066891
  simp only [CollatzResearch.WordTrace]
  refine ⟨75385707955014378724392527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50257138636676252482928351 75385707955014378724392527)
  ·
    refine ⟨113078561932521568086588791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75385707955014378724392527 113078561932521568086588791)
    ·
      refine ⟨169617842898782352129883187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113078561932521568086588791 169617842898782352129883187)
      ·
        refine ⟨254426764348173528194824781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169617842898782352129883187 254426764348173528194824781)
        ·
          refine ⟨95410036630565073073059293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254426764348173528194824781 95410036630565073073059293)
          ·
            refine ⟨35778763736461902402397235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95410036630565073073059293 35778763736461902402397235)
            ·
              refine ⟨53668145604692853603595853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35778763736461902402397235 53668145604692853603595853)
              ·
                refine ⟨20125554601759820101348445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53668145604692853603595853 20125554601759820101348445)
                ·
                  refine ⟨7547082975659932538005667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20125554601759820101348445 7547082975659932538005667)
                  ·
                    refine ⟨11320624463489898807008501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7547082975659932538005667 11320624463489898807008501)
                    ·
                      refine ⟨1061308543452178013157047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11320624463489898807008501 1061308543452178013157047)
                      ·
                        rfl

theorem cell23_2066891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 5].length) (baseStart_2066891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066891 prefixEnd_2066891 := by exact prefixLift 2066891
  have htrace : WordTrace (prefixWord ++ tailWord_2066891) baseStart_2066891 baseEnd_2066891 := by
    simpa [prefixWord, tailWord_2066891, baseEnd_2066891] using wordTrace_append hprefix tailTrace_2066891
  have hstable : (prefixWord ++ tailWord_2066891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066891).length < 2 ^ (prefixWord ++ tailWord_2066891).sum := by decide
  have hdescent : baseEnd_2066891 < baseStart_2066891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066922 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_2066922 : Nat := 118140960795 + 2066922 * 2 ^ 59
def prefixEnd_2066922 : Nat := 4983230072969 + 3 ^ 40 * 2066922 * 2
def baseEnd_2066922 : Nat := 1061324461352467391869405

theorem tailTrace_2066922 : CollatzResearch.WordTrace tailWord_2066922 prefixEnd_2066922 1061324461352467391869405 := by
  unfold tailWord_2066922
  simp only [CollatzResearch.WordTrace]
  refine ⟨18846709654475517754692755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50257892411934714012514013 18846709654475517754692755)
  ·
    refine ⟨28270064481713276632039133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18846709654475517754692755 28270064481713276632039133)
    ·
      refine ⟨10601274180642478737014675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28270064481713276632039133 10601274180642478737014675)
      ·
        refine ⟨15901911270963718105522013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10601274180642478737014675 15901911270963718105522013)
        ·
          refine ⟨5963216726611394289570755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15901911270963718105522013 5963216726611394289570755)
          ·
            refine ⟨8944825089917091434356133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963216726611394289570755 8944825089917091434356133)
            ·
              refine ⟨1677154704359454643941775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8944825089917091434356133 1677154704359454643941775)
              ·
                refine ⟨2515732056539181965912663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677154704359454643941775 2515732056539181965912663)
                ·
                  refine ⟨3773598084808772948868995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515732056539181965912663 3773598084808772948868995)
                  ·
                    refine ⟨5660397127213159423303493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773598084808772948868995 5660397127213159423303493)
                    ·
                      refine ⟨1061324461352467391869405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5660397127213159423303493 1061324461352467391869405)
                      ·
                        rfl

theorem cell23_2066922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_2066922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066922 prefixEnd_2066922 := by exact prefixLift 2066922
  have htrace : WordTrace (prefixWord ++ tailWord_2066922) baseStart_2066922 baseEnd_2066922 := by
    simpa [prefixWord, tailWord_2066922, baseEnd_2066922] using wordTrace_append hprefix tailTrace_2066922
  have hstable : (prefixWord ++ tailWord_2066922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066922).length < 2 ^ (prefixWord ++ tailWord_2066922).sum := by decide
  have hdescent : baseEnd_2066922 < baseStart_2066922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066955 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 3]
def baseStart_2066955 : Nat := 118140960795 + 2066955 * 2 ^ 59
def prefixEnd_2066955 : Nat := 4983230072969 + 3 ^ 40 * 2066955 * 2
def baseEnd_2066955 : Nat := 1061341406214065762756753

theorem tailTrace_2066955 : CollatzResearch.WordTrace tailWord_2066955 prefixEnd_2066955 1061341406214065762756753 := by
  unfold tailWord_2066955
  simp only [CollatzResearch.WordTrace]
  refine ⟨75388042226782517654722319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50258694817855011769814879 75388042226782517654722319)
  ·
    refine ⟨113082063340173776482083479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75388042226782517654722319 113082063340173776482083479)
    ·
      refine ⟨169623095010260664723125219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113082063340173776482083479 169623095010260664723125219)
      ·
        refine ⟨254434642515390997084687829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169623095010260664723125219 254434642515390997084687829)
        ·
          refine ⟨5963311933954476494172371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 254434642515390997084687829 5963311933954476494172371)
          ·
            refine ⟨8944967900931714741258557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963311933954476494172371 8944967900931714741258557)
            ·
              refine ⟨3354362962849393027971959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8944967900931714741258557 3354362962849393027971959)
              ·
                refine ⟨5031544444274089541957939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354362962849393027971959 5031544444274089541957939)
                ·
                  refine ⟨7547316666411134312936909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031544444274089541957939 7547316666411134312936909)
                  ·
                    refine ⟨2830243749904175367351341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7547316666411134312936909 2830243749904175367351341)
                    ·
                      refine ⟨1061341406214065762756753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2830243749904175367351341 1061341406214065762756753)
                      ·
                        rfl

theorem cell23_2066955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3, 3].length) (baseStart_2066955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066955 prefixEnd_2066955 := by exact prefixLift 2066955
  have htrace : WordTrace (prefixWord ++ tailWord_2066955) baseStart_2066955 baseEnd_2066955 := by
    simpa [prefixWord, tailWord_2066955, baseEnd_2066955] using wordTrace_append hprefix tailTrace_2066955
  have hstable : (prefixWord ++ tailWord_2066955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066955).length < 2 ^ (prefixWord ++ tailWord_2066955).sum := by decide
  have hdescent : baseEnd_2066955 < baseStart_2066955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066961 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_2066961 : Nat := 118140960795 + 2066961 * 2 ^ 59
def prefixEnd_2066961 : Nat := 4983230072969 + 3 ^ 40 * 2066961 * 2
def baseEnd_2066961 : Nat := 1061344487097992739281725

theorem tailTrace_2066961 : CollatzResearch.WordTrace tailWord_2066961 prefixEnd_2066961 1061344487097992739281725 := by
  unfold tailWord_2066961
  simp only [CollatzResearch.WordTrace]
  refine ⟨75388261064760780679440737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50258840709840520452960491 75388261064760780679440737)
  ·
    refine ⟨56541195798570585509580553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75388261064760780679440737 56541195798570585509580553)
    ·
      refine ⟨42405896848927939132185415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56541195798570585509580553 42405896848927939132185415)
      ·
        refine ⟨63608845273391908698278123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42405896848927939132185415 63608845273391908698278123)
        ·
          refine ⟨95413267910087863047417185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63608845273391908698278123 95413267910087863047417185)
          ·
            refine ⟨71559950932565897285562889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95413267910087863047417185 71559950932565897285562889)
            ·
              refine ⟨53669963199424422964172167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71559950932565897285562889 53669963199424422964172167)
              ·
                refine ⟨80504944799136634446258251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53669963199424422964172167 80504944799136634446258251)
                ·
                  refine ⟨120757417198704951669387377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80504944799136634446258251 120757417198704951669387377)
                  ·
                    refine ⟨90568062899028713752040533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120757417198704951669387377 90568062899028713752040533)
                    ·
                      refine ⟨1061344487097992739281725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 90568062899028713752040533 1061344487097992739281725)
                      ·
                        rfl

theorem cell23_2066961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_2066961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066961 prefixEnd_2066961 := by exact prefixLift 2066961
  have htrace : WordTrace (prefixWord ++ tailWord_2066961) baseStart_2066961 baseEnd_2066961 := by
    simpa [prefixWord, tailWord_2066961, baseEnd_2066961] using wordTrace_append hprefix tailTrace_2066961
  have hstable : (prefixWord ++ tailWord_2066961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066961).length < 2 ^ (prefixWord ++ tailWord_2066961).sum := by decide
  have hdescent : baseEnd_2066961 < baseStart_2066961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066968 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2066968 : Nat := 118140960795 + 2066968 * 2 ^ 59
def prefixEnd_2066968 : Nat := 4983230072969 + 3 ^ 40 * 2066968 * 2
def baseEnd_2066968 : Nat := 1061348081462574211894193

theorem tailTrace_2066968 : CollatzResearch.WordTrace tailWord_2066968 prefixEnd_2066968 1061348081462574211894193 := by
  unfold tailWord_2066968
  simp only [CollatzResearch.WordTrace]
  refine ⟨37694258187867710437472779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50259010917156947249963705 37694258187867710437472779)
  ·
    refine ⟨56541387281801565656209169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37694258187867710437472779 56541387281801565656209169)
    ·
      refine ⟨42406040461351174242156877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56541387281801565656209169 42406040461351174242156877)
      ·
        refine ⟨15902265173006690340808829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42406040461351174242156877 15902265173006690340808829)
        ·
          refine ⟨5963349439877508877803311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15902265173006690340808829 5963349439877508877803311)
          ·
            refine ⟨8945024159816263316704967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963349439877508877803311 8945024159816263316704967)
            ·
              refine ⟨13417536239724394975057451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945024159816263316704967 13417536239724394975057451)
              ·
                refine ⟨20126304359586592462586177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13417536239724394975057451 20126304359586592462586177)
                ·
                  refine ⟨15094728269689944346939633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20126304359586592462586177 15094728269689944346939633)
                  ·
                    refine ⟨11321046202267458260204725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15094728269689944346939633 11321046202267458260204725)
                    ·
                      refine ⟨1061348081462574211894193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11321046202267458260204725 1061348081462574211894193)
                      ·
                        rfl

theorem cell23_2066968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2066968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066968 prefixEnd_2066968 := by exact prefixLift 2066968
  have htrace : WordTrace (prefixWord ++ tailWord_2066968) baseStart_2066968 baseEnd_2066968 := by
    simpa [prefixWord, tailWord_2066968, baseEnd_2066968] using wordTrace_append hprefix tailTrace_2066968
  have hstable : (prefixWord ++ tailWord_2066968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066968).length < 2 ^ (prefixWord ++ tailWord_2066968).sum := by decide
  have hdescent : baseEnd_2066968 < baseStart_2066968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066978 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2066978 : Nat := 118140960795 + 2066978 * 2 ^ 59
def prefixEnd_2066978 : Nat := 4983230072969 + 3 ^ 40 * 2066978 * 2
def baseEnd_2066978 : Nat := 1061353216269119172769147

theorem tailTrace_2066978 : CollatzResearch.WordTrace tailWord_2066978 prefixEnd_2066978 1061353216269119172769147 := by
  unfold tailWord_2066978
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847220276424798145702397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50259254070466128388539725 18847220276424798145702397)
  ·
    refine ⟨7067707603659299304638399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18847220276424798145702397 7067707603659299304638399)
    ·
      refine ⟨10601561405488948956957599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067707603659299304638399 10601561405488948956957599)
      ·
        refine ⟨15902342108233423435436399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10601561405488948956957599 15902342108233423435436399)
        ·
          refine ⟨23853513162350135153154599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15902342108233423435436399 23853513162350135153154599)
          ·
            refine ⟨35780269743525202729731899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23853513162350135153154599 35780269743525202729731899)
            ·
              refine ⟨53670404615287804094597849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35780269743525202729731899 53670404615287804094597849)
              ·
                refine ⟨40252803461465853070948387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53670404615287804094597849 40252803461465853070948387)
                ·
                  refine ⟨60379205192198779606422581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40252803461465853070948387 60379205192198779606422581)
                  ·
                    refine ⟨5660550486768635588102117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60379205192198779606422581 5660550486768635588102117)
                    ·
                      refine ⟨1061353216269119172769147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5660550486768635588102117 1061353216269119172769147)
                      ·
                        rfl

theorem cell23_2066978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2066978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2066978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2066978 prefixEnd_2066978 := by exact prefixLift 2066978
  have htrace : WordTrace (prefixWord ++ tailWord_2066978) baseStart_2066978 baseEnd_2066978 := by
    simpa [prefixWord, tailWord_2066978, baseEnd_2066978] using wordTrace_append hprefix tailTrace_2066978
  have hstable : (prefixWord ++ tailWord_2066978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066978).length < 2 ^ (prefixWord ++ tailWord_2066978).sum := by decide
  have hdescent : baseEnd_2066978 < baseStart_2066978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067006 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2067006 : Nat := 118140960795 + 2067006 * 2 ^ 59
def prefixEnd_2067006 : Nat := 4983230072969 + 3 ^ 40 * 2067006 * 2
def baseEnd_2067006 : Nat := 1061367593727445063219019

theorem tailTrace_2067006 : CollatzResearch.WordTrace tailWord_2067006 prefixEnd_2067006 1061367593727445063219019 := by
  unfold tailWord_2067006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423737793699719170603609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50259934899731835576552581 9423737793699719170603609)
  ·
    refine ⟨7067803345274789377952707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9423737793699719170603609 7067803345274789377952707)
    ·
      refine ⟨10601705017912184066929061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067803345274789377952707 10601705017912184066929061)
      ·
        refine ⟨1987819690858534512549199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10601705017912184066929061 1987819690858534512549199)
        ·
          refine ⟨2981729536287801768823799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987819690858534512549199 2981729536287801768823799)
          ·
            refine ⟨4472594304431702653235699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981729536287801768823799 4472594304431702653235699)
            ·
              refine ⟨6708891456647553979853549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472594304431702653235699 6708891456647553979853549)
              ·
                refine ⟨2515834296242832742445081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6708891456647553979853549 2515834296242832742445081)
                ·
                  refine ⟨1886875722182124556833811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515834296242832742445081 1886875722182124556833811)
                  ·
                    refine ⟨2830313583273186835250717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1886875722182124556833811 2830313583273186835250717)
                    ·
                      refine ⟨1061367593727445063219019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2830313583273186835250717 1061367593727445063219019)
                      ·
                        rfl

theorem cell23_2067006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2067006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067006 prefixEnd_2067006 := by exact prefixLift 2067006
  have htrace : WordTrace (prefixWord ++ tailWord_2067006) baseStart_2067006 baseEnd_2067006 := by
    simpa [prefixWord, tailWord_2067006, baseEnd_2067006] using wordTrace_append hprefix tailTrace_2067006
  have hstable : (prefixWord ++ tailWord_2067006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067006).length < 2 ^ (prefixWord ++ tailWord_2067006).sum := by decide
  have hdescent : baseEnd_2067006 < baseStart_2067006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067008 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_2067008 : Nat := 118140960795 + 2067008 * 2 ^ 59
def prefixEnd_2067008 : Nat := 4983230072969 + 3 ^ 40 * 2067008 * 2
def baseEnd_2067008 : Nat := 1061368620688754055394009

theorem tailTrace_2067008 : CollatzResearch.WordTrace tailWord_2067008 prefixEnd_2067008 1061368620688754055394009 := by
  unfold tailWord_2067008
  simp only [CollatzResearch.WordTrace]
  refine ⟨37694987647795253853200839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50259983530393671804267785 37694987647795253853200839)
  ·
    refine ⟨56542481471692880779801259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37694987647795253853200839 56542481471692880779801259)
    ·
      refine ⟨84813722207539321169701889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56542481471692880779801259 84813722207539321169701889)
      ·
        refine ⟨63610291655654490877276417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84813722207539321169701889 63610291655654490877276417)
        ·
          refine ⟨47707718741740868157957313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63610291655654490877276417 47707718741740868157957313)
          ·
            refine ⟨35780789056305651118467985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47707718741740868157957313 35780789056305651118467985)
            ·
              refine ⟨26835591792229238338850989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35780789056305651118467985 26835591792229238338850989)
              ·
                refine ⟨10063346922085964377069121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26835591792229238338850989 10063346922085964377069121)
                ·
                  refine ⟨7547510191564473282801841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10063346922085964377069121 7547510191564473282801841)
                  ·
                    refine ⟨5660632643673354962101381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7547510191564473282801841 5660632643673354962101381)
                    ·
                      refine ⟨1061368620688754055394009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5660632643673354962101381 1061368620688754055394009)
                      ·
                        rfl

theorem cell23_2067008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_2067008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067008 prefixEnd_2067008 := by exact prefixLift 2067008
  have htrace : WordTrace (prefixWord ++ tailWord_2067008) baseStart_2067008 baseEnd_2067008 := by
    simpa [prefixWord, tailWord_2067008, baseEnd_2067008] using wordTrace_append hprefix tailTrace_2067008
  have hstable : (prefixWord ++ tailWord_2067008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067008).length < 2 ^ (prefixWord ++ tailWord_2067008).sum := by decide
  have hdescent : baseEnd_2067008 < baseStart_2067008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067052 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 5]
def baseStart_2067052 : Nat := 118140960795 + 2067052 * 2 ^ 59
def prefixEnd_2067052 : Nat := 4983230072969 + 3 ^ 40 * 2067052 * 2
def baseEnd_2067052 : Nat := 117932357093061320360423

theorem tailTrace_2067052 : CollatzResearch.WordTrace tailWord_2067052 prefixEnd_2067052 117932357093061320360423 := by
  unfold tailWord_2067052
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695790053715551610501705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50261053404954068814002273 37695790053715551610501705)
  ·
    refine ⟨28271842540286663707876279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37695790053715551610501705 28271842540286663707876279)
    ·
      refine ⟨42407763810429995561814419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28271842540286663707876279 42407763810429995561814419)
      ·
        refine ⟨63611645715644993342721629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42407763810429995561814419 63611645715644993342721629)
        ·
          refine ⟨23854367143366872503520611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63611645715644993342721629 23854367143366872503520611)
          ·
            refine ⟨35781550715050308755280917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23854367143366872503520611 35781550715050308755280917)
            ·
              refine ⟨1677260189767983222903793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35781550715050308755280917 1677260189767983222903793)
              ·
                refine ⟨1257945142325987417177845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677260189767983222903793 1257945142325987417177845)
                ·
                  refine ⟨117932357093061320360423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1257945142325987417177845 117932357093061320360423)
                  ·
                    rfl

theorem cell23_2067052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_2067052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067052 prefixEnd_2067052 := by exact prefixLift 2067052
  have htrace : WordTrace (prefixWord ++ tailWord_2067052) baseStart_2067052 baseEnd_2067052 := by
    simpa [prefixWord, tailWord_2067052, baseEnd_2067052] using wordTrace_append hprefix tailTrace_2067052
  have hstable : (prefixWord ++ tailWord_2067052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067052).length < 2 ^ (prefixWord ++ tailWord_2067052).sum := by decide
  have hdescent : baseEnd_2067052 < baseStart_2067052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067055 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 2, 5, 2]
def baseStart_2067055 : Nat := 118140960795 + 2067055 * 2 ^ 59
def prefixEnd_2067055 : Nat := 4983230072969 + 3 ^ 40 * 2067055 * 2
def baseEnd_2067055 : Nat := 1061392754279515371506293

theorem tailTrace_2067055 : CollatzResearch.WordTrace tailWord_2067055 prefixEnd_2067055 1061392754279515371506293 := by
  unfold tailWord_2067055
  simp only [CollatzResearch.WordTrace]
  refine ⟨75391689526420234733362619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50261126350946823155575079 75391689526420234733362619)
  ·
    refine ⟨113087534289630352100043929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75391689526420234733362619 113087534289630352100043929)
    ·
      refine ⟨84815650717222764075032947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113087534289630352100043929 84815650717222764075032947)
      ·
        refine ⟨127223476075834146112549421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84815650717222764075032947 127223476075834146112549421)
        ·
          refine ⟨47708803528437804792206033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127223476075834146112549421 47708803528437804792206033)
          ·
            refine ⟨35781602646328353594154525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47708803528437804792206033 35781602646328353594154525)
            ·
              refine ⟨13418100992373132597807947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35781602646328353594154525 13418100992373132597807947)
              ·
                refine ⟨20127151488559698896711921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13418100992373132597807947 20127151488559698896711921)
                ·
                  refine ⟨15095363616419774172533941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20127151488559698896711921 15095363616419774172533941)
                  ·
                    refine ⟨1415190339039353828675057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15095363616419774172533941 1415190339039353828675057)
                    ·
                      refine ⟨1061392754279515371506293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415190339039353828675057 1061392754279515371506293)
                      ·
                        rfl

theorem cell23_2067055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 5, 2].length) (baseStart_2067055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067055 prefixEnd_2067055 := by exact prefixLift 2067055
  have htrace : WordTrace (prefixWord ++ tailWord_2067055) baseStart_2067055 baseEnd_2067055 := by
    simpa [prefixWord, tailWord_2067055, baseEnd_2067055] using wordTrace_append hprefix tailTrace_2067055
  have hstable : (prefixWord ++ tailWord_2067055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067055).length < 2 ^ (prefixWord ++ tailWord_2067055).sum := by decide
  have hdescent : baseEnd_2067055 < baseStart_2067055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067095 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 5, 4]
def baseStart_2067095 : Nat := 118140960795 + 2067095 * 2 ^ 59
def prefixEnd_2067095 : Nat := 4983230072969 + 3 ^ 40 * 2067095 * 2
def baseEnd_2067095 : Nat := 353804431168565071668703

theorem tailTrace_2067095 : CollatzResearch.WordTrace tailWord_2067095 prefixEnd_2067095 353804431168565071668703 := by
  unfold tailWord_2067095
  simp only [CollatzResearch.WordTrace]
  refine ⟨75393148446275321564818739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50262098964183547709879159 75393148446275321564818739)
  ·
    refine ⟨113089722669412982347228109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75393148446275321564818739 113089722669412982347228109)
    ·
      refine ⟨42408646001029868380210541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113089722669412982347228109 42408646001029868380210541)
      ·
        refine ⟨15903242250386200642578953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42408646001029868380210541 15903242250386200642578953)
        ·
          refine ⟨11927431687789650481934215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15903242250386200642578953 11927431687789650481934215)
          ·
            refine ⟨17891147531684475722901323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927431687789650481934215 17891147531684475722901323)
            ·
              refine ⟨26836721297526713584351985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891147531684475722901323 26836721297526713584351985)
              ·
                refine ⟨20127540973145035188263989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26836721297526713584351985 20127540973145035188263989)
                ·
                  refine ⟨1886956966232347048899749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20127540973145035188263989 1886956966232347048899749)
                  ·
                    refine ⟨353804431168565071668703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886956966232347048899749 353804431168565071668703)
                    ·
                      rfl

theorem cell23_2067095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_2067095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067095 prefixEnd_2067095 := by exact prefixLift 2067095
  have htrace : WordTrace (prefixWord ++ tailWord_2067095) baseStart_2067095 baseEnd_2067095 := by
    simpa [prefixWord, tailWord_2067095, baseEnd_2067095] using wordTrace_append hprefix tailTrace_2067095
  have hstable : (prefixWord ++ tailWord_2067095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067095).length < 2 ^ (prefixWord ++ tailWord_2067095).sum := by decide
  have hdescent : baseEnd_2067095 < baseStart_2067095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067102 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2067102 : Nat := 118140960795 + 2067102 * 2 ^ 59
def prefixEnd_2067102 : Nat := 4983230072969 + 3 ^ 40 * 2067102 * 2
def baseEnd_2067102 : Nat := 1061416887870276687618577

theorem tailTrace_2067102 : CollatzResearch.WordTrace tailWord_2067102 prefixEnd_2067102 1061416887870276687618577 := by
  unfold tailWord_2067102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9424175469656245220040445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50262269171499974506882373 9424175469656245220040445)
  ·
    refine ⟨3534065801121091957515167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9424175469656245220040445 3534065801121091957515167)
    ·
      refine ⟨5301098701681637936272751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534065801121091957515167 5301098701681637936272751)
      ·
        refine ⟨7951648052522456904409127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5301098701681637936272751 7951648052522456904409127)
        ·
          refine ⟨11927472078783685356613691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951648052522456904409127 11927472078783685356613691)
          ·
            refine ⟨17891208118175528034920537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927472078783685356613691 17891208118175528034920537)
            ·
              refine ⟨13418406088631646026190403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17891208118175528034920537 13418406088631646026190403)
              ·
                refine ⟨20127609132947469039285605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13418406088631646026190403 20127609132947469039285605)
                ·
                  refine ⟨3773926712427650444866051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20127609132947469039285605 3773926712427650444866051)
                  ·
                    refine ⟨5660890068641475667299077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3773926712427650444866051 5660890068641475667299077)
                    ·
                      refine ⟨1061416887870276687618577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5660890068641475667299077 1061416887870276687618577)
                      ·
                        rfl

theorem cell23_2067102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2067102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067102 prefixEnd_2067102 := by exact prefixLift 2067102
  have htrace : WordTrace (prefixWord ++ tailWord_2067102) baseStart_2067102 baseEnd_2067102 := by
    simpa [prefixWord, tailWord_2067102, baseEnd_2067102] using wordTrace_append hprefix tailTrace_2067102
  have hstable : (prefixWord ++ tailWord_2067102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067102).length < 2 ^ (prefixWord ++ tailWord_2067102).sum := by decide
  have hdescent : baseEnd_2067102 < baseStart_2067102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067146 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_2067146 : Nat := 118140960795 + 2067146 * 2 ^ 59
def prefixEnd_2067146 : Nat := 4983230072969 + 3 ^ 40 * 2067146 * 2
def baseEnd_2067146 : Nat := 353813160339691505156125

theorem tailTrace_2067146 : CollatzResearch.WordTrace tailWord_2067146 prefixEnd_2067146 353813160339691505156125 := by
  unfold tailWord_2067146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18848752142272639318731323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50263339046060371516616861 18848752142272639318731323)
  ·
    refine ⟨28273128213408958978096985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18848752142272639318731323 28273128213408958978096985)
    ·
      refine ⟨21204846160056719233572739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28273128213408958978096985 21204846160056719233572739)
      ·
        refine ⟨31807269240085078850359109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21204846160056719233572739 31807269240085078850359109)
        ·
          refine ⟨5963862982515952284442333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31807269240085078850359109 5963862982515952284442333)
          ·
            refine ⟨2236448618443482106665875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5963862982515952284442333 2236448618443482106665875)
            ·
              refine ⟨3354672927665223159998813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236448618443482106665875 3354672927665223159998813)
              ·
                refine ⟨1258002347874458684999555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3354672927665223159998813 1258002347874458684999555)
                ·
                  refine ⟨1887003521811688027499333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258002347874458684999555 1887003521811688027499333)
                  ·
                    refine ⟨353813160339691505156125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1887003521811688027499333 353813160339691505156125)
                    ·
                      rfl

theorem cell23_2067146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_2067146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067146 prefixEnd_2067146 := by exact prefixLift 2067146
  have htrace : WordTrace (prefixWord ++ tailWord_2067146) baseStart_2067146 baseEnd_2067146 := by
    simpa [prefixWord, tailWord_2067146, baseEnd_2067146] using wordTrace_append hprefix tailTrace_2067146
  have hstable : (prefixWord ++ tailWord_2067146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067146).length < 2 ^ (prefixWord ++ tailWord_2067146).sum := by decide
  have hdescent : baseEnd_2067146 < baseStart_2067146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067169 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_2067169 : Nat := 118140960795 + 2067169 * 2 ^ 59
def prefixEnd_2067169 : Nat := 4983230072969 + 3 ^ 40 * 2067169 * 2
def baseEnd_2067169 : Nat := 1061451291074127925480769

theorem tailTrace_2067169 : CollatzResearch.WordTrace tailWord_2067169 prefixEnd_2067169 1061451291074127925480769 := by
  unfold tailWord_2067169
  simp only [CollatzResearch.WordTrace]
  refine ⟨75395847448007232203012561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50263898298671488135341707 75395847448007232203012561)
  ·
    refine ⟨56546885586005424152259421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75395847448007232203012561 56546885586005424152259421)
    ·
      refine ⟨21205082094752034057097283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56546885586005424152259421 21205082094752034057097283)
      ·
        refine ⟨31807623142128051085645925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21205082094752034057097283 31807623142128051085645925)
        ·
          refine ⟨5963929339149009578558611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31807623142128051085645925 5963929339149009578558611)
          ·
            refine ⟨8945894008723514367837917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963929339149009578558611 8945894008723514367837917)
            ·
              refine ⟨3354710253271317887939219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8945894008723514367837917 3354710253271317887939219)
              ·
                refine ⟨5032065379906976831908829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354710253271317887939219 5032065379906976831908829)
                ·
                  refine ⟨1887024517465116311965811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5032065379906976831908829 1887024517465116311965811)
                  ·
                    refine ⟨2830536776197674467948717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1887024517465116311965811 2830536776197674467948717)
                    ·
                      refine ⟨1061451291074127925480769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2830536776197674467948717 1061451291074127925480769)
                      ·
                        rfl

theorem cell23_2067169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_2067169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067169 prefixEnd_2067169 := by exact prefixLift 2067169
  have htrace : WordTrace (prefixWord ++ tailWord_2067169) baseStart_2067169 baseEnd_2067169 := by
    simpa [prefixWord, tailWord_2067169, baseEnd_2067169] using wordTrace_append hprefix tailTrace_2067169
  have hstable : (prefixWord ++ tailWord_2067169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067169).length < 2 ^ (prefixWord ++ tailWord_2067169).sum := by decide
  have hdescent : baseEnd_2067169 < baseStart_2067169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067176 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 6]
def baseStart_2067176 : Nat := 118140960795 + 2067176 * 2 ^ 59
def prefixEnd_2067176 : Nat := 4983230072969 + 3 ^ 40 * 2067176 * 2
def baseEnd_2067176 : Nat := 117939431715412155343693

theorem tailTrace_2067176 : CollatzResearch.WordTrace tailWord_2067176 prefixEnd_2067176 117939431715412155343693 := by
  unfold tailWord_2067176
  simp only [CollatzResearch.WordTrace]
  refine ⟨37698051379490936199258691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50264068505987914932344921 37698051379490936199258691)
  ·
    refine ⟨56547077069236404298888037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37698051379490936199258691 56547077069236404298888037)
    ·
      refine ⟨10602576950481825806041507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56547077069236404298888037 10602576950481825806041507)
      ·
        refine ⟨15903865425722738709062261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10602576950481825806041507 15903865425722738709062261)
        ·
          refine ⟨1490987383661506753974587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15903865425722738709062261 1490987383661506753974587)
          ·
            refine ⟨2236481075492260130961881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490987383661506753974587 2236481075492260130961881)
            ·
              refine ⟨1677360806619195098221411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236481075492260130961881 1677360806619195098221411)
              ·
                refine ⟨2516041209928792647332117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677360806619195098221411 2516041209928792647332117)
                ·
                  refine ⟨117939431715412155343693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2516041209928792647332117 117939431715412155343693)
                  ·
                    rfl

theorem cell23_2067176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 6].length) (baseStart_2067176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067176 prefixEnd_2067176 := by exact prefixLift 2067176
  have htrace : WordTrace (prefixWord ++ tailWord_2067176) baseStart_2067176 baseEnd_2067176 := by
    simpa [prefixWord, tailWord_2067176, baseEnd_2067176] using wordTrace_append hprefix tailTrace_2067176
  have hstable : (prefixWord ++ tailWord_2067176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067176).length < 2 ^ (prefixWord ++ tailWord_2067176).sum := by decide
  have hdescent : baseEnd_2067176 < baseStart_2067176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067185 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_2067185 : Nat := 118140960795 + 2067185 * 2 ^ 59
def prefixEnd_2067185 : Nat := 4983230072969 + 3 ^ 40 * 2067185 * 2
def baseEnd_2067185 : Nat := 353819835588199954293565

theorem tailTrace_2067185 : CollatzResearch.WordTrace tailWord_2067185 prefixEnd_2067185 353819835588199954293565 := by
  unfold tailWord_2067185
  simp only [CollatzResearch.WordTrace]
  refine ⟨75396431015949266935595009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50264287343966177957063339 75396431015949266935595009)
  ·
    refine ⟨56547323261961950201696257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75396431015949266935595009 56547323261961950201696257)
    ·
      refine ⟨42410492446471462651272193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56547323261961950201696257 42410492446471462651272193)
      ·
        refine ⟨31807869334853596988454145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42410492446471462651272193 31807869334853596988454145)
        ·
          refine ⟨23855902001140197741340609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31807869334853596988454145 23855902001140197741340609)
          ·
            refine ⟨17891926500855148306005457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23855902001140197741340609 17891926500855148306005457)
            ·
              refine ⟨13418944875641361229504093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17891926500855148306005457 13418944875641361229504093)
              ·
                refine ⟨5032104328365510461064035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13418944875641361229504093 5032104328365510461064035)
                ·
                  refine ⟨7548156492548265691596053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032104328365510461064035 7548156492548265691596053)
                  ·
                    refine ⟨353819835588199954293565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7548156492548265691596053 353819835588199954293565)
                    ·
                      rfl

theorem cell23_2067185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_2067185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067185 prefixEnd_2067185 := by exact prefixLift 2067185
  have htrace : WordTrace (prefixWord ++ tailWord_2067185) baseStart_2067185 baseEnd_2067185 := by
    simpa [prefixWord, tailWord_2067185, baseEnd_2067185] using wordTrace_append hprefix tailTrace_2067185
  have hstable : (prefixWord ++ tailWord_2067185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067185).length < 2 ^ (prefixWord ++ tailWord_2067185).sum := by decide
  have hdescent : baseEnd_2067185 < baseStart_2067185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067202 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2067202 : Nat := 118140960795 + 2067202 * 2 ^ 59
def prefixEnd_2067202 : Nat := 4983230072969 + 3 ^ 40 * 2067202 * 2
def baseEnd_2067202 : Nat := 353822745311908765456039

theorem tailTrace_2067202 : CollatzResearch.WordTrace tailWord_2067202 prefixEnd_2067202 353822745311908765456039 := by
  unfold tailWord_2067202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849262764221919709740965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50264700704591785892642573 18849262764221919709740965)
  ·
    refine ⟨3534236768291609945576431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18849262764221919709740965 3534236768291609945576431)
    ·
      refine ⟨5301355152437414918364647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534236768291609945576431 5301355152437414918364647)
      ·
        refine ⟨7952032728656122377546971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5301355152437414918364647 7952032728656122377546971)
        ·
          refine ⟨11928049092984183566320457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7952032728656122377546971 11928049092984183566320457)
          ·
            refine ⟨8946036819738137674740343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11928049092984183566320457 8946036819738137674740343)
            ·
              refine ⟨13419055229607206512110515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946036819738137674740343 13419055229607206512110515)
              ·
                refine ⟨20128582844410809768165773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13419055229607206512110515 20128582844410809768165773)
                ·
                  refine ⟨7548218566654053663062165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20128582844410809768165773 7548218566654053663062165)
                  ·
                    refine ⟨353822745311908765456039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7548218566654053663062165 353822745311908765456039)
                    ·
                      rfl

theorem cell23_2067202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2067202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067202 prefixEnd_2067202 := by exact prefixLift 2067202
  have htrace : WordTrace (prefixWord ++ tailWord_2067202) baseStart_2067202 baseEnd_2067202 := by
    simpa [prefixWord, tailWord_2067202, baseEnd_2067202] using wordTrace_append hprefix tailTrace_2067202
  have hstable : (prefixWord ++ tailWord_2067202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067202).length < 2 ^ (prefixWord ++ tailWord_2067202).sum := by decide
  have hdescent : baseEnd_2067202 < baseStart_2067202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067232 : List Nat := [2, 1, 1, 5, 1, 4, 1, 8]
def baseStart_2067232 : Nat := 118140960795 + 2067232 * 2 ^ 59
def prefixEnd_2067232 : Nat := 4983230072969 + 3 ^ 40 * 2067232 * 2
def baseEnd_2067232 : Nat := 39314208902050414036777

theorem tailTrace_2067232 : CollatzResearch.WordTrace tailWord_2067232 prefixEnd_2067232 39314208902050414036777 := by
  unfold tailWord_2067232
  simp only [CollatzResearch.WordTrace]
  refine ⟨37699072623389496981277975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50265430164519329308370633 37699072623389496981277975)
  ·
    refine ⟨56548608935084245471916963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37699072623389496981277975 56548608935084245471916963)
    ·
      refine ⟨84822913402626368207875445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56548608935084245471916963 84822913402626368207875445)
      ·
        refine ⟨7952148131496222019488323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84822913402626368207875445 7952148131496222019488323)
        ·
          refine ⟨11928222197244333029232485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7952148131496222019488323 11928222197244333029232485)
          ·
            refine ⟨2236541661983312442981091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11928222197244333029232485 2236541661983312442981091)
            ·
              refine ⟨3354812492974968664471637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236541661983312442981091 3354812492974968664471637)
              ·
                refine ⟨39314208902050414036777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3354812492974968664471637 39314208902050414036777)
                ·
                  rfl

theorem cell23_2067232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 8].length) (baseStart_2067232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067232 prefixEnd_2067232 := by exact prefixLift 2067232
  have htrace : WordTrace (prefixWord ++ tailWord_2067232) baseStart_2067232 baseEnd_2067232 := by
    simpa [prefixWord, tailWord_2067232, baseEnd_2067232] using wordTrace_append hprefix tailTrace_2067232
  have hstable : (prefixWord ++ tailWord_2067232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067232).length < 2 ^ (prefixWord ++ tailWord_2067232).sum := by decide
  have hdescent : baseEnd_2067232 < baseStart_2067232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067255 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_2067255 : Nat := 118140960795 + 2067255 * 2 ^ 59
def prefixEnd_2067255 : Nat := 4983230072969 + 3 ^ 40 * 2067255 * 2
def baseEnd_2067255 : Nat := 1061495450410414589005373

theorem tailTrace_2067255 : CollatzResearch.WordTrace tailWord_2067255 prefixEnd_2067255 1061495450410414589005373 := by
  unfold tailWord_2067255
  simp only [CollatzResearch.WordTrace]
  refine ⟨75398984125695668890643219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50265989417130445927095479 75398984125695668890643219)
  ·
    refine ⟨113098476188543503335964829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75398984125695668890643219 113098476188543503335964829)
    ·
      refine ⟨42411928570703813750986811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113098476188543503335964829 42411928570703813750986811)
      ·
        refine ⟨63617892856055720626480217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42411928570703813750986811 63617892856055720626480217)
        ·
          refine ⟨47713419642041790469860163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63617892856055720626480217 47713419642041790469860163)
          ·
            refine ⟨71570129463062685704790245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47713419642041790469860163 71570129463062685704790245)
            ·
              refine ⟨13419399274324253569648171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71570129463062685704790245 13419399274324253569648171)
              ·
                refine ⟨20129098911486380354472257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13419399274324253569648171 20129098911486380354472257)
                ·
                  refine ⟨15096824183614785265854193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20129098911486380354472257 15096824183614785265854193)
                  ·
                    refine ⟨11322618137711088949390645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15096824183614785265854193 11322618137711088949390645)
                    ·
                      refine ⟨1061495450410414589005373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11322618137711088949390645 1061495450410414589005373)
                      ·
                        rfl

theorem cell23_2067255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_2067255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067255 prefixEnd_2067255 := by exact prefixLift 2067255
  have htrace : WordTrace (prefixWord ++ tailWord_2067255) baseStart_2067255 baseEnd_2067255 := by
    simpa [prefixWord, tailWord_2067255, baseEnd_2067255] using wordTrace_append hprefix tailTrace_2067255
  have hstable : (prefixWord ++ tailWord_2067255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067255).length < 2 ^ (prefixWord ++ tailWord_2067255).sum := by decide
  have hdescent : baseEnd_2067255 < baseStart_2067255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067270 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2067270 : Nat := 118140960795 + 2067270 * 2 ^ 59
def prefixEnd_2067270 : Nat := 4983230072969 + 3 ^ 40 * 2067270 * 2
def baseEnd_2067270 : Nat := 353834384206744010105935

theorem tailTrace_2067270 : CollatzResearch.WordTrace tailWord_2067270 prefixEnd_2067270 353834384206744010105935 := by
  unfold tailWord_2067270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2356235350645041451638727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50266354147094217634959509 2356235350645041451638727)
  ·
    refine ⟨3534353025967562177458091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2356235350645041451638727 3534353025967562177458091)
    ·
      refine ⟨5301529538951343266187137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534353025967562177458091 5301529538951343266187137)
      ·
        refine ⟨3976147154213507449640353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5301529538951343266187137 3976147154213507449640353)
        ·
          refine ⟨2982110365660130587230265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976147154213507449640353 2982110365660130587230265)
          ·
            refine ⟨2236582774245097940422699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2982110365660130587230265 2236582774245097940422699)
            ·
              refine ⟨3354874161367646910634049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236582774245097940422699 3354874161367646910634049)
              ·
                refine ⟨2516155621025735182975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354874161367646910634049 2516155621025735182975537)
                ·
                  refine ⟨1887116715769301387231653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516155621025735182975537 1887116715769301387231653)
                  ·
                    refine ⟨353834384206744010105935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1887116715769301387231653 353834384206744010105935)
                    ·
                      rfl

theorem cell23_2067270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2067270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067270 prefixEnd_2067270 := by exact prefixLift 2067270
  have htrace : WordTrace (prefixWord ++ tailWord_2067270) baseStart_2067270 baseEnd_2067270 := by
    simpa [prefixWord, tailWord_2067270, baseEnd_2067270] using wordTrace_append hprefix tailTrace_2067270
  have hstable : (prefixWord ++ tailWord_2067270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067270).length < 2 ^ (prefixWord ++ tailWord_2067270).sum := by decide
  have hdescent : baseEnd_2067270 < baseStart_2067270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067276 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2067276 : Nat := 118140960795 + 2067276 * 2 ^ 59
def prefixEnd_2067276 : Nat := 4983230072969 + 3 ^ 40 * 2067276 * 2
def baseEnd_2067276 : Nat := 1061506233504159006842777

theorem tailTrace_2067276 : CollatzResearch.WordTrace tailWord_2067276 prefixEnd_2067276 1061506233504159006842777 := by
  unfold tailWord_2067276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37699875029309794738578841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50266500039079726318105121 37699875029309794738578841)
  ·
    refine ⟨28274906271982346053934131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37699875029309794738578841 28274906271982346053934131)
    ·
      refine ⟨42412359407973519080901197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28274906271982346053934131 42412359407973519080901197)
      ·
        refine ⟨15904634777990069655337949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42412359407973519080901197 15904634777990069655337949)
        ·
          refine ⟨5964238041746276120751731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15904634777990069655337949 5964238041746276120751731)
          ·
            refine ⟨8946357062619414181127597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964238041746276120751731 8946357062619414181127597)
            ·
              refine ⟨3354883898482280317922849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8946357062619414181127597 3354883898482280317922849)
              ·
                refine ⟨2516162923861710238442137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354883898482280317922849 2516162923861710238442137)
                ·
                  refine ⟨1887122192896282678831603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516162923861710238442137 1887122192896282678831603)
                  ·
                    refine ⟨2830683289344424018247405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1887122192896282678831603 2830683289344424018247405)
                    ·
                      refine ⟨1061506233504159006842777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2830683289344424018247405 1061506233504159006842777)
                      ·
                        rfl

theorem cell23_2067276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2067276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067276 prefixEnd_2067276 := by exact prefixLift 2067276
  have htrace : WordTrace (prefixWord ++ tailWord_2067276) baseStart_2067276 baseEnd_2067276 := by
    simpa [prefixWord, tailWord_2067276, baseEnd_2067276] using wordTrace_append hprefix tailTrace_2067276
  have hstable : (prefixWord ++ tailWord_2067276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067276).length < 2 ^ (prefixWord ++ tailWord_2067276).sum := by decide
  have hdescent : baseEnd_2067276 < baseStart_2067276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067372 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_2067372 : Nat := 118140960795 + 2067372 * 2 ^ 59
def prefixEnd_2067372 : Nat := 4983230072969 + 3 ^ 40 * 2067372 * 2
def baseEnd_2067372 : Nat := 1061555527646990631242335

theorem tailTrace_2067372 : CollatzResearch.WordTrace tailWord_2067372 prefixEnd_2067372 1061555527646990631242335 := by
  unfold tailWord_2067372
  simp only [CollatzResearch.WordTrace]
  refine ⟨37701625733135898936326185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50268834310847865248434913 37701625733135898936326185)
  ·
    refine ⟨28276219299851924202244639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37701625733135898936326185 28276219299851924202244639)
    ·
      refine ⟨42414328949777886303366959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28276219299851924202244639 42414328949777886303366959)
      ·
        refine ⟨63621493424666829455050439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42414328949777886303366959 63621493424666829455050439)
        ·
          refine ⟨95432240137000244182575659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63621493424666829455050439 95432240137000244182575659)
          ·
            refine ⟨143148360205500366273863489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95432240137000244182575659 143148360205500366273863489)
            ·
              refine ⟨107361270154125274705397617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143148360205500366273863489 107361270154125274705397617)
              ·
                refine ⟨80520952615593956029048213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107361270154125274705397617 80520952615593956029048213)
                ·
                  refine ⟨3774419653855966688861635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80520952615593956029048213 3774419653855966688861635)
                  ·
                    refine ⟨5661629480783950033292453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774419653855966688861635 5661629480783950033292453)
                    ·
                      refine ⟨1061555527646990631242335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5661629480783950033292453 1061555527646990631242335)
                      ·
                        rfl

theorem cell23_2067372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_2067372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067372 prefixEnd_2067372 := by exact prefixLift 2067372
  have htrace : WordTrace (prefixWord ++ tailWord_2067372) baseStart_2067372 baseEnd_2067372 := by
    simpa [prefixWord, tailWord_2067372, baseEnd_2067372] using wordTrace_append hprefix tailTrace_2067372
  have hstable : (prefixWord ++ tailWord_2067372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067372).length < 2 ^ (prefixWord ++ tailWord_2067372).sum := by decide
  have hdescent : baseEnd_2067372 < baseStart_2067372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067402 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2067402 : Nat := 118140960795 + 2067402 * 2 ^ 59
def prefixEnd_2067402 : Nat := 4983230072969 + 3 ^ 40 * 2067402 * 2
def baseEnd_2067402 : Nat := 1061570932066625513867197

theorem tailTrace_2067402 : CollatzResearch.WordTrace tailWord_2067402 prefixEnd_2067402 1061570932066625513867197 := by
  unfold tailWord_2067402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18851086414040778249061115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50269563770775408664162973 18851086414040778249061115)
  ·
    refine ⟨28276629621061167373591673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18851086414040778249061115 28276629621061167373591673)
    ·
      refine ⟨21207472215795875530193755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28276629621061167373591673 21207472215795875530193755)
      ·
        refine ⟨31811208323693813295290633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21207472215795875530193755 31811208323693813295290633)
        ·
          refine ⟨23858406242770359971467975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31811208323693813295290633 23858406242770359971467975)
          ·
            refine ⟨35787609364155539957201963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23858406242770359971467975 35787609364155539957201963)
            ·
              refine ⟨53681414046233309935802945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35787609364155539957201963 53681414046233309935802945)
              ·
                refine ⟨40261060534674982451852209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53681414046233309935802945 40261060534674982451852209)
                ·
                  refine ⟨30195795401006236838889157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40261060534674982451852209 30195795401006236838889157)
                  ·
                    refine ⟨5661711637688669407291717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30195795401006236838889157 5661711637688669407291717)
                    ·
                      refine ⟨1061570932066625513867197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5661711637688669407291717 1061570932066625513867197)
                      ·
                        rfl

theorem cell23_2067402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2067402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067402 prefixEnd_2067402 := by exact prefixLift 2067402
  have htrace : WordTrace (prefixWord ++ tailWord_2067402) baseStart_2067402 baseEnd_2067402 := by
    simpa [prefixWord, tailWord_2067402, baseEnd_2067402] using wordTrace_append hprefix tailTrace_2067402
  have hstable : (prefixWord ++ tailWord_2067402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067402).length < 2 ^ (prefixWord ++ tailWord_2067402).sum := by decide
  have hdescent : baseEnd_2067402 < baseStart_2067402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067406 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_2067406 : Nat := 118140960795 + 2067406 * 2 ^ 59
def prefixEnd_2067406 : Nat := 4983230072969 + 3 ^ 40 * 2067406 * 2
def baseEnd_2067406 : Nat := 1061572985989243498217179

theorem tailTrace_2067406 : CollatzResearch.WordTrace tailWord_2067406 prefixEnd_2067406 1061572985989243498217179 := by
  unfold tailWord_2067406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425561443518577709923759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50269661032099081119593381 9425561443518577709923759)
  ·
    refine ⟨14138342165277866564885639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9425561443518577709923759 14138342165277866564885639)
    ·
      refine ⟨21207513247916799847328459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14138342165277866564885639 21207513247916799847328459)
      ·
        refine ⟨31811269871875199770992689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21207513247916799847328459 31811269871875199770992689)
        ·
          refine ⟨23858452403906399828244517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31811269871875199770992689 23858452403906399828244517)
          ·
            refine ⟨4473459825732449967795847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23858452403906399828244517 4473459825732449967795847)
            ·
              refine ⟨6710189738598674951693771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473459825732449967795847 6710189738598674951693771)
              ·
                refine ⟨10065284607898012427540657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710189738598674951693771 10065284607898012427540657)
                ·
                  refine ⟨7548963455923509320655493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10065284607898012427540657 7548963455923509320655493)
                  ·
                    refine ⟨1415430647985657997622905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548963455923509320655493 1415430647985657997622905)
                    ·
                      refine ⟨1061572985989243498217179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415430647985657997622905 1061572985989243498217179)
                      ·
                        rfl

theorem cell23_2067406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_2067406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067406 prefixEnd_2067406 := by exact prefixLift 2067406
  have htrace : WordTrace (prefixWord ++ tailWord_2067406) baseStart_2067406 baseEnd_2067406 := by
    simpa [prefixWord, tailWord_2067406, baseEnd_2067406] using wordTrace_append hprefix tailTrace_2067406
  have hstable : (prefixWord ++ tailWord_2067406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067406).length < 2 ^ (prefixWord ++ tailWord_2067406).sum := by decide
  have hdescent : baseEnd_2067406 < baseStart_2067406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067423 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 2, 1, 4]
def baseStart_2067423 : Nat := 118140960795 + 2067423 * 2 ^ 59
def prefixEnd_2067423 : Nat := 4983230072969 + 3 ^ 40 * 2067423 * 2
def baseEnd_2067423 : Nat := 1061581715160369931704601

theorem tailTrace_2067423 : CollatzResearch.WordTrace tailWord_2067423 prefixEnd_2067423 1061581715160369931704601 := by
  unfold tailWord_2067423
  simp only [CollatzResearch.WordTrace]
  refine ⟨75405111589087033582758923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50270074392724689055172615 75405111589087033582758923)
  ·
    refine ⟨113107667383630550374138385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75405111589087033582758923 113107667383630550374138385)
    ·
      refine ⟨84830750537722912780603789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113107667383630550374138385 84830750537722912780603789)
      ·
        refine ⟨31811531451646092292726421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84830750537722912780603789 31811531451646092292726421)
        ·
          refine ⟨1491165536795910576221551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31811531451646092292726421 1491165536795910576221551)
          ·
            refine ⟨2236748305193865864332327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491165536795910576221551 2236748305193865864332327)
            ·
              refine ⟨3355122457790798796498491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236748305193865864332327 3355122457790798796498491)
              ·
                refine ⟨5032683686686198194747737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355122457790798796498491 5032683686686198194747737)
                ·
                  refine ⟨3774512765014648646060803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032683686686198194747737 3774512765014648646060803)
                  ·
                    refine ⟨5661769147521972969091205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3774512765014648646060803 5661769147521972969091205)
                    ·
                      refine ⟨1061581715160369931704601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5661769147521972969091205 1061581715160369931704601)
                      ·
                        rfl

theorem cell23_2067423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_2067423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067423 prefixEnd_2067423 := by exact prefixLift 2067423
  have htrace : WordTrace (prefixWord ++ tailWord_2067423) baseStart_2067423 baseEnd_2067423 := by
    simpa [prefixWord, tailWord_2067423, baseEnd_2067423] using wordTrace_append hprefix tailTrace_2067423
  have hstable : (prefixWord ++ tailWord_2067423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067423).length < 2 ^ (prefixWord ++ tailWord_2067423).sum := by decide
  have hdescent : baseEnd_2067423 < baseStart_2067423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067446 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_2067446 : Nat := 118140960795 + 2067446 * 2 ^ 59
def prefixEnd_2067446 : Nat := 4983230072969 + 3 ^ 40 * 2067446 * 2
def baseEnd_2067446 : Nat := 117954836135047037968555

theorem tailTrace_2067446 : CollatzResearch.WordTrace tailWord_2067446 prefixEnd_2067446 117954836135047037968555 := by
  unfold tailWord_2067446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712871904250231781927887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50270633645335805673897461 4712871904250231781927887)
  ·
    refine ⟨7069307856375347672891831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4712871904250231781927887 7069307856375347672891831)
    ·
      refine ⟨10603961784563021509337747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7069307856375347672891831 10603961784563021509337747)
      ·
        refine ⟨15905942676844532264006621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10603961784563021509337747 15905942676844532264006621)
        ·
          refine ⟨5964728503816699599002483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15905942676844532264006621 5964728503816699599002483)
          ·
            refine ⟨8947092755725049398503725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964728503816699599002483 8947092755725049398503725)
            ·
              refine ⟨3355159783396893524438897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947092755725049398503725 3355159783396893524438897)
              ·
                refine ⟨2516369837547670143329173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3355159783396893524438897 2516369837547670143329173)
                ·
                  refine ⟨117954836135047037968555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2516369837547670143329173 117954836135047037968555)
                  ·
                    rfl

theorem cell23_2067446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_2067446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067446 prefixEnd_2067446 := by exact prefixLift 2067446
  have htrace : WordTrace (prefixWord ++ tailWord_2067446) baseStart_2067446 baseEnd_2067446 := by
    simpa [prefixWord, tailWord_2067446, baseEnd_2067446] using wordTrace_append hprefix tailTrace_2067446
  have hstable : (prefixWord ++ tailWord_2067446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067446).length < 2 ^ (prefixWord ++ tailWord_2067446).sum := by decide
  have hdescent : baseEnd_2067446 < baseStart_2067446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067466 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_2067466 : Nat := 118140960795 + 2067466 * 2 ^ 59
def prefixEnd_2067466 : Nat := 4983230072969 + 3 ^ 40 * 2067466 * 2
def baseEnd_2067466 : Nat := 1061603794828513263466903

theorem tailTrace_2067466 : CollatzResearch.WordTrace tailWord_2067466 prefixEnd_2067466 1061603794828513263466903 := by
  unfold tailWord_2067466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18851669981982812981643563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50271119951954167951049501 18851669981982812981643563)
  ·
    refine ⟨28277504972974219472465345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18851669981982812981643563 28277504972974219472465345)
    ·
      refine ⟨21208128729730664604349009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28277504972974219472465345 21208128729730664604349009)
      ·
        refine ⟨15906096547297998453261757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21208128729730664604349009 15906096547297998453261757)
        ·
          refine ⟨5964786205236749419973159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15906096547297998453261757 5964786205236749419973159)
          ·
            refine ⟨8947179307855124129959739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964786205236749419973159 8947179307855124129959739)
            ·
              refine ⟨13420768961782686194939609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947179307855124129959739 13420768961782686194939609)
              ·
                refine ⟨10065576721337014646204707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13420768961782686194939609 10065576721337014646204707)
                ·
                  refine ⟨15098365082005521969307061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10065576721337014646204707 15098365082005521969307061)
                  ·
                    refine ⟨1415471726438017684622537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15098365082005521969307061 1415471726438017684622537)
                    ·
                      refine ⟨1061603794828513263466903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415471726438017684622537 1061603794828513263466903)
                      ·
                        rfl

theorem cell23_2067466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_2067466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067466 prefixEnd_2067466 := by exact prefixLift 2067466
  have htrace : WordTrace (prefixWord ++ tailWord_2067466) baseStart_2067466 baseEnd_2067466 := by
    simpa [prefixWord, tailWord_2067466, baseEnd_2067466] using wordTrace_append hprefix tailTrace_2067466
  have hstable : (prefixWord ++ tailWord_2067466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067466).length < 2 ^ (prefixWord ++ tailWord_2067466).sum := by decide
  have hdescent : baseEnd_2067466 < baseStart_2067466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067490 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_2067490 : Nat := 118140960795 + 2067490 * 2 ^ 59
def prefixEnd_2067490 : Nat := 4983230072969 + 3 ^ 40 * 2067490 * 2
def baseEnd_2067490 : Nat := 1061616118364221169566793

theorem tailTrace_2067490 : CollatzResearch.WordTrace tailWord_2067490 prefixEnd_2067490 1061616118364221169566793 := by
  unfold tailWord_2067490
  simp only [CollatzResearch.WordTrace]
  refine ⟨18851888819961076006361981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50271703519896202683631949 18851888819961076006361981)
  ·
    refine ⟨7069458307485403502385743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18851888819961076006361981 7069458307485403502385743)
    ·
      refine ⟨10604187461228105253578615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7069458307485403502385743 10604187461228105253578615)
      ·
        refine ⟨15906281191842157880367923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604187461228105253578615 15906281191842157880367923)
        ·
          refine ⟨23859421787763236820551885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15906281191842157880367923 23859421787763236820551885)
          ·
            refine ⟨8947283170411213807706957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23859421787763236820551885 8947283170411213807706957)
            ·
              refine ⟨3355231188904205177890109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947283170411213807706957 3355231188904205177890109)
              ·
                refine ⟨1258211695839076941708791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3355231188904205177890109 1258211695839076941708791)
                ·
                  refine ⟨1887317543758615412563187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258211695839076941708791 1887317543758615412563187)
                  ·
                    refine ⟨2830976315637923118844781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1887317543758615412563187 2830976315637923118844781)
                    ·
                      refine ⟨1061616118364221169566793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2830976315637923118844781 1061616118364221169566793)
                      ·
                        rfl

theorem cell23_2067490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_2067490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067490 prefixEnd_2067490 := by exact prefixLift 2067490
  have htrace : WordTrace (prefixWord ++ tailWord_2067490) baseStart_2067490 baseEnd_2067490 := by
    simpa [prefixWord, tailWord_2067490, baseEnd_2067490] using wordTrace_append hprefix tailTrace_2067490
  have hstable : (prefixWord ++ tailWord_2067490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067490).length < 2 ^ (prefixWord ++ tailWord_2067490).sum := by decide
  have hdescent : baseEnd_2067490 < baseStart_2067490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067499 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 5]
def baseStart_2067499 : Nat := 118140960795 + 2067499 * 2 ^ 59
def prefixEnd_2067499 : Nat := 4983230072969 + 3 ^ 40 * 2067499 * 2
def baseEnd_2067499 : Nat := 1061620739690111634354251

theorem tailTrace_2067499 : CollatzResearch.WordTrace tailWord_2067499 prefixEnd_2067499 1061620739690111634354251 := by
  unfold tailWord_2067499
  simp only [CollatzResearch.WordTrace]
  refine ⟨75407883536811698562525551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50271922357874465708350367 75407883536811698562525551)
  ·
    refine ⟨113111825305217547843788327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75407883536811698562525551 113111825305217547843788327)
    ·
      refine ⟨169667737957826321765682491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113111825305217547843788327 169667737957826321765682491)
      ·
        refine ⟨254501606936739482648523737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169667737957826321765682491 254501606936739482648523737)
        ·
          refine ⟨190876205202554611986392803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254501606936739482648523737 190876205202554611986392803)
          ·
            refine ⟨286314307803831917979589205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190876205202554611986392803 286314307803831917979589205)
            ·
              refine ⟨3355245794576155288823311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 286314307803831917979589205 3355245794576155288823311)
              ·
                refine ⟨5032868691864232933234967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355245794576155288823311 5032868691864232933234967)
                ·
                  refine ⟨7549303037796349399852451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032868691864232933234967 7549303037796349399852451)
                  ·
                    refine ⟨11323954556694524099778677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549303037796349399852451 11323954556694524099778677)
                    ·
                      refine ⟨1061620739690111634354251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11323954556694524099778677 1061620739690111634354251)
                      ·
                        rfl

theorem cell23_2067499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 5].length) (baseStart_2067499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067499 prefixEnd_2067499 := by exact prefixLift 2067499
  have htrace : WordTrace (prefixWord ++ tailWord_2067499) baseStart_2067499 baseEnd_2067499 := by
    simpa [prefixWord, tailWord_2067499, baseEnd_2067499] using wordTrace_append hprefix tailTrace_2067499
  have hstable : (prefixWord ++ tailWord_2067499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067499).length < 2 ^ (prefixWord ++ tailWord_2067499).sum := by decide
  have hdescent : baseEnd_2067499 < baseStart_2067499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067506 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_2067506 : Nat := 118140960795 + 2067506 * 2 ^ 59
def prefixEnd_2067506 : Nat := 4983230072969 + 3 ^ 40 * 2067506 * 2
def baseEnd_2067506 : Nat := 353874778018231035655573

theorem tailTrace_2067506 : CollatzResearch.WordTrace tailWord_2067506 prefixEnd_2067506 353874778018231035655573 := by
  unfold tailWord_2067506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852034711946584689507593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50272092565190892505353581 18852034711946584689507593)
  ·
    refine ⟨14139026033959938517130695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18852034711946584689507593 14139026033959938517130695)
    ·
      refine ⟨21208539050939907775696043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14139026033959938517130695 21208539050939907775696043)
      ·
        refine ⟨31812808576409861663544065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21208539050939907775696043 31812808576409861663544065)
        ·
          refine ⟨23859606432307396247658049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31812808576409861663544065 23859606432307396247658049)
          ·
            refine ⟨17894704824230547185743537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23859606432307396247658049 17894704824230547185743537)
            ·
              refine ⟨13421028618172910389307653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17894704824230547185743537 13421028618172910389307653)
              ·
                refine ⟨2516442865907420697995185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13421028618172910389307653 2516442865907420697995185)
                ·
                  refine ⟨1887332149430565523496389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516442865907420697995185 1887332149430565523496389)
                  ·
                    refine ⟨353874778018231035655573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1887332149430565523496389 353874778018231035655573)
                    ·
                      rfl

theorem cell23_2067506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_2067506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067506 prefixEnd_2067506 := by exact prefixLift 2067506
  have htrace : WordTrace (prefixWord ++ tailWord_2067506) baseStart_2067506 baseEnd_2067506 := by
    simpa [prefixWord, tailWord_2067506, baseEnd_2067506] using wordTrace_append hprefix tailTrace_2067506
  have hstable : (prefixWord ++ tailWord_2067506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067506).length < 2 ^ (prefixWord ++ tailWord_2067506).sum := by decide
  have hdescent : baseEnd_2067506 < baseStart_2067506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067533 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2067533 : Nat := 118140960795 + 2067533 * 2 ^ 59
def prefixEnd_2067533 : Nat := 4983230072969 + 3 ^ 40 * 2067533 * 2
def baseEnd_2067533 : Nat := 1061638198032364501329095

theorem tailTrace_2067533 : CollatzResearch.WordTrace tailWord_2067533 prefixEnd_2067533 1061638198032364501329095 := by
  unfold tailWord_2067533
  simp only [CollatzResearch.WordTrace]
  refine ⟨75409123618688522369263253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50272749079125681579508835 75409123618688522369263253)
  ·
    refine ⟨3534802669626024486059215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75409123618688522369263253 3534802669626024486059215)
    ·
      refine ⟨5302204004439036729088823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534802669626024486059215 5302204004439036729088823)
      ·
        refine ⟨7953306006658555093633235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302204004439036729088823 7953306006658555093633235)
        ·
          refine ⟨11929959009987832640449853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953306006658555093633235 11929959009987832640449853)
          ·
            refine ⟨4473734628745437240168695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11929959009987832640449853 4473734628745437240168695)
            ·
              refine ⟨6710601943118155860253043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473734628745437240168695 6710601943118155860253043)
              ·
                refine ⟨10065902914677233790379565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710601943118155860253043 10065902914677233790379565)
                ·
                  refine ⟨3774713593003962671392337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10065902914677233790379565 3774713593003962671392337)
                  ·
                    refine ⟨2831035194752972003544253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3774713593003962671392337 2831035194752972003544253)
                    ·
                      refine ⟨1061638198032364501329095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831035194752972003544253 1061638198032364501329095)
                      ·
                        rfl

theorem cell23_2067533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2067533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067533 prefixEnd_2067533 := by exact prefixLift 2067533
  have htrace : WordTrace (prefixWord ++ tailWord_2067533) baseStart_2067533 baseEnd_2067533 := by
    simpa [prefixWord, tailWord_2067533, baseEnd_2067533] using wordTrace_append hprefix tailTrace_2067533
  have hstable : (prefixWord ++ tailWord_2067533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067533).length < 2 ^ (prefixWord ++ tailWord_2067533).sum := by decide
  have hdescent : baseEnd_2067533 < baseStart_2067533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067546 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_2067546 : Nat := 118140960795 + 2067546 * 2 ^ 59
def prefixEnd_2067546 : Nat := 4983230072969 + 3 ^ 40 * 2067546 * 2
def baseEnd_2067546 : Nat := 1061644873280872950466535

theorem tailTrace_2067546 : CollatzResearch.WordTrace tailWord_2067546 prefixEnd_2067546 1061644873280872950466535 := by
  unfold tailWord_2067546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852399441910356397371623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50273065178427617059657661 18852399441910356397371623)
  ·
    refine ⟨28278599162865534596057435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18852399441910356397371623 28278599162865534596057435)
    ·
      refine ⟨42417898744298301894086153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28278599162865534596057435 42417898744298301894086153)
      ·
        refine ⟨31813424058223726420564615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42417898744298301894086153 31813424058223726420564615)
        ·
          refine ⟨47720136087335589630846923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31813424058223726420564615 47720136087335589630846923)
          ·
            refine ⟨71580204131003384446270385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47720136087335589630846923 71580204131003384446270385)
            ·
              refine ⟨53685153098252538334702789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71580204131003384446270385 53685153098252538334702789)
              ·
                refine ⟨10065966205922350937756773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53685153098252538334702789 10065966205922350937756773)
                ·
                  refine ⟨1887368663610440800829395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10065966205922350937756773 1887368663610440800829395)
                  ·
                    refine ⟨2831052995415661201244093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1887368663610440800829395 2831052995415661201244093)
                    ·
                      refine ⟨1061644873280872950466535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831052995415661201244093 1061644873280872950466535)
                      ·
                        rfl

theorem cell23_2067546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_2067546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067546 prefixEnd_2067546 := by exact prefixLift 2067546
  have htrace : WordTrace (prefixWord ++ tailWord_2067546) baseStart_2067546 baseEnd_2067546 := by
    simpa [prefixWord, tailWord_2067546, baseEnd_2067546] using wordTrace_append hprefix tailTrace_2067546
  have hstable : (prefixWord ++ tailWord_2067546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067546).length < 2 ^ (prefixWord ++ tailWord_2067546).sum := by decide
  have hdescent : baseEnd_2067546 < baseStart_2067546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067550 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2067550 : Nat := 118140960795 + 2067550 * 2 ^ 59
def prefixEnd_2067550 : Nat := 4983230072969 + 3 ^ 40 * 2067550 * 2
def baseEnd_2067550 : Nat := 1061646927203490934816517

theorem tailTrace_2067550 : CollatzResearch.WordTrace tailWord_2067550 prefixEnd_2067550 1061646927203490934816517 := by
  unfold tailWord_2067550
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426217957453366784079013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50273162439751289515088069 9426217957453366784079013)
  ·
    refine ⟨1767415867022506272014815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9426217957453366784079013 1767415867022506272014815)
    ·
      refine ⟨2651123800533759408022223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1767415867022506272014815 2651123800533759408022223)
      ·
        refine ⟨3976685700800639112033335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651123800533759408022223 3976685700800639112033335)
        ·
          refine ⟨5965028551200958668050003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976685700800639112033335 5965028551200958668050003)
          ·
            refine ⟨8947542826801438002075005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965028551200958668050003 8947542826801438002075005)
            ·
              refine ⟨3355328560050539250778127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947542826801438002075005 3355328560050539250778127)
              ·
                refine ⟨5032992840075808876167191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355328560050539250778127 5032992840075808876167191)
                ·
                  refine ⟨7549489260113713314250787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032992840075808876167191 7549489260113713314250787)
                  ·
                    refine ⟨11324233890170569971376181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7549489260113713314250787 11324233890170569971376181)
                    ·
                      refine ⟨1061646927203490934816517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11324233890170569971376181 1061646927203490934816517)
                      ·
                        rfl

theorem cell23_2067550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2067550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067550 prefixEnd_2067550 := by exact prefixLift 2067550
  have htrace : WordTrace (prefixWord ++ tailWord_2067550) baseStart_2067550 baseEnd_2067550 := by
    simpa [prefixWord, tailWord_2067550, baseEnd_2067550] using wordTrace_append hprefix tailTrace_2067550
  have hstable : (prefixWord ++ tailWord_2067550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067550).length < 2 ^ (prefixWord ++ tailWord_2067550).sum := by decide
  have hdescent : baseEnd_2067550 < baseStart_2067550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067607 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 1, 3, 2]
def baseStart_2067607 : Nat := 118140960795 + 2067607 * 2 ^ 59
def prefixEnd_2067607 : Nat := 4983230072969 + 3 ^ 40 * 2067607 * 2
def baseEnd_2067607 : Nat := 1061676195600797211803755

theorem tailTrace_2067607 : CollatzResearch.WordTrace tailWord_2067607 prefixEnd_2067607 1061676195600797211803755 := by
  unfold tailWord_2067607
  simp only [CollatzResearch.WordTrace]
  refine ⟨75411822620420433007457075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50274548413613622004971383 75411822620420433007457075)
  ·
    refine ⟨113117733930630649511185613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75411822620420433007457075 113117733930630649511185613)
    ·
      refine ⟨42419150223986493566694605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113117733930630649511185613 42419150223986493566694605)
      ·
        refine ⟨15907181333994935087510477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42419150223986493566694605 15907181333994935087510477)
        ·
          refine ⟨5965193000248100657816429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15907181333994935087510477 5965193000248100657816429)
          ·
            refine ⟨2236947375093037746681161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5965193000248100657816429 2236947375093037746681161)
            ·
              refine ⟨1677710531319778310010871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236947375093037746681161 1677710531319778310010871)
              ·
                refine ⟨2516565796979667465016307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677710531319778310010871 2516565796979667465016307)
                ·
                  refine ⟨3774848695469501197524461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516565796979667465016307 3774848695469501197524461)
                  ·
                    refine ⟨1415568260801062949071673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774848695469501197524461 1415568260801062949071673)
                    ·
                      refine ⟨1061676195600797211803755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415568260801062949071673 1061676195600797211803755)
                      ·
                        rfl

theorem cell23_2067607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_2067607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067607 prefixEnd_2067607 := by exact prefixLift 2067607
  have htrace : WordTrace (prefixWord ++ tailWord_2067607) baseStart_2067607 baseEnd_2067607 := by
    simpa [prefixWord, tailWord_2067607, baseEnd_2067607] using wordTrace_append hprefix tailTrace_2067607
  have hstable : (prefixWord ++ tailWord_2067607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067607).length < 2 ^ (prefixWord ++ tailWord_2067607).sum := by decide
  have hdescent : baseEnd_2067607 < baseStart_2067607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067620 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_2067620 : Nat := 118140960795 + 2067620 * 2 ^ 59
def prefixEnd_2067620 : Nat := 4983230072969 + 3 ^ 40 * 2067620 * 2
def baseEnd_2067620 : Nat := 1061682870849305660941195

theorem tailTrace_2067620 : CollatzResearch.WordTrace tailWord_2067620 prefixEnd_2067620 1061682870849305660941195 := by
  unfold tailWord_2067620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37706148384686668113840157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50274864512915557485120209 37706148384686668113840157)
  ·
    refine ⟨14139805644257500542690059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37706148384686668113840157 14139805644257500542690059)
    ·
      refine ⟨21209708466386250814035089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14139805644257500542690059 21209708466386250814035089)
      ·
        refine ⟨15907281349789688110526317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21209708466386250814035089 15907281349789688110526317)
        ·
          refine ⟨5965230506171133041447369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15907281349789688110526317 5965230506171133041447369)
          ·
            refine ⟨4473922879628349781085527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5965230506171133041447369 4473922879628349781085527)
            ·
              refine ⟨6710884319442524671628291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473922879628349781085527 6710884319442524671628291)
              ·
                refine ⟨10066326479163787007442437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6710884319442524671628291 10066326479163787007442437)
                ·
                  refine ⟨1887436214843210063895457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10066326479163787007442437 1887436214843210063895457)
                  ·
                    refine ⟨1415577161132407547921593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1887436214843210063895457 1415577161132407547921593)
                    ·
                      refine ⟨1061682870849305660941195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415577161132407547921593 1061682870849305660941195)
                      ·
                        rfl

theorem cell23_2067620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_2067620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067620 prefixEnd_2067620 := by exact prefixLift 2067620
  have htrace : WordTrace (prefixWord ++ tailWord_2067620) baseStart_2067620 baseEnd_2067620 := by
    simpa [prefixWord, tailWord_2067620, baseEnd_2067620] using wordTrace_append hprefix tailTrace_2067620
  have hstable : (prefixWord ++ tailWord_2067620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067620).length < 2 ^ (prefixWord ++ tailWord_2067620).sum := by decide
  have hdescent : baseEnd_2067620 < baseStart_2067620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067639 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 3, 7]
def baseStart_2067639 : Nat := 118140960795 + 2067639 * 2 ^ 59
def prefixEnd_2067639 : Nat := 4983230072969 + 3 ^ 40 * 2067639 * 2
def baseEnd_2067639 : Nat := 353897542327247028867869

theorem tailTrace_2067639 : CollatzResearch.WordTrace tailWord_2067639 prefixEnd_2067639 353897542327247028867869 := by
  unfold tailWord_2067639
  simp only [CollatzResearch.WordTrace]
  refine ⟨75412989756304502472621971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50275326504203001648414647 75412989756304502472621971)
  ·
    refine ⟨113119484634456753708932957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75412989756304502472621971 113119484634456753708932957)
    ·
      refine ⟨42419806737921282640849859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113119484634456753708932957 42419806737921282640849859)
      ·
        refine ⟨63629710106881923961274789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42419806737921282640849859 63629710106881923961274789)
        ·
          refine ⟨11930570645040360742739023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63629710106881923961274789 11930570645040360742739023)
          ·
            refine ⟨17895855967560541114108535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930570645040360742739023 17895855967560541114108535)
            ·
              refine ⟨26843783951340811671162803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895855967560541114108535 26843783951340811671162803)
              ·
                refine ⟨40265675927011217506744205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26843783951340811671162803 40265675927011217506744205)
                ·
                  refine ⟨15099628472629206565029077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40265675927011217506744205 15099628472629206565029077)
                  ·
                    refine ⟨353897542327247028867869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15099628472629206565029077 353897542327247028867869)
                    ·
                      rfl

theorem cell23_2067639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_2067639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067639 prefixEnd_2067639 := by exact prefixLift 2067639
  have htrace : WordTrace (prefixWord ++ tailWord_2067639) baseStart_2067639 baseEnd_2067639 := by
    simpa [prefixWord, tailWord_2067639, baseEnd_2067639] using wordTrace_append hprefix tailTrace_2067639
  have hstable : (prefixWord ++ tailWord_2067639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067639).length < 2 ^ (prefixWord ++ tailWord_2067639).sum := by decide
  have hdescent : baseEnd_2067639 < baseStart_2067639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067666 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2067666 : Nat := 118140960795 + 2067666 * 2 ^ 59
def prefixEnd_2067666 : Nat := 4983230072969 + 3 ^ 40 * 2067666 * 2
def baseEnd_2067666 : Nat := 1061706490959412480965983

theorem tailTrace_2067666 : CollatzResearch.WordTrace tailWord_2067666 prefixEnd_2067666 1061706490959412480965983 := by
  unfold tailWord_2067666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853493631801671520963713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50275983018137790722569901 18853493631801671520963713)
  ·
    refine ⟨14140120223851253640722785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18853493631801671520963713 14140120223851253640722785)
    ·
      refine ⟨10605090167888440230542089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14140120223851253640722785 10605090167888440230542089)
      ·
        refine ⟨7953817625916330172906567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10605090167888440230542089 7953817625916330172906567)
        ·
          refine ⟨11930726438874495259359851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953817625916330172906567 11930726438874495259359851)
          ·
            refine ⟨17896089658311742889039777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930726438874495259359851 17896089658311742889039777)
            ·
              refine ⟨13422067243733807166779833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17896089658311742889039777 13422067243733807166779833)
              ·
                refine ⟨10066550432800355375084875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13422067243733807166779833 10066550432800355375084875)
                ·
                  refine ⟨15099825649200533062627313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10066550432800355375084875 15099825649200533062627313)
                  ·
                    refine ⟨11324869236900399796970485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15099825649200533062627313 11324869236900399796970485)
                    ·
                      refine ⟨1061706490959412480965983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11324869236900399796970485 1061706490959412480965983)
                      ·
                        rfl

theorem cell23_2067666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2067666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067666 prefixEnd_2067666 := by exact prefixLift 2067666
  have htrace : WordTrace (prefixWord ++ tailWord_2067666) baseStart_2067666 baseEnd_2067666 := by
    simpa [prefixWord, tailWord_2067666, baseEnd_2067666] using wordTrace_append hprefix tailTrace_2067666
  have hstable : (prefixWord ++ tailWord_2067666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067666).length < 2 ^ (prefixWord ++ tailWord_2067666).sum := by decide
  have hdescent : baseEnd_2067666 < baseStart_2067666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067677 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 5]
def baseStart_2067677 : Nat := 118140960795 + 2067677 * 2 ^ 59
def prefixEnd_2067677 : Nat := 4983230072969 + 3 ^ 40 * 2067677 * 2
def baseEnd_2067677 : Nat := 117968015471845770880937

theorem tailTrace_2067677 : CollatzResearch.WordTrace tailWord_2067677 prefixEnd_2067677 117968015471845770880937 := by
  unfold tailWord_2067677
  simp only [CollatzResearch.WordTrace]
  refine ⟨75414375730166834962505285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50276250486777889975003523 75414375730166834962505285)
  ·
    refine ⟨14140195449406281555469741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75414375730166834962505285 14140195449406281555469741)
    ·
      refine ⟨5302573293527355583301153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14140195449406281555469741 5302573293527355583301153)
      ·
        refine ⟨3976929970145516687475865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5302573293527355583301153 3976929970145516687475865)
        ·
          refine ⟨2982697477609137515606899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976929970145516687475865 2982697477609137515606899)
          ·
            refine ⟨4474046216413706273410349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982697477609137515606899 4474046216413706273410349)
            ·
              refine ⟨1677767331155139852528881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4474046216413706273410349 1677767331155139852528881)
              ·
                refine ⟨1258325498366354889396661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677767331155139852528881 1258325498366354889396661)
                ·
                  refine ⟨117968015471845770880937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1258325498366354889396661 117968015471845770880937)
                  ·
                    rfl

theorem cell23_2067677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_2067677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067677 prefixEnd_2067677 := by exact prefixLift 2067677
  have htrace : WordTrace (prefixWord ++ tailWord_2067677) baseStart_2067677 baseEnd_2067677 := by
    simpa [prefixWord, tailWord_2067677, baseEnd_2067677] using wordTrace_append hprefix tailTrace_2067677
  have hstable : (prefixWord ++ tailWord_2067677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067677).length < 2 ^ (prefixWord ++ tailWord_2067677).sum := by decide
  have hdescent : baseEnd_2067677 < baseStart_2067677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067710 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2067710 : Nat := 118140960795 + 2067710 * 2 ^ 59
def prefixEnd_2067710 : Nat := 4983230072969 + 3 ^ 40 * 2067710 * 2
def baseEnd_2067710 : Nat := 1061729084108210308815781

theorem tailTrace_2067710 : CollatzResearch.WordTrace tailWord_2067710 prefixEnd_2067710 1061729084108210308815781 := by
  unfold tailWord_2067710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426947417380910199807073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50277052892698187732304389 9426947417380910199807073)
  ·
    refine ⟨7070210563035682649855305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9426947417380910199807073 7070210563035682649855305)
    ·
      refine ⟨5302657922276761987391479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070210563035682649855305 5302657922276761987391479)
      ·
        refine ⟨7953986883415142981087219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302657922276761987391479 7953986883415142981087219)
        ·
          refine ⟨11930980325122714471630829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953986883415142981087219 11930980325122714471630829)
          ·
            refine ⟨4474117621921017926861561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11930980325122714471630829 4474117621921017926861561)
            ·
              refine ⟨3355588216440763445146171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474117621921017926861561 3355588216440763445146171)
              ·
                refine ⟨5033382324661145167719257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355588216440763445146171 5033382324661145167719257)
                ·
                  refine ⟨3775036743495858875789443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5033382324661145167719257 3775036743495858875789443)
                  ·
                    refine ⟨5662555115243788313684165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3775036743495858875789443 5662555115243788313684165)
                    ·
                      refine ⟨1061729084108210308815781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5662555115243788313684165 1061729084108210308815781)
                      ·
                        rfl

theorem cell23_2067710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2067710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067710 prefixEnd_2067710 := by exact prefixLift 2067710
  have htrace : WordTrace (prefixWord ++ tailWord_2067710) baseStart_2067710 baseEnd_2067710 := by
    simpa [prefixWord, tailWord_2067710, baseEnd_2067710] using wordTrace_append hprefix tailTrace_2067710
  have hstable : (prefixWord ++ tailWord_2067710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067710).length < 2 ^ (prefixWord ++ tailWord_2067710).sum := by decide
  have hdescent : baseEnd_2067710 < baseStart_2067710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067713 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_2067713 : Nat := 118140960795 + 2067713 * 2 ^ 59
def prefixEnd_2067713 : Nat := 4983230072969 + 3 ^ 40 * 2067713 * 2
def baseEnd_2067713 : Nat := 1061730624550173797078267

theorem tailTrace_2067713 : CollatzResearch.WordTrace tailWord_2067713 prefixEnd_2067713 1061730624550173797078267 := by
  unfold tailWord_2067713
  simp only [CollatzResearch.WordTrace]
  refine ⟨75415688758036413110815793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50277125838690942073877195 75415688758036413110815793)
  ·
    refine ⟨56561766568527309833111845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75415688758036413110815793 56561766568527309833111845)
    ·
      refine ⟨10605331231598870593708471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56561766568527309833111845 10605331231598870593708471)
      ·
        refine ⟨15907996847398305890562707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605331231598870593708471 15907996847398305890562707)
        ·
          refine ⟨23861995271097458835844061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907996847398305890562707 23861995271097458835844061)
          ·
            refine ⟨8948248226661547063441523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23861995271097458835844061 8948248226661547063441523)
            ·
              refine ⟨13422372339992320595162285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948248226661547063441523 13422372339992320595162285)
              ·
                refine ⟨5033389627497120223185857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13422372339992320595162285 5033389627497120223185857)
                ·
                  refine ⟨3775042220622840167389393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5033389627497120223185857 3775042220622840167389393)
                  ·
                    refine ⟨2831281665467130125542045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3775042220622840167389393 2831281665467130125542045)
                    ·
                      refine ⟨1061730624550173797078267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831281665467130125542045 1061730624550173797078267)
                      ·
                        rfl

theorem cell23_2067713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_2067713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067713 prefixEnd_2067713 := by exact prefixLift 2067713
  have htrace : WordTrace (prefixWord ++ tailWord_2067713) baseStart_2067713 baseEnd_2067713 := by
    simpa [prefixWord, tailWord_2067713, baseEnd_2067713] using wordTrace_append hprefix tailTrace_2067713
  have hstable : (prefixWord ++ tailWord_2067713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067713).length < 2 ^ (prefixWord ++ tailWord_2067713).sum := by decide
  have hdescent : baseEnd_2067713 < baseStart_2067713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067776 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_2067776 : Nat := 118140960795 + 2067776 * 2 ^ 59
def prefixEnd_2067776 : Nat := 4983230072969 + 3 ^ 40 * 2067776 * 2
def baseEnd_2067776 : Nat := 353920991277135683530159

theorem tailTrace_2067776 : CollatzResearch.WordTrace tailWord_2067776 prefixEnd_2067776 353920991277135683530159 := by
  unfold tailWord_2067776
  simp only [CollatzResearch.WordTrace]
  refine ⟨37708993278404087435179591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50278657704538783246906121 37708993278404087435179591)
  ·
    refine ⟨56563489917606131152769387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37708993278404087435179591 56563489917606131152769387)
    ·
      refine ⟨84845234876409196729154081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56563489917606131152769387 84845234876409196729154081)
      ·
        refine ⟨63633926157306897546865561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84845234876409196729154081 63633926157306897546865561)
        ·
          refine ⟨47725444617980173160149171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63633926157306897546865561 47725444617980173160149171)
          ·
            refine ⟨71588166926970259740223757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47725444617980173160149171 71588166926970259740223757)
            ·
              refine ⟨26845562597613847402583909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71588166926970259740223757 26845562597613847402583909)
              ·
                refine ⟨5033542987052596387984483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26845562597613847402583909 5033542987052596387984483)
                ·
                  refine ⟨7550314480578894581976725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033542987052596387984483 7550314480578894581976725)
                  ·
                    refine ⟨353920991277135683530159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7550314480578894581976725 353920991277135683530159)
                    ·
                      rfl

theorem cell23_2067776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_2067776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067776 prefixEnd_2067776 := by exact prefixLift 2067776
  have htrace : WordTrace (prefixWord ++ tailWord_2067776) baseStart_2067776 baseEnd_2067776 := by
    simpa [prefixWord, tailWord_2067776, baseEnd_2067776] using wordTrace_append hprefix tailTrace_2067776
  have hstable : (prefixWord ++ tailWord_2067776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067776).length < 2 ^ (prefixWord ++ tailWord_2067776).sum := by decide
  have hdescent : baseEnd_2067776 < baseStart_2067776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067786 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2067786 : Nat := 118140960795 + 2067786 * 2 ^ 59
def prefixEnd_2067786 : Nat := 4983230072969 + 3 ^ 40 * 2067786 * 2
def baseEnd_2067786 : Nat := 1061768108637952011465431

theorem tailTrace_2067786 : CollatzResearch.WordTrace tailWord_2067786 prefixEnd_2067786 1061768108637952011465431 := by
  unfold tailWord_2067786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18854587821692986644555803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50278900857847964385482141 18854587821692986644555803)
  ·
    refine ⟨28281881732539479966833705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18854587821692986644555803 28281881732539479966833705)
    ·
      refine ⟨21211411299404609975125279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28281881732539479966833705 21211411299404609975125279)
      ·
        refine ⟨31817116949106914962687919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21211411299404609975125279 31817116949106914962687919)
        ·
          refine ⟨47725675423660372444031879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31817116949106914962687919 47725675423660372444031879)
          ·
            refine ⟨71588513135490558666047819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47725675423660372444031879 71588513135490558666047819)
            ·
              refine ⟨107382769703235837999071729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71588513135490558666047819 107382769703235837999071729)
              ·
                refine ⟨80537077277426878499303797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107382769703235837999071729 80537077277426878499303797)
                ·
                  refine ⟨7550350994758769859309731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80537077277426878499303797 7550350994758769859309731)
                  ·
                    refine ⟨11325526492138154788964597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7550350994758769859309731 11325526492138154788964597)
                    ·
                      refine ⟨1061768108637952011465431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11325526492138154788964597 1061768108637952011465431)
                      ·
                        rfl

theorem cell23_2067786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2067786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067786 prefixEnd_2067786 := by exact prefixLift 2067786
  have htrace : WordTrace (prefixWord ++ tailWord_2067786) baseStart_2067786 baseEnd_2067786 := by
    simpa [prefixWord, tailWord_2067786, baseEnd_2067786] using wordTrace_append hprefix tailTrace_2067786
  have hstable : (prefixWord ++ tailWord_2067786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067786).length < 2 ^ (prefixWord ++ tailWord_2067786).sum := by decide
  have hdescent : baseEnd_2067786 < baseStart_2067786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067793 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 4, 4]
def baseStart_2067793 : Nat := 118140960795 + 2067793 * 2 ^ 59
def prefixEnd_2067793 : Nat := 4983230072969 + 3 ^ 40 * 2067793 * 2
def baseEnd_2067793 : Nat := 353923901000844494692633

theorem tailTrace_2067793 : CollatzResearch.WordTrace tailWord_2067793 prefixEnd_2067793 353923901000844494692633 := by
  unfold tailWord_2067793
  simp only [CollatzResearch.WordTrace]
  refine ⟨75418606597746586773728033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50279071065164391182485355 75418606597746586773728033)
  ·
    refine ⟨56563954948309940080296025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75418606597746586773728033 56563954948309940080296025)
    ·
      refine ⟨42422966211232455060222019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56563954948309940080296025 42422966211232455060222019)
      ·
        refine ⟨63634449316848682590333029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42422966211232455060222019 63634449316848682590333029)
        ·
          refine ⟨11931459246909127985687443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63634449316848682590333029 11931459246909127985687443)
          ·
            refine ⟨17897188870363691978531165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931459246909127985687443 17897188870363691978531165)
            ·
              refine ⟨6711445826386384491949187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17897188870363691978531165 6711445826386384491949187)
              ·
                refine ⟨10067168739579576737923781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711445826386384491949187 10067168739579576737923781)
                ·
                  refine ⟨1887594138671170638360709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10067168739579576737923781 1887594138671170638360709)
                  ·
                    refine ⟨353923901000844494692633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1887594138671170638360709 353923901000844494692633)
                    ·
                      rfl

theorem cell23_2067793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_2067793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067793 prefixEnd_2067793 := by exact prefixLift 2067793
  have htrace : WordTrace (prefixWord ++ tailWord_2067793) baseStart_2067793 baseEnd_2067793 := by
    simpa [prefixWord, tailWord_2067793, baseEnd_2067793] using wordTrace_append hprefix tailTrace_2067793
  have hstable : (prefixWord ++ tailWord_2067793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067793).length < 2 ^ (prefixWord ++ tailWord_2067793).sum := by decide
  have hdescent : baseEnd_2067793 < baseStart_2067793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067820 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_2067820 : Nat := 118140960795 + 2067820 * 2 ^ 59
def prefixEnd_2067820 : Nat := 4983230072969 + 3 ^ 40 * 2067820 * 2
def baseEnd_2067820 : Nat := 1061785566980204878440275

theorem tailTrace_2067820 : CollatzResearch.WordTrace tailWord_2067820 prefixEnd_2067820 1061785566980204878440275 := by
  unfold tailWord_2067820
  simp only [CollatzResearch.WordTrace]
  refine ⟨37709795684324385192480457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50279727579099180256640609 37709795684324385192480457)
  ·
    refine ⟨28282346763243288894360343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37709795684324385192480457 28282346763243288894360343)
    ·
      refine ⟨42423520144864933341540515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28282346763243288894360343 42423520144864933341540515)
      ·
        refine ⟨63635280217297400012310773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42423520144864933341540515 63635280217297400012310773)
        ·
          refine ⟨5965807520371631251154135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63635280217297400012310773 5965807520371631251154135)
          ·
            refine ⟨8948711280557446876731203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965807520371631251154135 8948711280557446876731203)
            ·
              refine ⟨13423066920836170315096805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948711280557446876731203 13423066920836170315096805)
              ·
                refine ⟨2516825047656781934080651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13423066920836170315096805 2516825047656781934080651)
                ·
                  refine ⟨3775237571485172901120977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516825047656781934080651 3775237571485172901120977)
                  ·
                    refine ⟨2831428178613879675840733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3775237571485172901120977 2831428178613879675840733)
                    ·
                      refine ⟨1061785566980204878440275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831428178613879675840733 1061785566980204878440275)
                      ·
                        rfl

theorem cell23_2067820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_2067820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067820 prefixEnd_2067820 := by exact prefixLift 2067820
  have htrace : WordTrace (prefixWord ++ tailWord_2067820) baseStart_2067820 baseEnd_2067820 := by
    simpa [prefixWord, tailWord_2067820, baseEnd_2067820] using wordTrace_append hprefix tailTrace_2067820
  have hstable : (prefixWord ++ tailWord_2067820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067820).length < 2 ^ (prefixWord ++ tailWord_2067820).sum := by decide
  have hdescent : baseEnd_2067820 < baseStart_2067820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067833 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_2067833 : Nat := 118140960795 + 2067833 * 2 ^ 59
def prefixEnd_2067833 : Nat := 4983230072969 + 3 ^ 40 * 2067833 * 2
def baseEnd_2067833 : Nat := 1061792242228713327577715

theorem tailTrace_2067833 : CollatzResearch.WordTrace tailWord_2067833 prefixEnd_2067833 1061792242228713327577715 := by
  unfold tailWord_2067833
  simp only [CollatzResearch.WordTrace]
  refine ⟨75420065517601673605184153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50280043678401115736789435 75420065517601673605184153)
  ·
    refine ⟨56565049138201255203888115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75420065517601673605184153 56565049138201255203888115)
    ·
      refine ⟨84847573707301882805832173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56565049138201255203888115 84847573707301882805832173)
      ·
        refine ⟨31817840140238206052187065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84847573707301882805832173 31817840140238206052187065)
        ·
          refine ⟨23863380105178654539140299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31817840140238206052187065 23863380105178654539140299)
          ·
            refine ⟨35795070157767981808710449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23863380105178654539140299 35795070157767981808710449)
            ·
              refine ⟨26846302618325986356532837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35795070157767981808710449 26846302618325986356532837)
              ·
                refine ⟨5033681740936122441849907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26846302618325986356532837 5033681740936122441849907)
                ·
                  refine ⟨7550522611404183662774861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033681740936122441849907 7550522611404183662774861)
                  ·
                    refine ⟨2831445979276568873540573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7550522611404183662774861 2831445979276568873540573)
                    ·
                      refine ⟨1061792242228713327577715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831445979276568873540573 1061792242228713327577715)
                      ·
                        rfl

theorem cell23_2067833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_2067833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067833 prefixEnd_2067833 := by exact prefixLift 2067833
  have htrace : WordTrace (prefixWord ++ tailWord_2067833) baseStart_2067833 baseEnd_2067833 := by
    simpa [prefixWord, tailWord_2067833, baseEnd_2067833] using wordTrace_append hprefix tailTrace_2067833
  have hstable : (prefixWord ++ tailWord_2067833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067833).length < 2 ^ (prefixWord ++ tailWord_2067833).sum := by decide
  have hdescent : baseEnd_2067833 < baseStart_2067833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067907 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 2, 2, 2]
def baseStart_2067907 : Nat := 118140960795 + 2067907 * 2 ^ 59
def prefixEnd_2067907 : Nat := 4983230072969 + 3 ^ 40 * 2067907 * 2
def baseEnd_2067907 : Nat := 1061830239797146038052375

theorem tailTrace_2067907 : CollatzResearch.WordTrace tailWord_2067907 prefixEnd_2067907 1061830239797146038052375 := by
  unfold tailWord_2067907
  simp only [CollatzResearch.WordTrace]
  refine ⟨75422764519333584243377975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50281843012889056162251983 75422764519333584243377975)
  ·
    refine ⟨113134146779000376365066963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75422764519333584243377975 113134146779000376365066963)
    ·
      refine ⟨169701220168500564547600445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113134146779000376365066963 169701220168500564547600445)
      ·
        refine ⟨63637957563187711705350167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169701220168500564547600445 63637957563187711705350167)
        ·
          refine ⟨95456936344781567558025251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63637957563187711705350167 95456936344781567558025251)
          ·
            refine ⟨143185404517172351337037877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95456936344781567558025251 143185404517172351337037877)
            ·
              refine ⟨13423631673484907937847301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143185404517172351337037877 13423631673484907937847301)
              ·
                refine ⟨2516930938778420238346369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13423631673484907937847301 2516930938778420238346369)
                ·
                  refine ⟨1887698204083815178759777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516930938778420238346369 1887698204083815178759777)
                  ·
                    refine ⟨1415773653062861384069833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1887698204083815178759777 1415773653062861384069833)
                    ·
                      refine ⟨1061830239797146038052375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415773653062861384069833 1061830239797146038052375)
                      ·
                        rfl

theorem cell23_2067907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_2067907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067907 prefixEnd_2067907 := by exact prefixLift 2067907
  have htrace : WordTrace (prefixWord ++ tailWord_2067907) baseStart_2067907 baseEnd_2067907 := by
    simpa [prefixWord, tailWord_2067907, baseEnd_2067907] using wordTrace_append hprefix tailTrace_2067907
  have hstable : (prefixWord ++ tailWord_2067907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067907).length < 2 ^ (prefixWord ++ tailWord_2067907).sum := by decide
  have hdescent : baseEnd_2067907 < baseStart_2067907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067924 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2067924 : Nat := 118140960795 + 2067924 * 2 ^ 59
def prefixEnd_2067924 : Nat := 4983230072969 + 3 ^ 40 * 2067924 * 2
def baseEnd_2067924 : Nat := 1061838968968272471539797

theorem tailTrace_2067924 : CollatzResearch.WordTrace tailWord_2067924 prefixEnd_2067924 1061838968968272471539797 := by
  unfold tailWord_2067924
  simp only [CollatzResearch.WordTrace]
  refine ⟨37711692280135998073373413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50282256373514664097831217 37711692280135998073373413)
  ·
    refine ⟨7070942302525499638757515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37711692280135998073373413 7070942302525499638757515)
    ·
      refine ⟨10606413453788249458136273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070942302525499638757515 10606413453788249458136273)
      ·
        refine ⟨7954810090341187093602205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10606413453788249458136273 7954810090341187093602205)
        ·
          refine ⟨2983053783877945160100827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7954810090341187093602205 2983053783877945160100827)
          ·
            refine ⟨4474580675816917740151241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983053783877945160100827 4474580675816917740151241)
            ·
              refine ⟨3355935506862688305113431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474580675816917740151241 3355935506862688305113431)
              ·
                refine ⟨5033903260294032457670147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355935506862688305113431 5033903260294032457670147)
                ·
                  refine ⟨7550854890441048686505221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033903260294032457670147 7550854890441048686505221)
                  ·
                    refine ⟨1415785291957696628719729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7550854890441048686505221 1415785291957696628719729)
                    ·
                      refine ⟨1061838968968272471539797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415785291957696628719729 1061838968968272471539797)
                      ·
                        rfl

theorem cell23_2067924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2067924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067924 prefixEnd_2067924 := by exact prefixLift 2067924
  have htrace : WordTrace (prefixWord ++ tailWord_2067924) baseStart_2067924 baseEnd_2067924 := by
    simpa [prefixWord, tailWord_2067924, baseEnd_2067924] using wordTrace_append hprefix tailTrace_2067924
  have hstable : (prefixWord ++ tailWord_2067924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067924).length < 2 ^ (prefixWord ++ tailWord_2067924).sum := by decide
  have hdescent : baseEnd_2067924 < baseStart_2067924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067957 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2067957 : Nat := 118140960795 + 2067957 * 2 ^ 59
def prefixEnd_2067957 : Nat := 4983230072969 + 3 ^ 40 * 2067957 * 2
def baseEnd_2067957 : Nat := 1061855913829870842427145

theorem tailTrace_2067957 : CollatzResearch.WordTrace tailWord_2067957 prefixEnd_2067957 1061855913829870842427145 := by
  unfold tailWord_2067957
  simp only [CollatzResearch.WordTrace]
  refine ⟨75424588169152442782698125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50283058779434961855132083 75424588169152442782698125)
  ·
    refine ⟨28284220563432166043511797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75424588169152442782698125 28284220563432166043511797)
    ·
      refine ⟨2651645677821765566579231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28284220563432166043511797 2651645677821765566579231)
      ·
        refine ⟨3977468516732648349868847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651645677821765566579231 3977468516732648349868847)
        ·
          refine ⟨5966202775098972524803271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3977468516732648349868847 5966202775098972524803271)
          ·
            refine ⟨8949304162648458787204907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5966202775098972524803271 8949304162648458787204907)
            ·
              refine ⟨13423956243972688180807361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8949304162648458787204907 13423956243972688180807361)
              ·
                refine ⟨10067967182979516135605521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13423956243972688180807361 10067967182979516135605521)
                ·
                  refine ⟨7550975387234637101704141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10067967182979516135605521 7550975387234637101704141)
                  ·
                    refine ⟨2831615770212988913139053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7550975387234637101704141 2831615770212988913139053)
                    ·
                      refine ⟨1061855913829870842427145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831615770212988913139053 1061855913829870842427145)
                      ·
                        rfl

theorem cell23_2067957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2067957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2067957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2067957 prefixEnd_2067957 := by exact prefixLift 2067957
  have htrace : WordTrace (prefixWord ++ tailWord_2067957) baseStart_2067957 baseEnd_2067957 := by
    simpa [prefixWord, tailWord_2067957, baseEnd_2067957] using wordTrace_append hprefix tailTrace_2067957
  have hstable : (prefixWord ++ tailWord_2067957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067957).length < 2 ^ (prefixWord ++ tailWord_2067957).sum := by decide
  have hdescent : baseEnd_2067957 < baseStart_2067957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068064 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 1, 1, 3]
def baseStart_2068064 : Nat := 118140960795 + 2068064 * 2 ^ 59
def prefixEnd_2068064 : Nat := 4983230072969 + 3 ^ 40 * 2068064 * 2
def baseEnd_2068064 : Nat := 1061910856259901923789153

theorem tailTrace_2068064 : CollatzResearch.WordTrace tailWord_2068064 prefixEnd_2068064 1061910856259901923789153 := by
  unfold tailWord_2068064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37714245389882400028421623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50285660519843200037895497 37714245389882400028421623)
  ·
    refine ⟨56571368084823600042632435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37714245389882400028421623 56571368084823600042632435)
    ·
      refine ⟨84857052127235400063948653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56571368084823600042632435 84857052127235400063948653)
      ·
        refine ⟨31821394547713275023980745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84857052127235400063948653 31821394547713275023980745)
        ·
          refine ⟨23866045910784956267985559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31821394547713275023980745 23866045910784956267985559)
          ·
            refine ⟨35799068866177434401978339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23866045910784956267985559 35799068866177434401978339)
            ·
              refine ⟨53698603299266151602967509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35799068866177434401978339 53698603299266151602967509)
              ·
                refine ⟨1258561014826550428194551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53698603299266151602967509 1258561014826550428194551)
                ·
                  refine ⟨1887841522239825642291827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258561014826550428194551 1887841522239825642291827)
                  ·
                    refine ⟨2831762283359738463437741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1887841522239825642291827 2831762283359738463437741)
                    ·
                      refine ⟨1061910856259901923789153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831762283359738463437741 1061910856259901923789153)
                      ·
                        rfl

theorem cell23_2068064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_2068064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068064 prefixEnd_2068064 := by exact prefixLift 2068064
  have htrace : WordTrace (prefixWord ++ tailWord_2068064) baseStart_2068064 baseEnd_2068064 := by
    simpa [prefixWord, tailWord_2068064, baseEnd_2068064] using wordTrace_append hprefix tailTrace_2068064
  have hstable : (prefixWord ++ tailWord_2068064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068064).length < 2 ^ (prefixWord ++ tailWord_2068064).sum := by decide
  have hdescent : baseEnd_2068064 < baseStart_2068064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068074 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_2068074 : Nat := 118140960795 + 2068074 * 2 ^ 59
def prefixEnd_2068074 : Nat := 4983230072969 + 3 ^ 40 * 2068074 * 2
def baseEnd_2068074 : Nat := 1061915991066446884664107

theorem tailTrace_2068074 : CollatzResearch.WordTrace tailWord_2068074 prefixEnd_2068074 1061915991066446884664107 := by
  unfold tailWord_2068074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18857213877432142941176819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50285903673152381176471517 18857213877432142941176819)
  ·
    refine ⟨28285820816148214411765229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18857213877432142941176819 28285820816148214411765229)
    ·
      refine ⟨10607182806055580404411961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28285820816148214411765229 10607182806055580404411961)
      ·
        refine ⟨7955387104541685303308971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10607182806055580404411961 7955387104541685303308971)
        ·
          refine ⟨11933080656812527954963457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955387104541685303308971 11933080656812527954963457)
          ·
            refine ⟨8949810492609395966222593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11933080656812527954963457 8949810492609395966222593)
            ·
              refine ⟨6712357869457046974666945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8949810492609395966222593 6712357869457046974666945)
              ·
                refine ⟨5034268402092785231000209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6712357869457046974666945 5034268402092785231000209)
                ·
                  refine ⟨3775701301569588923250157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5034268402092785231000209 3775701301569588923250157)
                  ·
                    refine ⟨1415887988088595846218809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3775701301569588923250157 1415887988088595846218809)
                    ·
                      refine ⟨1061915991066446884664107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415887988088595846218809 1061915991066446884664107)
                      ·
                        rfl

theorem cell23_2068074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_2068074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068074 prefixEnd_2068074 := by exact prefixLift 2068074
  have htrace : WordTrace (prefixWord ++ tailWord_2068074) baseStart_2068074 baseEnd_2068074 := by
    simpa [prefixWord, tailWord_2068074, baseEnd_2068074] using wordTrace_append hprefix tailTrace_2068074
  have hstable : (prefixWord ++ tailWord_2068074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068074).length < 2 ^ (prefixWord ++ tailWord_2068074).sum := by decide
  have hdescent : baseEnd_2068074 < baseStart_2068074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068097 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2068097 : Nat := 118140960795 + 2068097 * 2 ^ 59
def prefixEnd_2068097 : Nat := 4983230072969 + 3 ^ 40 * 2068097 * 2
def baseEnd_2068097 : Nat := 353975933707166764892167

theorem tailTrace_2068097 : CollatzResearch.WordTrace tailWord_2068097 prefixEnd_2068097 353975933707166764892167 := by
  unfold tailWord_2068097
  simp only [CollatzResearch.WordTrace]
  refine ⟨75429694388645246692794545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50286462925763497795196363 75429694388645246692794545)
  ·
    refine ⟨56572270791483935019595909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75429694388645246692794545 56572270791483935019595909)
    ·
      refine ⟨10607300773403237816174233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56572270791483935019595909 10607300773403237816174233)
      ·
        refine ⟨7955475580052428362130675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10607300773403237816174233 7955475580052428362130675)
        ·
          refine ⟨11933213370078642543196013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955475580052428362130675 11933213370078642543196013)
          ·
            refine ⟨4474955013779490953698505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11933213370078642543196013 4474955013779490953698505)
            ·
              refine ⟨3356216260334618215273879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474955013779490953698505 3356216260334618215273879)
              ·
                refine ⟨5034324390501927322910819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356216260334618215273879 5034324390501927322910819)
                ·
                  refine ⟨7551486585752890984366229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5034324390501927322910819 7551486585752890984366229)
                  ·
                    refine ⟨353975933707166764892167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7551486585752890984366229 353975933707166764892167)
                    ·
                      rfl

theorem cell23_2068097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2068097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068097 prefixEnd_2068097 := by exact prefixLift 2068097
  have htrace : WordTrace (prefixWord ++ tailWord_2068097) baseStart_2068097 baseEnd_2068097 := by
    simpa [prefixWord, tailWord_2068097, baseEnd_2068097] using wordTrace_append hprefix tailTrace_2068097
  have hstable : (prefixWord ++ tailWord_2068097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068097).length < 2 ^ (prefixWord ++ tailWord_2068097).sum := by decide
  have hdescent : baseEnd_2068097 < baseStart_2068097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068107 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 3]
def baseStart_2068107 : Nat := 118140960795 + 2068107 * 2 ^ 59
def prefixEnd_2068107 : Nat := 4983230072969 + 3 ^ 40 * 2068107 * 2
def baseEnd_2068107 : Nat := 1061932935928045255551455

theorem tailTrace_2068107 : CollatzResearch.WordTrace tailWord_2068107 prefixEnd_2068107 1061932935928045255551455 := by
  unfold tailWord_2068107
  simp only [CollatzResearch.WordTrace]
  refine ⟨75430059118609018400658575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50286706079072678933772383 75430059118609018400658575)
  ·
    refine ⟨113145088677913527600987863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75430059118609018400658575 113145088677913527600987863)
    ·
      refine ⟨169717633016870291401481795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113145088677913527600987863 169717633016870291401481795)
      ·
        refine ⟨254576449525305437102222693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169717633016870291401481795 254576449525305437102222693)
        ·
          refine ⟨47733084285994769456666755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254576449525305437102222693 47733084285994769456666755)
          ·
            refine ⟨71599626428992154185000133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47733084285994769456666755 71599626428992154185000133)
            ·
              refine ⟨13424929955436028909687525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71599626428992154185000133 13424929955436028909687525)
              ·
                refine ⟨2517174366644255420566411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13424929955436028909687525 2517174366644255420566411)
                ·
                  refine ⟨3775761549966383130849617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517174366644255420566411 3775761549966383130849617)
                  ·
                    refine ⟨2831821162474787348137213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3775761549966383130849617 2831821162474787348137213)
                    ·
                      refine ⟨1061932935928045255551455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831821162474787348137213 1061932935928045255551455)
                      ·
                        rfl

theorem cell23_2068107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 3].length) (baseStart_2068107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068107 prefixEnd_2068107 := by exact prefixLift 2068107
  have htrace : WordTrace (prefixWord ++ tailWord_2068107) baseStart_2068107 baseEnd_2068107 := by
    simpa [prefixWord, tailWord_2068107, baseEnd_2068107] using wordTrace_append hprefix tailTrace_2068107
  have hstable : (prefixWord ++ tailWord_2068107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068107).length < 2 ^ (prefixWord ++ tailWord_2068107).sum := by decide
  have hdescent : baseEnd_2068107 < baseStart_2068107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068127 : List Nat := [1, 1, 2, 7, 1, 1, 10]
def baseStart_2068127 : Nat := 118140960795 + 2068127 * 2 ^ 59
def prefixEnd_2068127 : Nat := 4983230072969 + 3 ^ 40 * 2068127 * 2
def baseEnd_2068127 : Nat := 13110409944952286139523

theorem tailTrace_2068127 : CollatzResearch.WordTrace tailWord_2068127 prefixEnd_2068127 13110409944952286139523 := by
  unfold tailWord_2068127
  simp only [CollatzResearch.WordTrace]
  refine ⟨75430788578536561816386635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50287192385691041210924423 75430788578536561816386635)
  ·
    refine ⟨113146182867804842724579953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75430788578536561816386635 113146182867804842724579953)
    ·
      refine ⟨84859637150853632043434965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113146182867804842724579953 84859637150853632043434965)
      ·
        refine ⟨1988897745723132001018007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84859637150853632043434965 1988897745723132001018007)
        ·
          refine ⟨2983346618584698001527011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988897745723132001018007 2983346618584698001527011)
          ·
            refine ⟨4475019927877047002290517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983346618584698001527011 4475019927877047002290517)
            ·
              refine ⟨13110409944952286139523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4475019927877047002290517 13110409944952286139523)
              ·
                rfl

theorem cell23_2068127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 10].length) (baseStart_2068127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068127 prefixEnd_2068127 := by exact prefixLift 2068127
  have htrace : WordTrace (prefixWord ++ tailWord_2068127) baseStart_2068127 baseEnd_2068127 := by
    simpa [prefixWord, tailWord_2068127, baseEnd_2068127] using wordTrace_append hprefix tailTrace_2068127
  have hstable : (prefixWord ++ tailWord_2068127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068127).length < 2 ^ (prefixWord ++ tailWord_2068127).sum := by decide
  have hdescent : baseEnd_2068127 < baseStart_2068127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068154 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_2068154 : Nat := 118140960795 + 2068154 * 2 ^ 59
def prefixEnd_2068154 : Nat := 4983230072969 + 3 ^ 40 * 2068154 * 2
def baseEnd_2068154 : Nat := 1061957069518806571663739

theorem tailTrace_2068154 : CollatzResearch.WordTrace tailWord_2068154 prefixEnd_2068154 1061957069518806571663739 := by
  unfold tailWord_2068154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18857943337359686356904879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50287848899625830285079677 18857943337359686356904879)
  ·
    refine ⟨28286915006039529535357319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18857943337359686356904879 28286915006039529535357319)
    ·
      refine ⟨42430372509059294303035979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28286915006039529535357319 42430372509059294303035979)
      ·
        refine ⟨63645558763588941454553969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42430372509059294303035979 63645558763588941454553969)
        ·
          refine ⟨47734169072691706090915477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63645558763588941454553969 47734169072691706090915477)
          ·
            refine ⟨2237539175282423723011663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47734169072691706090915477 2237539175282423723011663)
            ·
              refine ⟨3356308762923635584517495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237539175282423723011663 3356308762923635584517495)
              ·
                refine ⟨5034463144385453376776243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356308762923635584517495 5034463144385453376776243)
                ·
                  refine ⟨7551694716578180065164365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5034463144385453376776243 7551694716578180065164365)
                  ·
                    refine ⟨2831885518716817524436637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7551694716578180065164365 2831885518716817524436637)
                    ·
                      refine ⟨1061957069518806571663739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831885518716817524436637 1061957069518806571663739)
                      ·
                        rfl

theorem cell23_2068154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_2068154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068154 prefixEnd_2068154 := by exact prefixLift 2068154
  have htrace : WordTrace (prefixWord ++ tailWord_2068154) baseStart_2068154 baseEnd_2068154 := by
    simpa [prefixWord, tailWord_2068154, baseEnd_2068154] using wordTrace_append hprefix tailTrace_2068154
  have hstable : (prefixWord ++ tailWord_2068154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068154).length < 2 ^ (prefixWord ++ tailWord_2068154).sum := by decide
  have hdescent : baseEnd_2068154 < baseStart_2068154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068172 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2068172 : Nat := 118140960795 + 2068172 * 2 ^ 59
def prefixEnd_2068172 : Nat := 4983230072969 + 3 ^ 40 * 2068172 * 2
def baseEnd_2068172 : Nat := 1061966312170587501238657

theorem tailTrace_2068172 : CollatzResearch.WordTrace tailWord_2068172 prefixEnd_2068172 1061966312170587501238657 := by
  unfold tailWord_2068172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37716214931686767250887385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50288286575582356334516513 37716214931686767250887385)
  ·
    refine ⟨28287161198765075438165539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37716214931686767250887385 28287161198765075438165539)
    ·
      refine ⟨42430741798147613157248309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28287161198765075438165539 42430741798147613157248309)
      ·
        refine ⟨3977882043576338733492029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42430741798147613157248309 3977882043576338733492029)
        ·
          refine ⟨1491705766341127025059511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3977882043576338733492029 1491705766341127025059511)
          ·
            refine ⟨2237558649511690537589267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491705766341127025059511 2237558649511690537589267)
            ·
              refine ⟨3356337974267535806383901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237558649511690537589267 3356337974267535806383901)
              ·
                refine ⟨1258626740350325927393963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3356337974267535806383901 1258626740350325927393963)
                ·
                  refine ⟨1887940110525488891090945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258626740350325927393963 1887940110525488891090945)
                  ·
                    refine ⟨1415955082894116668318209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1887940110525488891090945 1415955082894116668318209)
                    ·
                      refine ⟨1061966312170587501238657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1415955082894116668318209 1061966312170587501238657)
                      ·
                        rfl

theorem cell23_2068172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2068172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068172 prefixEnd_2068172 := by exact prefixLift 2068172
  have htrace : WordTrace (prefixWord ++ tailWord_2068172) baseStart_2068172 baseEnd_2068172 := by
    simpa [prefixWord, tailWord_2068172, baseEnd_2068172] using wordTrace_append hprefix tailTrace_2068172
  have hstable : (prefixWord ++ tailWord_2068172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068172).length < 2 ^ (prefixWord ++ tailWord_2068172).sum := by decide
  have hdescent : baseEnd_2068172 < baseStart_2068172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068197 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2068197 : Nat := 118140960795 + 2068197 * 2 ^ 59
def prefixEnd_2068197 : Nat := 4983230072969 + 3 ^ 40 * 2068197 * 2
def baseEnd_2068197 : Nat := 1061979149186949903426041

theorem tailTrace_2068197 : CollatzResearch.WordTrace tailWord_2068197 prefixEnd_2068197 1061979149186949903426041 := by
  unfold tailWord_2068197
  simp only [CollatzResearch.WordTrace]
  refine ⟨75433341688282963771434845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50288894458855309180956563 75433341688282963771434845)
  ·
    refine ⟨28287503133106111414288067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75433341688282963771434845 28287503133106111414288067)
    ·
      refine ⟨42431254699659167121432101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28287503133106111414288067 42431254699659167121432101)
      ·
        refine ⟨7955860256186093835268519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42431254699659167121432101 7955860256186093835268519)
        ·
          refine ⟨11933790384279140752902779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955860256186093835268519 11933790384279140752902779)
          ·
            refine ⟨17900685576418711129354169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933790384279140752902779 17900685576418711129354169)
            ·
              refine ⟨13425514182314033347015627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17900685576418711129354169 13425514182314033347015627)
              ·
                refine ⟨20138271273471050020523441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13425514182314033347015627 20138271273471050020523441)
                ·
                  refine ⟨15103703455103287515392581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20138271273471050020523441 15103703455103287515392581)
                  ·
                    refine ⟨2831944397831866409136109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15103703455103287515392581 2831944397831866409136109)
                    ·
                      refine ⟨1061979149186949903426041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2831944397831866409136109 1061979149186949903426041)
                      ·
                        rfl

theorem cell23_2068197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2068197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068197 prefixEnd_2068197 := by exact prefixLift 2068197
  have htrace : WordTrace (prefixWord ++ tailWord_2068197) baseStart_2068197 baseEnd_2068197 := by
    simpa [prefixWord, tailWord_2068197, baseEnd_2068197] using wordTrace_append hprefix tailTrace_2068197
  have hstable : (prefixWord ++ tailWord_2068197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068197).length < 2 ^ (prefixWord ++ tailWord_2068197).sum := by decide
  have hdescent : baseEnd_2068197 < baseStart_2068197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068257 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2068257 : Nat := 118140960795 + 2068257 * 2 ^ 59
def prefixEnd_2068257 : Nat := 4983230072969 + 3 ^ 40 * 2068257 * 2
def baseEnd_2068257 : Nat := 1062009958026219668675765

theorem tailTrace_2068257 : CollatzResearch.WordTrace tailWord_2068257 prefixEnd_2068257 1062009958026219668675765 := by
  unfold tailWord_2068257
  simp only [CollatzResearch.WordTrace]
  refine ⟨75435530068065594018619025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50290353378710396012412683 75435530068065594018619025)
  ·
    refine ⟨56576647551049195513964269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75435530068065594018619025 56576647551049195513964269)
    ·
      refine ⟨21216242831643448317736601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56576647551049195513964269 21216242831643448317736601)
      ·
        refine ⟨15912182123732586238302451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21216242831643448317736601 15912182123732586238302451)
        ·
          refine ⟨23868273185598879357453677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15912182123732586238302451 23868273185598879357453677)
          ·
            refine ⟨8950602444599579759045129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23868273185598879357453677 8950602444599579759045129)
            ·
              refine ⟨6712951833449684819283847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8950602444599579759045129 6712951833449684819283847)
              ·
                refine ⟨10069427750174527228925771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712951833449684819283847 10069427750174527228925771)
                ·
                  refine ⟨15104141625261790843388657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10069427750174527228925771 15104141625261790843388657)
                  ·
                    refine ⟨11328106218946343132541493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15104141625261790843388657 11328106218946343132541493)
                    ·
                      refine ⟨1062009958026219668675765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11328106218946343132541493 1062009958026219668675765)
                      ·
                        rfl

theorem cell23_2068257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2068257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068257 prefixEnd_2068257 := by exact prefixLift 2068257
  have htrace : WordTrace (prefixWord ++ tailWord_2068257) baseStart_2068257 baseEnd_2068257 := by
    simpa [prefixWord, tailWord_2068257, baseEnd_2068257] using wordTrace_append hprefix tailTrace_2068257
  have hstable : (prefixWord ++ tailWord_2068257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068257).length < 2 ^ (prefixWord ++ tailWord_2068257).sum := by decide
  have hdescent : baseEnd_2068257 < baseStart_2068257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068284 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_2068284 : Nat := 118140960795 + 2068284 * 2 ^ 59
def prefixEnd_2068284 : Nat := 4983230072969 + 3 ^ 40 * 2068284 * 2
def baseEnd_2068284 : Nat := 1062023822003891063038141

theorem tailTrace_2068284 : CollatzResearch.WordTrace tailWord_2068284 prefixEnd_2068284 1062023822003891063038141 := by
  unfold tailWord_2068284
  simp only [CollatzResearch.WordTrace]
  refine ⟨37718257419483888814925953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50291009892645185086567937 37718257419483888814925953)
  ·
    refine ⟨28288693064612916611194465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37718257419483888814925953 28288693064612916611194465)
    ·
      refine ⟨21216519798459687458395849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28288693064612916611194465 21216519798459687458395849)
      ·
        refine ⟨15912389848844765593796887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21216519798459687458395849 15912389848844765593796887)
        ·
          refine ⟨23868584773267148390695331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15912389848844765593796887 23868584773267148390695331)
          ·
            refine ⟨35802877159900722586042997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23868584773267148390695331 35802877159900722586042997)
            ·
              refine ⟨3356519733740692742441531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35802877159900722586042997 3356519733740692742441531)
              ·
                refine ⟨5034779600611039113662297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356519733740692742441531 5034779600611039113662297)
                ·
                  refine ⟨3776084700458279335246723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5034779600611039113662297 3776084700458279335246723)
                  ·
                    refine ⟨5664127050687419002870085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776084700458279335246723 5664127050687419002870085)
                    ·
                      refine ⟨1062023822003891063038141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5664127050687419002870085 1062023822003891063038141)
                      ·
                        rfl

theorem cell23_2068284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_2068284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068284 prefixEnd_2068284 := by exact prefixLift 2068284
  have htrace : WordTrace (prefixWord ++ tailWord_2068284) baseStart_2068284 baseEnd_2068284 := by
    simpa [prefixWord, tailWord_2068284, baseEnd_2068284] using wordTrace_append hprefix tailTrace_2068284
  have hstable : (prefixWord ++ tailWord_2068284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068284).length < 2 ^ (prefixWord ++ tailWord_2068284).sum := by decide
  have hdescent : baseEnd_2068284 < baseStart_2068284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068311 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 3, 4]
def baseStart_2068311 : Nat := 118140960795 + 2068311 * 2 ^ 59
def prefixEnd_2068311 : Nat := 4983230072969 + 3 ^ 40 * 2068311 * 2
def baseEnd_2068311 : Nat := 354012561993854152466839

theorem tailTrace_2068311 : CollatzResearch.WordTrace tailWord_2068311 prefixEnd_2068311 354012561993854152466839 := by
  unfold tailWord_2068311
  simp only [CollatzResearch.WordTrace]
  refine ⟨75437499609869961241084787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50291666406579974160723191 75437499609869961241084787)
  ·
    refine ⟨113156249414804941861627181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75437499609869961241084787 113156249414804941861627181)
    ·
      refine ⟨42433593530551853198110193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113156249414804941861627181 42433593530551853198110193)
      ·
        refine ⟨31825195147913889898582645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42433593530551853198110193 31825195147913889898582645)
        ·
          refine ⟨2983612045116927177992123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31825195147913889898582645 2983612045116927177992123)
          ·
            refine ⟨4475418067675390766988185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983612045116927177992123 4475418067675390766988185)
            ·
              refine ⟨3356563550756543075241139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4475418067675390766988185 3356563550756543075241139)
              ·
                refine ⟨5034845326134814612861709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356563550756543075241139 5034845326134814612861709)
                ·
                  refine ⟨1888066997300555479823141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5034845326134814612861709 1888066997300555479823141)
                  ·
                    refine ⟨354012561993854152466839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888066997300555479823141 354012561993854152466839)
                    ·
                      rfl

theorem cell23_2068311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_2068311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068311 prefixEnd_2068311 := by exact prefixLift 2068311
  have htrace : WordTrace (prefixWord ++ tailWord_2068311) baseStart_2068311 baseEnd_2068311 := by
    simpa [prefixWord, tailWord_2068311, baseEnd_2068311] using wordTrace_append hprefix tailTrace_2068311
  have hstable : (prefixWord ++ tailWord_2068311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068311).length < 2 ^ (prefixWord ++ tailWord_2068311).sum := by decide
  have hdescent : baseEnd_2068311 < baseStart_2068311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068327 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2068327 : Nat := 118140960795 + 2068327 * 2 ^ 59
def prefixEnd_2068327 : Nat := 4983230072969 + 3 ^ 40 * 2068327 * 2
def baseEnd_2068327 : Nat := 1062045901672034394800443

theorem tailTrace_2068327 : CollatzResearch.WordTrace tailWord_2068327 prefixEnd_2068327 1062045901672034394800443 := by
  unfold tailWord_2068327
  simp only [CollatzResearch.WordTrace]
  refine ⟨75438083177811995973667235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50292055451874663982444823 75438083177811995973667235)
  ·
    refine ⟨113157124766717993960500853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75438083177811995973667235 113157124766717993960500853)
    ·
      refine ⟨10608480446879811933796955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113157124766717993960500853 10608480446879811933796955)
      ·
        refine ⟨15912720670319717900695433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608480446879811933796955 15912720670319717900695433)
        ·
          refine ⟨11934540502739788425521575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15912720670319717900695433 11934540502739788425521575)
          ·
            refine ⟨17901810754109682638282363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934540502739788425521575 17901810754109682638282363)
            ·
              refine ⟨26852716131164523957423545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17901810754109682638282363 26852716131164523957423545)
              ·
                refine ⟨20139537098373392968067659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26852716131164523957423545 20139537098373392968067659)
                ·
                  refine ⟨30209305647560089452101489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20139537098373392968067659 30209305647560089452101489)
                  ·
                    refine ⟨22656979235670067089076117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30209305647560089452101489 22656979235670067089076117)
                    ·
                      refine ⟨1062045901672034394800443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22656979235670067089076117 1062045901672034394800443)
                      ·
                        rfl

theorem cell23_2068327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2068327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068327 prefixEnd_2068327 := by exact prefixLift 2068327
  have htrace : WordTrace (prefixWord ++ tailWord_2068327) baseStart_2068327 baseEnd_2068327 := by
    simpa [prefixWord, tailWord_2068327, baseEnd_2068327] using wordTrace_append hprefix tailTrace_2068327
  have hstable : (prefixWord ++ tailWord_2068327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068327).length < 2 ^ (prefixWord ++ tailWord_2068327).sum := by decide
  have hdescent : baseEnd_2068327 < baseStart_2068327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068361 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 2, 3, 2]
def baseStart_2068361 : Nat := 118140960795 + 2068361 * 2 ^ 59
def prefixEnd_2068361 : Nat := 4983230072969 + 3 ^ 40 * 2068361 * 2
def baseEnd_2068361 : Nat := 1062063360014287261775287

theorem tailTrace_2068361 : CollatzResearch.WordTrace tailWord_2068361 prefixEnd_2068361 1062063360014287261775287 := by
  unfold tailWord_2068361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75439323259688819780404937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50292882173125879853603291 75439323259688819780404937)
  ·
    refine ⟨56579492444766614835303703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75439323259688819780404937 56579492444766614835303703)
    ·
      refine ⟨84869238667149922252955555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56579492444766614835303703 84869238667149922252955555)
      ·
        refine ⟨127303858000724883379433333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84869238667149922252955555 127303858000724883379433333)
        ·
          refine ⟨11934736687567957816821875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127303858000724883379433333 11934736687567957816821875)
          ·
            refine ⟨17902105031351936725232813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11934736687567957816821875 17902105031351936725232813)
            ·
              refine ⟨6713289386756976271962305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17902105031351936725232813 6713289386756976271962305)
              ·
                refine ⟨5034967040067732203971729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6713289386756976271962305 5034967040067732203971729)
                ·
                  refine ⟨3776225280050799152978797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5034967040067732203971729 3776225280050799152978797)
                  ·
                    refine ⟨1416084480019049682367049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776225280050799152978797 1416084480019049682367049)
                    ·
                      refine ⟨1062063360014287261775287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416084480019049682367049 1062063360014287261775287)
                      ·
                        rfl

theorem cell23_2068361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 3, 2].length) (baseStart_2068361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068361 prefixEnd_2068361 := by exact prefixLift 2068361
  have htrace : WordTrace (prefixWord ++ tailWord_2068361) baseStart_2068361 baseEnd_2068361 := by
    simpa [prefixWord, tailWord_2068361, baseEnd_2068361] using wordTrace_append hprefix tailTrace_2068361
  have hstable : (prefixWord ++ tailWord_2068361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068361).length < 2 ^ (prefixWord ++ tailWord_2068361).sum := by decide
  have hdescent : baseEnd_2068361 < baseStart_2068361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068391 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2068391 : Nat := 118140960795 + 2068391 * 2 ^ 59
def prefixEnd_2068391 : Nat := 4983230072969 + 3 ^ 40 * 2068391 * 2
def baseEnd_2068391 : Nat := 1062078764433922144400149

theorem tailTrace_2068391 : CollatzResearch.WordTrace tailWord_2068391 prefixEnd_2068391 1062078764433922144400149 := by
  unfold tailWord_2068391
  simp only [CollatzResearch.WordTrace]
  refine ⟨75440417449580134903997027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50293611633053423269331351 75440417449580134903997027)
  ·
    refine ⟨113160626174370202355995541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75440417449580134903997027 113160626174370202355995541)
    ·
      refine ⟨5304404351923603235437291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113160626174370202355995541 5304404351923603235437291)
      ·
        refine ⟨7956606527885404853155937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304404351923603235437291 7956606527885404853155937)
        ·
          refine ⟨5967454895914053639866953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7956606527885404853155937 5967454895914053639866953)
          ·
            refine ⟨4475591171935540229900215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5967454895914053639866953 4475591171935540229900215)
            ·
              refine ⟨6713386757903310344850323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475591171935540229900215 6713386757903310344850323)
              ·
                refine ⟨10070080136854965517275485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6713386757903310344850323 10070080136854965517275485)
                ·
                  refine ⟨3776280051320612068978307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10070080136854965517275485 3776280051320612068978307)
                  ·
                    refine ⟨5664420076980918103467461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776280051320612068978307 5664420076980918103467461)
                    ·
                      refine ⟨1062078764433922144400149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5664420076980918103467461 1062078764433922144400149)
                      ·
                        rfl

theorem cell23_2068391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2068391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068391 prefixEnd_2068391 := by exact prefixLift 2068391
  have htrace : WordTrace (prefixWord ++ tailWord_2068391) baseStart_2068391 baseEnd_2068391 := by
    simpa [prefixWord, tailWord_2068391, baseEnd_2068391] using wordTrace_append hprefix tailTrace_2068391
  have hstable : (prefixWord ++ tailWord_2068391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068391).length < 2 ^ (prefixWord ++ tailWord_2068391).sum := by decide
  have hdescent : baseEnd_2068391 < baseStart_2068391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068427 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 9]
def baseStart_2068427 : Nat := 118140960795 + 2068427 * 2 ^ 59
def prefixEnd_2068427 : Nat := 4983230072969 + 3 ^ 40 * 2068427 * 2
def baseEnd_2068427 : Nat := 354032416579161334516661

theorem tailTrace_2068427 : CollatzResearch.WordTrace tailWord_2068427 prefixEnd_2068427 354032416579161334516661 := by
  unfold tailWord_2068427
  simp only [CollatzResearch.WordTrace]
  refine ⟨75441730477449713052307535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50294486984966475368205023 75441730477449713052307535)
  ·
    refine ⟨113162595716174569578461303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75441730477449713052307535 113162595716174569578461303)
    ·
      refine ⟨169743893574261854367691955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113162595716174569578461303 169743893574261854367691955)
      ·
        refine ⟨254615840361392781551537933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169743893574261854367691955 254615840361392781551537933)
        ·
          refine ⟨95480940135522293081826725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254615840361392781551537933 95480940135522293081826725)
          ·
            refine ⟨17902676275410429952842511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95480940135522293081826725 17902676275410429952842511)
            ·
              refine ⟨26854014413115644929263767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17902676275410429952842511 26854014413115644929263767)
              ·
                refine ⟨40281021619673467393895651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26854014413115644929263767 40281021619673467393895651)
                ·
                  refine ⟨60421532429510201090843477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40281021619673467393895651 60421532429510201090843477)
                  ·
                    refine ⟨354032416579161334516661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60421532429510201090843477 354032416579161334516661)
                    ·
                      rfl

theorem cell23_2068427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 9].length) (baseStart_2068427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068427 prefixEnd_2068427 := by exact prefixLift 2068427
  have htrace : WordTrace (prefixWord ++ tailWord_2068427) baseStart_2068427 baseEnd_2068427 := by
    simpa [prefixWord, tailWord_2068427, baseEnd_2068427] using wordTrace_append hprefix tailTrace_2068427
  have hstable : (prefixWord ++ tailWord_2068427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068427).length < 2 ^ (prefixWord ++ tailWord_2068427).sum := by decide
  have hdescent : baseEnd_2068427 < baseStart_2068427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068486 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2068486 : Nat := 118140960795 + 2068486 * 2 ^ 59
def prefixEnd_2068486 : Nat := 4983230072969 + 3 ^ 40 * 2068486 * 2
def baseEnd_2068486 : Nat := 354042515032033090904071

theorem tailTrace_2068486 : CollatzResearch.WordTrace tailWord_2068486 prefixEnd_2068486 354042515032033090904071 := by
  unfold tailWord_2068486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357621324507373941522041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50295921589490644085803541 2357621324507373941522041)
  ·
    refine ⟨1768215993380530456141531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2357621324507373941522041 1768215993380530456141531)
    ·
      refine ⟨2652323990070795684212297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768215993380530456141531 2652323990070795684212297)
      ·
        refine ⟨1989242992553096763159223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652323990070795684212297 1989242992553096763159223)
        ·
          refine ⟨2983864488829645144738835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989242992553096763159223 2983864488829645144738835)
          ·
            refine ⟨4475796733244467717108253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983864488829645144738835 4475796733244467717108253)
            ·
              refine ⟨1678423774966675393915595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4475796733244467717108253 1678423774966675393915595)
              ·
                refine ⟨2517635662450013090873393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678423774966675393915595 2517635662450013090873393)
                ·
                  refine ⟨1888226746837509818155045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2517635662450013090873393 1888226746837509818155045)
                  ·
                    refine ⟨354042515032033090904071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888226746837509818155045 354042515032033090904071)
                    ·
                      rfl

theorem cell23_2068486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2068486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068486 prefixEnd_2068486 := by exact prefixLift 2068486
  have htrace : WordTrace (prefixWord ++ tailWord_2068486) baseStart_2068486 baseEnd_2068486 := by
    simpa [prefixWord, tailWord_2068486, baseEnd_2068486] using wordTrace_append hprefix tailTrace_2068486
  have hstable : (prefixWord ++ tailWord_2068486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068486).length < 2 ^ (prefixWord ++ tailWord_2068486).sum := by decide
  have hdescent : baseEnd_2068486 < baseStart_2068486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068504 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 7]
def baseStart_2068504 : Nat := 118140960795 + 2068504 * 2 ^ 59
def prefixEnd_2068504 : Nat := 4983230072969 + 3 ^ 40 * 2068504 * 2
def baseEnd_2068504 : Nat := 118015198638653355809681

theorem tailTrace_2068504 : CollatzResearch.WordTrace tailWord_2068504 prefixEnd_2068504 118015198638653355809681 := by
  unfold tailWord_2068504
  simp only [CollatzResearch.WordTrace]
  refine ⟨37722269449085377601430283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50296359265447170135240377 37722269449085377601430283)
  ·
    refine ⟨56583404173628066402145425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37722269449085377601430283 56583404173628066402145425)
    ·
      refine ⟨42437553130221049801609069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56583404173628066402145425 42437553130221049801609069)
      ·
        refine ⟨15914082423832893675603401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42437553130221049801609069 15914082423832893675603401)
        ·
          refine ⟨11935561817874670256702551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15914082423832893675603401 11935561817874670256702551)
          ·
            refine ⟨17903342726812005385053827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935561817874670256702551 17903342726812005385053827)
            ·
              refine ⟨26855014090218008077580741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17903342726812005385053827 26855014090218008077580741)
              ·
                refine ⟨5035315141915876514546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26855014090218008077580741 5035315141915876514546389)
                ·
                  refine ⟨118015198638653355809681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5035315141915876514546389 118015198638653355809681)
                  ·
                    rfl

theorem cell23_2068504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_2068504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068504 prefixEnd_2068504 := by exact prefixLift 2068504
  have htrace : WordTrace (prefixWord ++ tailWord_2068504) baseStart_2068504 baseEnd_2068504 := by
    simpa [prefixWord, tailWord_2068504, baseEnd_2068504] using wordTrace_append hprefix tailTrace_2068504
  have hstable : (prefixWord ++ tailWord_2068504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068504).length < 2 ^ (prefixWord ++ tailWord_2068504).sum := by decide
  have hdescent : baseEnd_2068504 < baseStart_2068504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068544 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_2068544 : Nat := 118140960795 + 2068544 * 2 ^ 59
def prefixEnd_2068544 : Nat := 4983230072969 + 3 ^ 40 * 2068544 * 2
def baseEnd_2068544 : Nat := 1062157326974060045786945

theorem tailTrace_2068544 : CollatzResearch.WordTrace tailWord_2068544 prefixEnd_2068544 1062157326974060045786945 := by
  unfold tailWord_2068544
  simp only [CollatzResearch.WordTrace]
  refine ⟨37722998909012921017158343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50297331878683894689544457 37722998909012921017158343)
  ·
    refine ⟨56584498363519381525737515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37722998909012921017158343 56584498363519381525737515)
    ·
      refine ⟨84876747545279072288606273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56584498363519381525737515 84876747545279072288606273)
      ·
        refine ⟨63657560658959304216454705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84876747545279072288606273 63657560658959304216454705)
        ·
          refine ⟨47743170494219478162341029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63657560658959304216454705 47743170494219478162341029)
          ·
            refine ⟨8951844467666152155438943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47743170494219478162341029 8951844467666152155438943)
            ·
              refine ⟨13427766701499228233158415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951844467666152155438943 13427766701499228233158415)
              ·
                refine ⟨20141650052248842349737623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13427766701499228233158415 20141650052248842349737623)
                ·
                  refine ⟨30212475078373263524606435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20141650052248842349737623 30212475078373263524606435)
                  ·
                    refine ⟨45318712617559895286909653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30212475078373263524606435 45318712617559895286909653)
                    ·
                      refine ⟨1062157326974060045786945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45318712617559895286909653 1062157326974060045786945)
                      ·
                        rfl

theorem cell23_2068544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_2068544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068544 prefixEnd_2068544 := by exact prefixLift 2068544
  have htrace : WordTrace (prefixWord ++ tailWord_2068544) baseStart_2068544 baseEnd_2068544 := by
    simpa [prefixWord, tailWord_2068544, baseEnd_2068544] using wordTrace_append hprefix tailTrace_2068544
  have hstable : (prefixWord ++ tailWord_2068544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068544).length < 2 ^ (prefixWord ++ tailWord_2068544).sum := by decide
  have hdescent : baseEnd_2068544 < baseStart_2068544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068611 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 6]
def baseStart_2068611 : Nat := 118140960795 + 2068611 * 2 ^ 59
def prefixEnd_2068611 : Nat := 4983230072969 + 3 ^ 40 * 2068611 * 2
def baseEnd_2068611 : Nat := 118021303353101253738793

theorem tailTrace_2068611 : CollatzResearch.WordTrace tailWord_2068611 prefixEnd_2068611 118021303353101253738793 := by
  unfold tailWord_2068611
  simp only [CollatzResearch.WordTrace]
  refine ⟨75448441508783112477005687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50298961005855408318003791 75448441508783112477005687)
  ·
    refine ⟨113172662263174668715508531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75448441508783112477005687 113172662263174668715508531)
    ·
      refine ⟨169758993394762003073262797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113172662263174668715508531 169758993394762003073262797)
      ·
        refine ⟨63659622523035751152473549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169758993394762003073262797 63659622523035751152473549)
        ·
          refine ⟨23872358446138406682177581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63659622523035751152473549 23872358446138406682177581)
          ·
            refine ⟨8952134417301902505816593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23872358446138406682177581 8952134417301902505816593)
            ·
              refine ⟨6714100812976426879362445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8952134417301902505816593 6714100812976426879362445)
              ·
                refine ⟨2517787804866160079760917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6714100812976426879362445 2517787804866160079760917)
                ·
                  refine ⟨118021303353101253738793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2517787804866160079760917 118021303353101253738793)
                  ·
                    rfl

theorem cell23_2068611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 6].length) (baseStart_2068611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068611 prefixEnd_2068611 := by exact prefixLift 2068611
  have htrace : WordTrace (prefixWord ++ tailWord_2068611) baseStart_2068611 baseEnd_2068611 := by
    simpa [prefixWord, tailWord_2068611, baseEnd_2068611] using wordTrace_append hprefix tailTrace_2068611
  have hstable : (prefixWord ++ tailWord_2068611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068611).length < 2 ^ (prefixWord ++ tailWord_2068611).sum := by decide
  have hdescent : baseEnd_2068611 < baseStart_2068611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068622 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_2068622 : Nat := 118140960795 + 2068622 * 2 ^ 59
def prefixEnd_2068622 : Nat := 4983230072969 + 3 ^ 40 * 2068622 * 2
def baseEnd_2068622 : Nat := 1062197378465110740611587

theorem tailTrace_2068622 : CollatzResearch.WordTrace tailWord_2068622 prefixEnd_2068622 1062197378465110740611587 := by
  unfold tailWord_2068622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431105338967907669457015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50299228474495507570437413 9431105338967907669457015)
  ·
    refine ⟨14146658008451861504185523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9431105338967907669457015 14146658008451861504185523)
    ·
      refine ⟨21219987012677792256278285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14146658008451861504185523 21219987012677792256278285)
      ·
        refine ⟨7957495129754172096104357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21219987012677792256278285 7957495129754172096104357)
        ·
          refine ⟨1492030336828907268019567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7957495129754172096104357 1492030336828907268019567)
          ·
            refine ⟨2238045505243360902029351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492030336828907268019567 2238045505243360902029351)
            ·
              refine ⟨3357068257865041353044027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238045505243360902029351 3357068257865041353044027)
              ·
                refine ⟨5035602386797562029566041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357068257865041353044027 5035602386797562029566041)
                ·
                  refine ⟨3776701790098171522174531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5035602386797562029566041 3776701790098171522174531)
                  ·
                    refine ⟨5665052685147257283261797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776701790098171522174531 5665052685147257283261797)
                    ·
                      refine ⟨1062197378465110740611587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5665052685147257283261797 1062197378465110740611587)
                      ·
                        rfl

theorem cell23_2068622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_2068622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068622 prefixEnd_2068622 := by exact prefixLift 2068622
  have htrace : WordTrace (prefixWord ++ tailWord_2068622) baseStart_2068622 baseEnd_2068622 := by
    simpa [prefixWord, tailWord_2068622, baseEnd_2068622] using wordTrace_append hprefix tailTrace_2068622
  have hstable : (prefixWord ++ tailWord_2068622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068622).length < 2 ^ (prefixWord ++ tailWord_2068622).sum := by decide
  have hdescent : baseEnd_2068622 < baseStart_2068622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068632 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 1, 4]
def baseStart_2068632 : Nat := 118140960795 + 2068632 * 2 ^ 59
def prefixEnd_2068632 : Nat := 4983230072969 + 3 ^ 40 * 2068632 * 2
def baseEnd_2068632 : Nat := 354067504423885233828847

theorem tailTrace_2068632 : CollatzResearch.WordTrace tailWord_2068632 prefixEnd_2068632 354067504423885233828847 := by
  unfold tailWord_2068632
  simp only [CollatzResearch.WordTrace]
  refine ⟨37724603720853516531760075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50299471627804688709013433 37724603720853516531760075)
  ·
    refine ⟨56586905581280274797640113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37724603720853516531760075 56586905581280274797640113)
    ·
      refine ⟨42440179185960206098230085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56586905581280274797640113 42440179185960206098230085)
      ·
        refine ⟨7957533597367538643418141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42440179185960206098230085 7957533597367538643418141)
        ·
          refine ⟨2984075099012826991281803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7957533597367538643418141 2984075099012826991281803)
          ·
            refine ⟨4476112648519240486922705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984075099012826991281803 4476112648519240486922705)
            ·
              refine ⟨3357084486389430365192029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476112648519240486922705 3357084486389430365192029)
              ·
                refine ⟨1258906682396036386947011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3357084486389430365192029 1258906682396036386947011)
                ·
                  refine ⟨1888360023594054580420517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258906682396036386947011 1888360023594054580420517)
                  ·
                    refine ⟨354067504423885233828847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888360023594054580420517 354067504423885233828847)
                    ·
                      rfl

theorem cell23_2068632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_2068632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068632 prefixEnd_2068632 := by exact prefixLift 2068632
  have htrace : WordTrace (prefixWord ++ tailWord_2068632) baseStart_2068632 baseEnd_2068632 := by
    simpa [prefixWord, tailWord_2068632, baseEnd_2068632] using wordTrace_append hprefix tailTrace_2068632
  have hstable : (prefixWord ++ tailWord_2068632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068632).length < 2 ^ (prefixWord ++ tailWord_2068632).sum := by decide
  have hdescent : baseEnd_2068632 < baseStart_2068632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068712 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_2068712 : Nat := 118140960795 + 2068712 * 2 ^ 59
def prefixEnd_2068712 : Nat := 4983230072969 + 3 ^ 40 * 2068712 * 2
def baseEnd_2068712 : Nat := 1062243591724015388486173

theorem tailTrace_2068712 : CollatzResearch.WordTrace tailWord_2068712 prefixEnd_2068712 1062243591724015388486173 := by
  unfold tailWord_2068712
  simp only [CollatzResearch.WordTrace]
  refine ⟨37726062640708603363216195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50301416854278137817621593 37726062640708603363216195)
  ·
    refine ⟨56589093961062905044824293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37726062640708603363216195 56589093961062905044824293)
    ·
      refine ⟨10610455117699294695904555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56589093961062905044824293 10610455117699294695904555)
      ·
        refine ⟨15915682676548942043856833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10610455117699294695904555 15915682676548942043856833)
        ·
          refine ⟨11936762007411706532892625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15915682676548942043856833 11936762007411706532892625)
          ·
            refine ⟨8952571505558779899669469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11936762007411706532892625 8952571505558779899669469)
            ·
              refine ⟨3357214314584542462376051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8952571505558779899669469 3357214314584542462376051)
              ·
                refine ⟨5035821471876813693564077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357214314584542462376051 5035821471876813693564077)
                ·
                  refine ⟨1888433051953805135086529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5035821471876813693564077 1888433051953805135086529)
                  ·
                    refine ⟨1416324788965353851314897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1888433051953805135086529 1416324788965353851314897)
                    ·
                      refine ⟨1062243591724015388486173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416324788965353851314897 1062243591724015388486173)
                      ·
                        rfl

theorem cell23_2068712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_2068712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068712 prefixEnd_2068712 := by exact prefixLift 2068712
  have htrace : WordTrace (prefixWord ++ tailWord_2068712) baseStart_2068712 baseEnd_2068712 := by
    simpa [prefixWord, tailWord_2068712, baseEnd_2068712] using wordTrace_append hprefix tailTrace_2068712
  have hstable : (prefixWord ++ tailWord_2068712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068712).length < 2 ^ (prefixWord ++ tailWord_2068712).sum := by decide
  have hdescent : baseEnd_2068712 < baseStart_2068712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068722 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_2068722 : Nat := 118140960795 + 2068722 * 2 ^ 59
def prefixEnd_2068722 : Nat := 4983230072969 + 3 ^ 40 * 2068722 * 2
def baseEnd_2068722 : Nat := 354082908843520116453709

theorem tailTrace_2068722 : CollatzResearch.WordTrace tailWord_2068722 prefixEnd_2068722 354082908843520116453709 := by
  unfold tailWord_2068722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863122502845244608574105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50301660007587318956197613 18863122502845244608574105)
  ·
    refine ⟨14147341877133933456430579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18863122502845244608574105 14147341877133933456430579)
    ·
      refine ⟨21221012815700900184645869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14147341877133933456430579 21221012815700900184645869)
      ·
        refine ⟨7957879805887837569242201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21221012815700900184645869 7957879805887837569242201)
        ·
          refine ⟨5968409854415878176931651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7957879805887837569242201 5968409854415878176931651)
          ·
            refine ⟨8952614781623817265397477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968409854415878176931651 8952614781623817265397477)
            ·
              refine ⟨1678615271554465737262027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8952614781623817265397477 1678615271554465737262027)
              ·
                refine ⟨2517922907331698605893041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678615271554465737262027 2517922907331698605893041)
                ·
                  refine ⟨1888442180498773954419781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2517922907331698605893041 1888442180498773954419781)
                  ·
                    refine ⟨354082908843520116453709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888442180498773954419781 354082908843520116453709)
                    ·
                      rfl

theorem cell23_2068722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_2068722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068722 prefixEnd_2068722 := by exact prefixLift 2068722
  have htrace : WordTrace (prefixWord ++ tailWord_2068722) baseStart_2068722 baseEnd_2068722 := by
    simpa [prefixWord, tailWord_2068722, baseEnd_2068722] using wordTrace_append hprefix tailTrace_2068722
  have hstable : (prefixWord ++ tailWord_2068722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068722).length < 2 ^ (prefixWord ++ tailWord_2068722).sum := by decide
  have hdescent : baseEnd_2068722 < baseStart_2068722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068732 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_2068732 : Nat := 118140960795 + 2068732 * 2 ^ 59
def prefixEnd_2068732 : Nat := 4983230072969 + 3 ^ 40 * 2068732 * 2
def baseEnd_2068732 : Nat := 1062253861337105310236081

theorem tailTrace_2068732 : CollatzResearch.WordTrace tailWord_2068732 prefixEnd_2068732 1062253861337105310236081 := by
  unfold tailWord_2068732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37726427370672375071080225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50301903160896500094773633 37726427370672375071080225)
  ·
    refine ⟨28294820528004281303310169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37726427370672375071080225 28294820528004281303310169)
    ·
      refine ⟨21221115396003210977482627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28294820528004281303310169 21221115396003210977482627)
      ·
        refine ⟨31831673094004816466223941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21221115396003210977482627 31831673094004816466223941)
        ·
          refine ⟨5968438705125903087416989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31831673094004816466223941 5968438705125903087416989)
          ·
            refine ⟨2238164514422213657781371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5968438705125903087416989 2238164514422213657781371)
            ·
              refine ⟨3357246771633320486672057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238164514422213657781371 3357246771633320486672057)
              ·
                refine ⟨2517935078724990365004043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3357246771633320486672057 2517935078724990365004043)
                ·
                  refine ⟨3776902618087485547506065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517935078724990365004043 3776902618087485547506065)
                  ·
                    refine ⟨2832676963565614160629549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3776902618087485547506065 2832676963565614160629549)
                    ·
                      refine ⟨1062253861337105310236081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2832676963565614160629549 1062253861337105310236081)
                      ·
                        rfl

theorem cell23_2068732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_2068732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068732 prefixEnd_2068732 := by exact prefixLift 2068732
  have htrace : WordTrace (prefixWord ++ tailWord_2068732) baseStart_2068732 baseEnd_2068732 := by
    simpa [prefixWord, tailWord_2068732, baseEnd_2068732] using wordTrace_append hprefix tailTrace_2068732
  have hstable : (prefixWord ++ tailWord_2068732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068732).length < 2 ^ (prefixWord ++ tailWord_2068732).sum := by decide
  have hdescent : baseEnd_2068732 < baseStart_2068732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068741 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_2068741 : Nat := 118140960795 + 2068741 * 2 ^ 59
def prefixEnd_2068741 : Nat := 4983230072969 + 3 ^ 40 * 2068741 * 2
def baseEnd_2068741 : Nat := 1062258482662995775023539

theorem tailTrace_2068741 : CollatzResearch.WordTrace tailWord_2068741 prefixEnd_2068741 1062258482662995775023539 := by
  unfold tailWord_2068741
  simp only [CollatzResearch.WordTrace]
  refine ⟨75453182998312144679238077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50302121998874763119492051 75453182998312144679238077)
  ·
    refine ⟨28294943624367054254714279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75453182998312144679238077 28294943624367054254714279)
    ·
      refine ⟨42442415436550581382071419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28294943624367054254714279 42442415436550581382071419)
      ·
        refine ⟨63663623154825872073107129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42442415436550581382071419 63663623154825872073107129)
        ·
          refine ⟨47747717366119404054830347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63663623154825872073107129 47747717366119404054830347)
          ·
            refine ⟨71621576049179106082245521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47747717366119404054830347 71621576049179106082245521)
            ·
              refine ⟨53716182036884329561684141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71621576049179106082245521 53716182036884329561684141)
              ·
                refine ⟨20143568263831623585631553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53716182036884329561684141 20143568263831623585631553)
                ·
                  refine ⟨15107676197873717689223665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20143568263831623585631553 15107676197873717689223665)
                  ·
                    refine ⟨11330757148405288266917749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15107676197873717689223665 11330757148405288266917749)
                    ·
                      refine ⟨1062258482662995775023539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11330757148405288266917749 1062258482662995775023539)
                      ·
                        rfl

theorem cell23_2068741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_2068741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068741 prefixEnd_2068741 := by exact prefixLift 2068741
  have htrace : WordTrace (prefixWord ++ tailWord_2068741) baseStart_2068741 baseEnd_2068741 := by
    simpa [prefixWord, tailWord_2068741, baseEnd_2068741] using wordTrace_append hprefix tailTrace_2068741
  have hstable : (prefixWord ++ tailWord_2068741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068741).length < 2 ^ (prefixWord ++ tailWord_2068741).sum := by decide
  have hdescent : baseEnd_2068741 < baseStart_2068741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068751 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_2068751 : Nat := 118140960795 + 2068751 * 2 ^ 59
def prefixEnd_2068751 : Nat := 4983230072969 + 3 ^ 40 * 2068751 * 2
def baseEnd_2068751 : Nat := 1062263617469540735898493

theorem tailTrace_2068751 : CollatzResearch.WordTrace tailWord_2068751 prefixEnd_2068751 1062263617469540735898493 := by
  unfold tailWord_2068751
  simp only [CollatzResearch.WordTrace]
  refine ⟨75453547728275916387102107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50302365152183944258068071 75453547728275916387102107)
  ·
    refine ⟨113180321592413874580653161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75453547728275916387102107 113180321592413874580653161)
    ·
      refine ⟨84885241194310405935489871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113180321592413874580653161 84885241194310405935489871)
      ·
        refine ⟨127327861791465608903234807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84885241194310405935489871 127327861791465608903234807)
        ·
          refine ⟨190991792687198413354852211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127327861791465608903234807 190991792687198413354852211)
          ·
            refine ⟨286487689030797620032278317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190991792687198413354852211 286487689030797620032278317)
            ·
              refine ⟨107432883386549107512104369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286487689030797620032278317 107432883386549107512104369)
              ·
                refine ⟨80574662539911830634078277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107432883386549107512104369 80574662539911830634078277)
                ·
                  refine ⟨15107749226233468243889677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80574662539911830634078277 15107749226233468243889677)
                  ·
                    refine ⟨5665405959837550591458629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15107749226233468243889677 5665405959837550591458629)
                    ·
                      refine ⟨1062263617469540735898493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5665405959837550591458629 1062263617469540735898493)
                      ·
                        rfl

theorem cell23_2068751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_2068751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068751 prefixEnd_2068751 := by exact prefixLift 2068751
  have htrace : WordTrace (prefixWord ++ tailWord_2068751) baseStart_2068751 baseEnd_2068751 := by
    simpa [prefixWord, tailWord_2068751, baseEnd_2068751] using wordTrace_append hprefix tailTrace_2068751
  have hstable : (prefixWord ++ tailWord_2068751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068751).length < 2 ^ (prefixWord ++ tailWord_2068751).sum := by decide
  have hdescent : baseEnd_2068751 < baseStart_2068751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068755 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 1, 3, 2]
def baseStart_2068755 : Nat := 118140960795 + 2068755 * 2 ^ 59
def prefixEnd_2068755 : Nat := 4983230072969 + 3 ^ 40 * 2068755 * 2
def baseEnd_2068755 : Nat := 1062265671392158720248475

theorem tailTrace_2068755 : CollatzResearch.WordTrace tailWord_2068755 prefixEnd_2068755 1062265671392158720248475 := by
  unfold tailWord_2068755
  simp only [CollatzResearch.WordTrace]
  refine ⟨75453693620261425070247719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50302462413507616713498479 75453693620261425070247719)
  ·
    refine ⟨113180540430392137605371579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75453693620261425070247719 113180540430392137605371579)
    ·
      refine ⟨169770810645588206408057369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113180540430392137605371579 169770810645588206408057369)
      ·
        refine ⟨127328107984191154806043027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169770810645588206408057369 127328107984191154806043027)
        ·
          refine ⟨190992161976286732209064541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127328107984191154806043027 190992161976286732209064541)
          ·
            refine ⟨71622060741107524578399203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190992161976286732209064541 71622060741107524578399203)
            ·
              refine ⟨107433091111661286867598805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71622060741107524578399203 107433091111661286867598805)
              ·
                refine ⟨2517963072929561410959347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107433091111661286867598805 2517963072929561410959347)
                ·
                  refine ⟨3776944609394342116439021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517963072929561410959347 3776944609394342116439021)
                  ·
                    refine ⟨1416354228522878293664633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776944609394342116439021 1416354228522878293664633)
                    ·
                      refine ⟨1062265671392158720248475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416354228522878293664633 1062265671392158720248475)
                      ·
                        rfl

theorem cell23_2068755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 3, 2].length) (baseStart_2068755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068755 prefixEnd_2068755 := by exact prefixLift 2068755
  have htrace : WordTrace (prefixWord ++ tailWord_2068755) baseStart_2068755 baseEnd_2068755 := by
    simpa [prefixWord, tailWord_2068755, baseEnd_2068755] using wordTrace_append hprefix tailTrace_2068755
  have hstable : (prefixWord ++ tailWord_2068755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068755).length < 2 ^ (prefixWord ++ tailWord_2068755).sum := by decide
  have hdescent : baseEnd_2068755 < baseStart_2068755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068768 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2068768 : Nat := 118140960795 + 2068768 * 2 ^ 59
def prefixEnd_2068768 : Nat := 4983230072969 + 3 ^ 40 * 2068768 * 2
def baseEnd_2068768 : Nat := 1062272346640667169385915

theorem tailTrace_2068768 : CollatzResearch.WordTrace tailWord_2068768 prefixEnd_2068768 1062272346640667169385915 := by
  unfold tailWord_2068768
  simp only [CollatzResearch.WordTrace]
  refine ⟨37727083884607164145235479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50302778512809552193647305 37727083884607164145235479)
  ·
    refine ⟨56590625826910746217853219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37727083884607164145235479 56590625826910746217853219)
    ·
      refine ⟨84885938740366119326779829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56590625826910746217853219 84885938740366119326779829)
      ·
        refine ⟨7958056756909323686885609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84885938740366119326779829 7958056756909323686885609)
        ·
          refine ⟨5968542567681992765164207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7958056756909323686885609 5968542567681992765164207)
          ·
            refine ⟨8952813851522989147746311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968542567681992765164207 8952813851522989147746311)
            ·
              refine ⟨13429220777284483721619467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8952813851522989147746311 13429220777284483721619467)
              ·
                refine ⟨20143831165926725582429201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13429220777284483721619467 20143831165926725582429201)
                ·
                  refine ⟨15107873374445044186821901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20143831165926725582429201 15107873374445044186821901)
                  ·
                    refine ⟨5665452515416891570058213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15107873374445044186821901 5665452515416891570058213)
                    ·
                      refine ⟨1062272346640667169385915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5665452515416891570058213 1062272346640667169385915)
                      ·
                        rfl

theorem cell23_2068768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2068768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068768 prefixEnd_2068768 := by exact prefixLift 2068768
  have htrace : WordTrace (prefixWord ++ tailWord_2068768) baseStart_2068768 baseEnd_2068768 := by
    simpa [prefixWord, tailWord_2068768, baseEnd_2068768] using wordTrace_append hprefix tailTrace_2068768
  have hstable : (prefixWord ++ tailWord_2068768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068768).length < 2 ^ (prefixWord ++ tailWord_2068768).sum := by decide
  have hdescent : baseEnd_2068768 < baseStart_2068768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068830 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2068830 : Nat := 118140960795 + 2068830 * 2 ^ 59
def prefixEnd_2068830 : Nat := 4983230072969 + 3 ^ 40 * 2068830 * 2
def baseEnd_2068830 : Nat := 1062304182441245926810631

theorem tailTrace_2068830 : CollatzResearch.WordTrace tailWord_2068830 prefixEnd_2068830 1062304182441245926810631 := by
  unfold tailWord_2068830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432053636873714109903493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50304286063326475252818629 9432053636873714109903493)
  ·
    refine ⟨1768510056913821395606905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9432053636873714109903493 1768510056913821395606905)
    ·
      refine ⟨1326382542685366046705179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768510056913821395606905 1326382542685366046705179)
      ·
        refine ⟨1989573814028049070057769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326382542685366046705179 1989573814028049070057769)
        ·
          refine ⟨1492180360521036802543327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989573814028049070057769 1492180360521036802543327)
          ·
            refine ⟨2238270540781555203814991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492180360521036802543327 2238270540781555203814991)
            ·
              refine ⟨3357405811172332805722487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238270540781555203814991 3357405811172332805722487)
              ·
                refine ⟨5036108716758499208583731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357405811172332805722487 5036108716758499208583731)
                ·
                  refine ⟨7554163075137748812875597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036108716758499208583731 7554163075137748812875597)
                  ·
                    refine ⟨2832811153176655804828349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7554163075137748812875597 2832811153176655804828349)
                    ·
                      refine ⟨1062304182441245926810631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2832811153176655804828349 1062304182441245926810631)
                      ·
                        rfl

theorem cell23_2068830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2068830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068830 prefixEnd_2068830 := by exact prefixLift 2068830
  have htrace : WordTrace (prefixWord ++ tailWord_2068830) baseStart_2068830 baseEnd_2068830 := by
    simpa [prefixWord, tailWord_2068830, baseEnd_2068830] using wordTrace_append hprefix tailTrace_2068830
  have hstable : (prefixWord ++ tailWord_2068830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068830).length < 2 ^ (prefixWord ++ tailWord_2068830).sum := by decide
  have hdescent : baseEnd_2068830 < baseStart_2068830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068875 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 4]
def baseStart_2068875 : Nat := 118140960795 + 2068875 * 2 ^ 59
def prefixEnd_2068875 : Nat := 4983230072969 + 3 ^ 40 * 2068875 * 2
def baseEnd_2068875 : Nat := 1062327289070698250747923

theorem tailTrace_2068875 : CollatzResearch.WordTrace tailWord_2068875 prefixEnd_2068875 1062327289070698250747923 := by
  unfold tailWord_2068875
  simp only [CollatzResearch.WordTrace]
  refine ⟨75458070379826685564616079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50305380253217790376410719 75458070379826685564616079)
  ·
    refine ⟨113187105569740028346924119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75458070379826685564616079 113187105569740028346924119)
    ·
      refine ⟨169780658354610042520386179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113187105569740028346924119 169780658354610042520386179)
      ·
        refine ⟨254670987531915063780579269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169780658354610042520386179 254670987531915063780579269)
        ·
          refine ⟨47750810162234074458858613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254670987531915063780579269 47750810162234074458858613)
          ·
            refine ⟨4476638452709444480517995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47750810162234074458858613 4476638452709444480517995)
            ·
              refine ⟨6714957679064166720776993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476638452709444480517995 6714957679064166720776993)
              ·
                refine ⟨5036218259298125040582745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6714957679064166720776993 5036218259298125040582745)
                ·
                  refine ⟨3777163694473593780437059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036218259298125040582745 3777163694473593780437059)
                  ·
                    refine ⟨5665745541710390670655589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777163694473593780437059 5665745541710390670655589)
                    ·
                      refine ⟨1062327289070698250747923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5665745541710390670655589 1062327289070698250747923)
                      ·
                        rfl

theorem cell23_2068875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 4].length) (baseStart_2068875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068875 prefixEnd_2068875 := by exact prefixLift 2068875
  have htrace : WordTrace (prefixWord ++ tailWord_2068875) baseStart_2068875 baseEnd_2068875 := by
    simpa [prefixWord, tailWord_2068875, baseEnd_2068875] using wordTrace_append hprefix tailTrace_2068875
  have hstable : (prefixWord ++ tailWord_2068875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068875).length < 2 ^ (prefixWord ++ tailWord_2068875).sum := by decide
  have hdescent : baseEnd_2068875 < baseStart_2068875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068895 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2068895 : Nat := 118140960795 + 2068895 * 2 ^ 59
def prefixEnd_2068895 : Nat := 4983230072969 + 3 ^ 40 * 2068895 * 2
def baseEnd_2068895 : Nat := 1062337558683788172497831

theorem tailTrace_2068895 : CollatzResearch.WordTrace tailWord_2068895 prefixEnd_2068895 1062337558683788172497831 := by
  unfold tailWord_2068895
  simp only [CollatzResearch.WordTrace]
  refine ⟨75458799839754228980344139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50305866559836152653562759 75458799839754228980344139)
  ·
    refine ⟨113188199759631343470516209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75458799839754228980344139 113188199759631343470516209)
    ·
      refine ⟨84891149819723507602887157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113188199759631343470516209 84891149819723507602887157)
      ·
        refine ⟨7958545295599078837770671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84891149819723507602887157 7958545295599078837770671)
        ·
          refine ⟨11937817943398618256656007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7958545295599078837770671 11937817943398618256656007)
          ·
            refine ⟨17906726915097927384984011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11937817943398618256656007 17906726915097927384984011)
            ·
              refine ⟨26860090372646891077476017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17906726915097927384984011 26860090372646891077476017)
              ·
                refine ⟨20145067779485168308107013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26860090372646891077476017 20145067779485168308107013)
                ·
                  refine ⟨3777200208653469057770065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20145067779485168308107013 3777200208653469057770065)
                  ·
                    refine ⟨2832900156490101793327549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3777200208653469057770065 2832900156490101793327549)
                    ·
                      refine ⟨1062337558683788172497831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2832900156490101793327549 1062337558683788172497831)
                      ·
                        rfl

theorem cell23_2068895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2068895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068895 prefixEnd_2068895 := by exact prefixLift 2068895
  have htrace : WordTrace (prefixWord ++ tailWord_2068895) baseStart_2068895 baseEnd_2068895 := by
    simpa [prefixWord, tailWord_2068895, baseEnd_2068895] using wordTrace_append hprefix tailTrace_2068895
  have hstable : (prefixWord ++ tailWord_2068895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068895).length < 2 ^ (prefixWord ++ tailWord_2068895).sum := by decide
  have hdescent : baseEnd_2068895 < baseStart_2068895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068906 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2068906 : Nat := 118140960795 + 2068906 * 2 ^ 59
def prefixEnd_2068906 : Nat := 4983230072969 + 3 ^ 40 * 2068906 * 2
def baseEnd_2068906 : Nat := 354114402323662543153427

theorem tailTrace_2068906 : CollatzResearch.WordTrace tailWord_2068906 prefixEnd_2068906 354114402323662543153427 := by
  unfold tailWord_2068906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864800260678594464748643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50306134028476251905996381 18864800260678594464748643)
  ·
    refine ⟨28297200391017891697122965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18864800260678594464748643 28297200391017891697122965)
    ·
      refine ⟨1326431268328963673302639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28297200391017891697122965 1326431268328963673302639)
      ·
        refine ⟨1989646902493445509953959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326431268328963673302639 1989646902493445509953959)
        ·
          refine ⟨2984470353740168264930939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989646902493445509953959 2984470353740168264930939)
          ·
            refine ⟨4476705530610252397396409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984470353740168264930939 4476705530610252397396409)
            ·
              refine ⟨3357529147957689298047307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476705530610252397396409 3357529147957689298047307)
              ·
                refine ⟨5036293721936533947070961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357529147957689298047307 5036293721936533947070961)
                ·
                  refine ⟨3777220291452400460303221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036293721936533947070961 3777220291452400460303221)
                  ·
                    refine ⟨354114402323662543153427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3777220291452400460303221 354114402323662543153427)
                    ·
                      rfl

theorem cell23_2068906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2068906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068906 prefixEnd_2068906 := by exact prefixLift 2068906
  have htrace : WordTrace (prefixWord ++ tailWord_2068906) baseStart_2068906 baseEnd_2068906 := by
    simpa [prefixWord, tailWord_2068906, baseEnd_2068906] using wordTrace_append hprefix tailTrace_2068906
  have hstable : (prefixWord ++ tailWord_2068906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068906).length < 2 ^ (prefixWord ++ tailWord_2068906).sum := by decide
  have hdescent : baseEnd_2068906 < baseStart_2068906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068909 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2068909 : Nat := 118140960795 + 2068909 * 2 ^ 59
def prefixEnd_2068909 : Nat := 4983230072969 + 3 ^ 40 * 2068909 * 2
def baseEnd_2068909 : Nat := 1062344747412951117722767

theorem tailTrace_2068909 : CollatzResearch.WordTrace tailWord_2068909 prefixEnd_2068909 1062344747412951117722767 := by
  unfold tailWord_2068909
  simp only [CollatzResearch.WordTrace]
  refine ⟨75459310461703509371353781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50306206974469006247569187 75459310461703509371353781)
  ·
    refine ⟨7074310355784704003564417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75459310461703509371353781 7074310355784704003564417)
    ·
      refine ⟨5305732766838528002673313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7074310355784704003564417 5305732766838528002673313)
      ·
        refine ⟨3979299575128896002004985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5305732766838528002673313 3979299575128896002004985)
        ·
          refine ⟨2984474681346672001503739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979299575128896002004985 2984474681346672001503739)
          ·
            refine ⟨4476712022020008002255609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984474681346672001503739 4476712022020008002255609)
            ·
              refine ⟨3357534016515006001691707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476712022020008002255609 3357534016515006001691707)
              ·
                refine ⟨5036301024772509002537561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357534016515006001691707 5036301024772509002537561)
                ·
                  refine ⟨3777225768579381751903171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5036301024772509002537561 3777225768579381751903171)
                  ·
                    refine ⟨5665838652869072627854757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3777225768579381751903171 5665838652869072627854757)
                    ·
                      refine ⟨1062344747412951117722767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5665838652869072627854757 1062344747412951117722767)
                      ·
                        rfl

theorem cell23_2068909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2068909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068909 prefixEnd_2068909 := by exact prefixLift 2068909
  have htrace : WordTrace (prefixWord ++ tailWord_2068909) baseStart_2068909 baseEnd_2068909 := by
    simpa [prefixWord, tailWord_2068909, baseEnd_2068909] using wordTrace_append hprefix tailTrace_2068909
  have hstable : (prefixWord ++ tailWord_2068909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068909).length < 2 ^ (prefixWord ++ tailWord_2068909).sum := by decide
  have hdescent : baseEnd_2068909 < baseStart_2068909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068936 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 1, 4]
def baseStart_2068936 : Nat := 118140960795 + 2068936 * 2 ^ 59
def prefixEnd_2068936 : Nat := 4983230072969 + 3 ^ 40 * 2068936 * 2
def baseEnd_2068936 : Nat := 354119537130207504028381

theorem tailTrace_2068936 : CollatzResearch.WordTrace tailWord_2068936 prefixEnd_2068936 354119537130207504028381 := by
  unfold tailWord_2068936
  simp only [CollatzResearch.WordTrace]
  refine ⟨37730147616302846491293331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50306863488403795321724441 37730147616302846491293331)
  ·
    refine ⟨56595221424454269736939997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37730147616302846491293331 56595221424454269736939997)
    ·
      refine ⟨21223208034170351151352499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56595221424454269736939997 21223208034170351151352499)
      ·
        refine ⟨31834812051255526727028749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21223208034170351151352499 31834812051255526727028749)
        ·
          refine ⟨11938054519220822522635781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31834812051255526727028749 11938054519220822522635781)
          ·
            refine ⟨2238385222353904222994209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11938054519220822522635781 2238385222353904222994209)
            ·
              refine ⟨1678788916765428167245657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238385222353904222994209 1678788916765428167245657)
              ·
                refine ⟨1259091687574071125434243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678788916765428167245657 1259091687574071125434243)
                ·
                  refine ⟨1888637531361106688151365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259091687574071125434243 1888637531361106688151365)
                  ·
                    refine ⟨354119537130207504028381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888637531361106688151365 354119537130207504028381)
                    ·
                      rfl

theorem cell23_2068936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_2068936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068936 prefixEnd_2068936 := by exact prefixLift 2068936
  have htrace : WordTrace (prefixWord ++ tailWord_2068936) baseStart_2068936 baseEnd_2068936 := by
    simpa [prefixWord, tailWord_2068936, baseEnd_2068936] using wordTrace_append hprefix tailTrace_2068936
  have hstable : (prefixWord ++ tailWord_2068936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068936).length < 2 ^ (prefixWord ++ tailWord_2068936).sum := by decide
  have hdescent : baseEnd_2068936 < baseStart_2068936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068942 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_2068942 : Nat := 118140960795 + 2068942 * 2 ^ 59
def prefixEnd_2068942 : Nat := 4983230072969 + 3 ^ 40 * 2068942 * 2
def baseEnd_2068942 : Nat := 1062361692274549488610115

theorem tailTrace_2068942 : CollatzResearch.WordTrace tailWord_2068942 prefixEnd_2068942 1062361692274549488610115 := by
  unfold tailWord_2068942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432564258822994500913135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50307009380389304004870053 9432564258822994500913135)
  ·
    refine ⟨14148846388234491751369703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9432564258822994500913135 14148846388234491751369703)
    ·
      refine ⟨21223269582351737627054555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14148846388234491751369703 21223269582351737627054555)
      ·
        refine ⟨31834904373527606440581833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21223269582351737627054555 31834904373527606440581833)
        ·
          refine ⟨23876178280145704830436375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31834904373527606440581833 23876178280145704830436375)
          ·
            refine ⟨35814267420218557245654563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23876178280145704830436375 35814267420218557245654563)
            ·
              refine ⟨53721401130327835868481845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35814267420218557245654563 53721401130327835868481845)
              ·
                refine ⟨5036381355968234612670173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53721401130327835868481845 5036381355968234612670173)
                ·
                  refine ⟨1888643008488087979751315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5036381355968234612670173 1888643008488087979751315)
                  ·
                    refine ⟨2832964512732131969626973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1888643008488087979751315 2832964512732131969626973)
                    ·
                      refine ⟨1062361692274549488610115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2832964512732131969626973 1062361692274549488610115)
                      ·
                        rfl

theorem cell23_2068942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_2068942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068942 prefixEnd_2068942 := by exact prefixLift 2068942
  have htrace : WordTrace (prefixWord ++ tailWord_2068942) baseStart_2068942 baseEnd_2068942 := by
    simpa [prefixWord, tailWord_2068942, baseEnd_2068942] using wordTrace_append hprefix tailTrace_2068942
  have hstable : (prefixWord ++ tailWord_2068942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068942).length < 2 ^ (prefixWord ++ tailWord_2068942).sum := by decide
  have hdescent : baseEnd_2068942 < baseStart_2068942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068975 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 4, 4]
def baseStart_2068975 : Nat := 118140960795 + 2068975 * 2 ^ 59
def prefixEnd_2068975 : Nat := 4983230072969 + 3 ^ 40 * 2068975 * 2
def baseEnd_2068975 : Nat := 354126212378715953165821

theorem tailTrace_2068975 : CollatzResearch.WordTrace tailWord_2068975 prefixEnd_2068975 354126212378715953165821 := by
  unfold tailWord_2068975
  simp only [CollatzResearch.WordTrace]
  refine ⟨75461717679464402643256379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50307811786309601762170919 75461717679464402643256379)
  ·
    refine ⟨113192576519196603964884569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75461717679464402643256379 113192576519196603964884569)
    ·
      refine ⟨84894432389397452973663427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113192576519196603964884569 84894432389397452973663427)
      ·
        refine ⟨127341648584096179460495141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84894432389397452973663427 127341648584096179460495141)
        ·
          refine ⟨23876559109518033648842839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127341648584096179460495141 23876559109518033648842839)
          ·
            refine ⟨35814838664277050473264259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23876559109518033648842839 35814838664277050473264259)
            ·
              refine ⟨53722257996415575709896389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35814838664277050473264259 53722257996415575709896389)
              ·
                refine ⟨10072923374327920445605573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53722257996415575709896389 10072923374327920445605573)
                ·
                  refine ⟨1888673132686485083551045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10072923374327920445605573 1888673132686485083551045)
                  ·
                    refine ⟨354126212378715953165821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1888673132686485083551045 354126212378715953165821)
                    ·
                      rfl

theorem cell23_2068975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_2068975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2068975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2068975 prefixEnd_2068975 := by exact prefixLift 2068975
  have htrace : WordTrace (prefixWord ++ tailWord_2068975) baseStart_2068975 baseEnd_2068975 := by
    simpa [prefixWord, tailWord_2068975, baseEnd_2068975] using wordTrace_append hprefix tailTrace_2068975
  have hstable : (prefixWord ++ tailWord_2068975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068975).length < 2 ^ (prefixWord ++ tailWord_2068975).sum := by decide
  have hdescent : baseEnd_2068975 < baseStart_2068975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069008 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_2069008 : Nat := 118140960795 + 2069008 * 2 ^ 59
def prefixEnd_2069008 : Nat := 4983230072969 + 3 ^ 40 * 2069008 * 2
def baseEnd_2069008 : Nat := 1062395581997746230384811

theorem tailTrace_2069008 : CollatzResearch.WordTrace tailWord_2069008 prefixEnd_2069008 1062395581997746230384811 := by
  unfold tailWord_2069008
  simp only [CollatzResearch.WordTrace]
  refine ⟨37731460644172424639603839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50308614192229899519471785 37731460644172424639603839)
  ·
    refine ⟨56597190966258636959405759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37731460644172424639603839 56597190966258636959405759)
    ·
      refine ⟨84895786449387955439108639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56597190966258636959405759 84895786449387955439108639)
      ·
        refine ⟨127343679674081933158662959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84895786449387955439108639 127343679674081933158662959)
        ·
          refine ⟨191015519511122899737994439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127343679674081933158662959 191015519511122899737994439)
          ·
            refine ⟨286523279266684349606991659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191015519511122899737994439 286523279266684349606991659)
            ·
              refine ⟨429784918900026524410487489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286523279266684349606991659 429784918900026524410487489)
              ·
                refine ⟨322338689175019893307865617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429784918900026524410487489 322338689175019893307865617)
                ·
                  refine ⟨241754016881264919980899213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322338689175019893307865617 241754016881264919980899213)
                  ·
                    refine ⟨90657756330474344992837205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241754016881264919980899213 90657756330474344992837205)
                    ·
                      refine ⟨1062395581997746230384811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 90657756330474344992837205 1062395581997746230384811)
                      ·
                        rfl

theorem cell23_2069008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_2069008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069008 prefixEnd_2069008 := by exact prefixLift 2069008
  have htrace : WordTrace (prefixWord ++ tailWord_2069008) baseStart_2069008 baseEnd_2069008 := by
    simpa [prefixWord, tailWord_2069008, baseEnd_2069008] using wordTrace_append hprefix tailTrace_2069008
  have hstable : (prefixWord ++ tailWord_2069008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069008).length < 2 ^ (prefixWord ++ tailWord_2069008).sum := by decide
  have hdescent : baseEnd_2069008 < baseStart_2069008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069045 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2069045 : Nat := 118140960795 + 2069045 * 2 ^ 59
def prefixEnd_2069045 : Nat := 4983230072969 + 3 ^ 40 * 2069045 * 2
def baseEnd_2069045 : Nat := 1062414580781962585622141

theorem tailTrace_2069045 : CollatzResearch.WordTrace tailWord_2069045 prefixEnd_2069045 1062414580781962585622141 := by
  unfold tailWord_2069045
  simp only [CollatzResearch.WordTrace]
  refine ⟨75464270789210804598304589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50309513859473869732203059 75464270789210804598304589)
  ·
    refine ⟨28299101545954051724364221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75464270789210804598304589 28299101545954051724364221)
    ·
      refine ⟨10612163079732769396636583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28299101545954051724364221 10612163079732769396636583)
      ·
        refine ⟨15918244619599154094954875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612163079732769396636583 15918244619599154094954875)
        ·
          refine ⟨23877366929398731142432313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918244619599154094954875 23877366929398731142432313)
          ·
            refine ⟨17908025197049048356824235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23877366929398731142432313 17908025197049048356824235)
            ·
              refine ⟨26862037795573572535236353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17908025197049048356824235 26862037795573572535236353)
              ·
                refine ⟨20146528346680179401427265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26862037795573572535236353 20146528346680179401427265)
                ·
                  refine ⟨15109896260010134551070449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20146528346680179401427265 15109896260010134551070449)
                  ·
                    refine ⟨11332422195007600913302837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15109896260010134551070449 11332422195007600913302837)
                    ·
                      refine ⟨1062414580781962585622141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11332422195007600913302837 1062414580781962585622141)
                      ·
                        rfl

theorem cell23_2069045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2069045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069045 prefixEnd_2069045 := by exact prefixLift 2069045
  have htrace : WordTrace (prefixWord ++ tailWord_2069045) baseStart_2069045 baseEnd_2069045 := by
    simpa [prefixWord, tailWord_2069045, baseEnd_2069045] using wordTrace_append hprefix tailTrace_2069045
  have hstable : (prefixWord ++ tailWord_2069045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069045).length < 2 ^ (prefixWord ++ tailWord_2069045).sum := by decide
  have hdescent : baseEnd_2069045 < baseStart_2069045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069049 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2069049 : Nat := 118140960795 + 2069049 * 2 ^ 59
def prefixEnd_2069049 : Nat := 4983230072969 + 3 ^ 40 * 2069049 * 2
def baseEnd_2069049 : Nat := 1062416634704580569972123

theorem tailTrace_2069049 : CollatzResearch.WordTrace tailWord_2069049 prefixEnd_2069049 1062416634704580569972123 := by
  unfold tailWord_2069049
  simp only [CollatzResearch.WordTrace]
  refine ⟨75464416681196313281450201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50309611120797542187633467 75464416681196313281450201)
  ·
    refine ⟨56598312510897234961087651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75464416681196313281450201 56598312510897234961087651)
    ·
      refine ⟨84897468766345852441631477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56598312510897234961087651 84897468766345852441631477)
      ·
        refine ⟨7959137696844923666402951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84897468766345852441631477 7959137696844923666402951)
        ·
          refine ⟨11938706545267385499604427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7959137696844923666402951 11938706545267385499604427)
          ·
            refine ⟨17908059817901078249406641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11938706545267385499604427 17908059817901078249406641)
            ·
              refine ⟨13431044863425808687054981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17908059817901078249406641 13431044863425808687054981)
              ·
                refine ⟨2518320911892339128822809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13431044863425808687054981 2518320911892339128822809)
                ·
                  refine ⟨1888740683919254346617107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518320911892339128822809 1888740683919254346617107)
                  ·
                    refine ⟨2833111025878881519925661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1888740683919254346617107 2833111025878881519925661)
                    ·
                      refine ⟨1062416634704580569972123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2833111025878881519925661 1062416634704580569972123)
                      ·
                        rfl

theorem cell23_2069049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2069049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069049 prefixEnd_2069049 := by exact prefixLift 2069049
  have htrace : WordTrace (prefixWord ++ tailWord_2069049) baseStart_2069049 baseEnd_2069049 := by
    simpa [prefixWord, tailWord_2069049, baseEnd_2069049] using wordTrace_append hprefix tailTrace_2069049
  have hstable : (prefixWord ++ tailWord_2069049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069049).length < 2 ^ (prefixWord ++ tailWord_2069049).sum := by decide
  have hdescent : baseEnd_2069049 < baseStart_2069049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069055 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_2069055 : Nat := 118140960795 + 2069055 * 2 ^ 59
def prefixEnd_2069055 : Nat := 4983230072969 + 3 ^ 40 * 2069055 * 2
def baseEnd_2069055 : Nat := 1062419715588507546497095

theorem tailTrace_2069055 : CollatzResearch.WordTrace tailWord_2069055 prefixEnd_2069055 1062419715588507546497095 := by
  unfold tailWord_2069055
  simp only [CollatzResearch.WordTrace]
  refine ⟨75464635519174576306168619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50309757012783050870779079 75464635519174576306168619)
  ·
    refine ⟨113196953278761864459252929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75464635519174576306168619 113196953278761864459252929)
    ·
      refine ⟨84897714959071398344439697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113196953278761864459252929 84897714959071398344439697)
      ·
        refine ⟨63673286219303548758329773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84897714959071398344439697 63673286219303548758329773)
        ·
          refine ⟨23877482332238830784373665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63673286219303548758329773 23877482332238830784373665)
          ·
            refine ⟨17908111749179123088280249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23877482332238830784373665 17908111749179123088280249)
            ·
              refine ⟨13431083811884342316210187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17908111749179123088280249 13431083811884342316210187)
              ·
                refine ⟨20146625717826513474315281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13431083811884342316210187 20146625717826513474315281)
                ·
                  refine ⟨15109969288369885105736461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20146625717826513474315281 15109969288369885105736461)
                  ·
                    refine ⟨5666238483138706914651173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15109969288369885105736461 5666238483138706914651173)
                    ·
                      refine ⟨1062419715588507546497095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5666238483138706914651173 1062419715588507546497095)
                      ·
                        rfl

theorem cell23_2069055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_2069055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069055 prefixEnd_2069055 := by exact prefixLift 2069055
  have htrace : WordTrace (prefixWord ++ tailWord_2069055) baseStart_2069055 baseEnd_2069055 := by
    simpa [prefixWord, tailWord_2069055, baseEnd_2069055] using wordTrace_append hprefix tailTrace_2069055
  have hstable : (prefixWord ++ tailWord_2069055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069055).length < 2 ^ (prefixWord ++ tailWord_2069055).sum := by decide
  have hdescent : baseEnd_2069055 < baseStart_2069055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069066 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_2069066 : Nat := 118140960795 + 2069066 * 2 ^ 59
def prefixEnd_2069066 : Nat := 4983230072969 + 3 ^ 40 * 2069066 * 2
def baseEnd_2069066 : Nat := 1062425363875707003459545

theorem tailTrace_2069066 : CollatzResearch.WordTrace tailWord_2069066 prefixEnd_2069066 1062425363875707003459545 := by
  unfold tailWord_2069066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18866259180533681296204763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50310024481423150123212701 18866259180533681296204763)
  ·
    refine ⟨28299388770800521944307145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18866259180533681296204763 28299388770800521944307145)
    ·
      refine ⟨21224541578100391458230359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28299388770800521944307145 21224541578100391458230359)
      ·
        refine ⟨31836812367150587187345539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21224541578100391458230359 31836812367150587187345539)
        ·
          refine ⟨47755218550725880781018309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31836812367150587187345539 47755218550725880781018309)
          ·
            refine ⟨8954103478261102646440933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47755218550725880781018309 8954103478261102646440933)
            ·
              refine ⟨1678894402173956746207675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8954103478261102646440933 1678894402173956746207675)
              ·
                refine ⟨2518341603260935119311513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678894402173956746207675 2518341603260935119311513)
                ·
                  refine ⟨1888756202445701339483635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518341603260935119311513 1888756202445701339483635)
                  ·
                    refine ⟨2833134303668552009225453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1888756202445701339483635 2833134303668552009225453)
                    ·
                      refine ⟨1062425363875707003459545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2833134303668552009225453 1062425363875707003459545)
                      ·
                        rfl

theorem cell23_2069066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_2069066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069066 prefixEnd_2069066 := by exact prefixLift 2069066
  have htrace : WordTrace (prefixWord ++ tailWord_2069066) baseStart_2069066 baseEnd_2069066 := by
    simpa [prefixWord, tailWord_2069066, baseEnd_2069066] using wordTrace_append hprefix tailTrace_2069066
  have hstable : (prefixWord ++ tailWord_2069066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069066).length < 2 ^ (prefixWord ++ tailWord_2069066).sum := by decide
  have hdescent : baseEnd_2069066 < baseStart_2069066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069076 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_2069076 : Nat := 118140960795 + 2069076 * 2 ^ 59
def prefixEnd_2069076 : Nat := 4983230072969 + 3 ^ 40 * 2069076 * 2
def baseEnd_2069076 : Nat := 1062430498682251964334499

theorem tailTrace_2069076 : CollatzResearch.WordTrace tailWord_2069076 prefixEnd_2069076 1062430498682251964334499 := by
  unfold tailWord_2069076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37732700726049248446341541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50310267634732331261788721 37732700726049248446341541)
  ·
    refine ⟨7074881386134234083689039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37732700726049248446341541 7074881386134234083689039)
    ·
      refine ⟨10612322079201351125533559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7074881386134234083689039 10612322079201351125533559)
      ·
        refine ⟨15918483118802026688300339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612322079201351125533559 15918483118802026688300339)
        ·
          refine ⟨23877724678203040032450509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15918483118802026688300339 23877724678203040032450509)
          ·
            refine ⟨8954146754326140012168941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23877724678203040032450509 8954146754326140012168941)
            ·
              refine ⟨3357805032872302504563353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8954146754326140012168941 3357805032872302504563353)
              ·
                refine ⟨2518353774654226878422515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3357805032872302504563353 2518353774654226878422515)
                ·
                  refine ⟨3777530661981340317633773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518353774654226878422515 3777530661981340317633773)
                  ·
                    refine ⟨1416573998243002619112665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777530661981340317633773 1416573998243002619112665)
                    ·
                      refine ⟨1062430498682251964334499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416573998243002619112665 1062430498682251964334499)
                      ·
                        rfl

theorem cell23_2069076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_2069076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069076 prefixEnd_2069076 := by exact prefixLift 2069076
  have htrace : WordTrace (prefixWord ++ tailWord_2069076) baseStart_2069076 baseEnd_2069076 := by
    simpa [prefixWord, tailWord_2069076, baseEnd_2069076] using wordTrace_append hprefix tailTrace_2069076
  have hstable : (prefixWord ++ tailWord_2069076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069076).length < 2 ^ (prefixWord ++ tailWord_2069076).sum := by decide
  have hdescent : baseEnd_2069076 < baseStart_2069076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069089 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_2069089 : Nat := 118140960795 + 2069089 * 2 ^ 59
def prefixEnd_2069089 : Nat := 4983230072969 + 3 ^ 40 * 2069089 * 2
def baseEnd_2069089 : Nat := 1062437173930760413471939

theorem tailTrace_2069089 : CollatzResearch.WordTrace tailWord_2069089 prefixEnd_2069089 1062437173930760413471939 := by
  unfold tailWord_2069089
  simp only [CollatzResearch.WordTrace]
  refine ⟨75465875601051400112906321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50310583734034266741937547 75465875601051400112906321)
  ·
    refine ⟨56599406700788550084679741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75465875601051400112906321 56599406700788550084679741)
    ·
      refine ⟨21224777512795706281754903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56599406700788550084679741 21224777512795706281754903)
      ·
        refine ⟨31837166269193559422632355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21224777512795706281754903 31837166269193559422632355)
        ·
          refine ⟨47755749403790339133948533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31837166269193559422632355 47755749403790339133948533)
          ·
            refine ⟨4477101506605344293807675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47755749403790339133948533 4477101506605344293807675)
            ·
              refine ⟨6715652259908016440711513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477101506605344293807675 6715652259908016440711513)
              ·
                refine ⟨5036739194931012330533635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6715652259908016440711513 5036739194931012330533635)
                ·
                  refine ⟨7555108792396518495800453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5036739194931012330533635 7555108792396518495800453)
                  ·
                    refine ⟨1416582898574347217962585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7555108792396518495800453 1416582898574347217962585)
                    ·
                      refine ⟨1062437173930760413471939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416582898574347217962585 1062437173930760413471939)
                      ·
                        rfl

theorem cell23_2069089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_2069089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069089 prefixEnd_2069089 := by exact prefixLift 2069089
  have htrace : WordTrace (prefixWord ++ tailWord_2069089) baseStart_2069089 baseEnd_2069089 := by
    simpa [prefixWord, tailWord_2069089, baseEnd_2069089] using wordTrace_append hprefix tailTrace_2069089
  have hstable : (prefixWord ++ tailWord_2069089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069089).length < 2 ^ (prefixWord ++ tailWord_2069089).sum := by decide
  have hdescent : baseEnd_2069089 < baseStart_2069089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069093 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 1, 3, 2]
def baseStart_2069093 : Nat := 118140960795 + 2069093 * 2 ^ 59
def prefixEnd_2069093 : Nat := 4983230072969 + 3 ^ 40 * 2069093 * 2
def baseEnd_2069093 : Nat := 1062439227853378397821921

theorem tailTrace_2069093 : CollatzResearch.WordTrace tailWord_2069093 prefixEnd_2069093 1062439227853378397821921 := by
  unfold tailWord_2069093
  simp only [CollatzResearch.WordTrace]
  refine ⟨75466021493036908796051933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50310680995357939197367955 75466021493036908796051933)
  ·
    refine ⟨28299758059888840798519475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75466021493036908796051933 28299758059888840798519475)
    ·
      refine ⟨42449637089833261197779213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28299758059888840798519475 42449637089833261197779213)
      ·
        refine ⟨15918613908687472949167205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42449637089833261197779213 15918613908687472949167205)
        ·
          refine ⟨2984740107878901177968851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15918613908687472949167205 2984740107878901177968851)
          ·
            refine ⟨4477110161818351766953277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984740107878901177968851 4477110161818351766953277)
            ·
              refine ⟨1678916310681881912607479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4477110161818351766953277 1678916310681881912607479)
              ·
                refine ⟨2518374466022822868911219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678916310681881912607479 2518374466022822868911219)
                ·
                  refine ⟨3777561699034234303366829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518374466022822868911219 3777561699034234303366829)
                  ·
                    refine ⟨1416585637137837863762561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777561699034234303366829 1416585637137837863762561)
                    ·
                      refine ⟨1062439227853378397821921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416585637137837863762561 1062439227853378397821921)
                      ·
                        rfl

theorem cell23_2069093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_2069093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069093 prefixEnd_2069093 := by exact prefixLift 2069093
  have htrace : WordTrace (prefixWord ++ tailWord_2069093) baseStart_2069093 baseEnd_2069093 := by
    simpa [prefixWord, tailWord_2069093, baseEnd_2069093] using wordTrace_append hprefix tailTrace_2069093
  have hstable : (prefixWord ++ tailWord_2069093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069093).length < 2 ^ (prefixWord ++ tailWord_2069093).sum := by decide
  have hdescent : baseEnd_2069093 < baseStart_2069093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069112 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 5]
def baseStart_2069112 : Nat := 118140960795 + 2069112 * 2 ^ 59
def prefixEnd_2069112 : Nat := 4983230072969 + 3 ^ 40 * 2069112 * 2
def baseEnd_2069112 : Nat := 118049887109534869276037

theorem tailTrace_2069112 : CollatzResearch.WordTrace tailWord_2069112 prefixEnd_2069112 118049887109534869276037 := by
  unfold tailWord_2069112
  simp only [CollatzResearch.WordTrace]
  refine ⟨37733357239984037520496795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50311142986645383360662393 37733357239984037520496795)
  ·
    refine ⟨56600035859976056280745193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37733357239984037520496795 56600035859976056280745193)
    ·
      refine ⟨42450026894982042210558895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56600035859976056280745193 42450026894982042210558895)
      ·
        refine ⟨63675040342473063315838343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42450026894982042210558895 63675040342473063315838343)
        ·
          refine ⟨95512560513709594973757515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63675040342473063315838343 95512560513709594973757515)
          ·
            refine ⟨143268840770564392460636273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95512560513709594973757515 143268840770564392460636273)
            ·
              refine ⟨107451630577923294345477205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143268840770564392460636273 107451630577923294345477205)
              ·
                refine ⟨1259198795835038605611061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 107451630577923294345477205 1259198795835038605611061)
                ·
                  refine ⟨118049887109534869276037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1259198795835038605611061 118049887109534869276037)
                  ·
                    rfl

theorem cell23_2069112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 5].length) (baseStart_2069112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069112 prefixEnd_2069112 := by exact prefixLift 2069112
  have htrace : WordTrace (prefixWord ++ tailWord_2069112) baseStart_2069112 baseEnd_2069112 := by
    simpa [prefixWord, tailWord_2069112, baseEnd_2069112] using wordTrace_append hprefix tailTrace_2069112
  have hstable : (prefixWord ++ tailWord_2069112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069112).length < 2 ^ (prefixWord ++ tailWord_2069112).sum := by decide
  have hdescent : baseEnd_2069112 < baseStart_2069112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069195 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9]
def baseStart_2069195 : Nat := 118140960795 + 2069195 * 2 ^ 59
def prefixEnd_2069195 : Nat := 4983230072969 + 3 ^ 40 * 2069195 * 2
def baseEnd_2069195 : Nat := 1062491602880136998746451

theorem tailTrace_2069195 : CollatzResearch.WordTrace tailWord_2069195 prefixEnd_2069195 1062491602880136998746451 := by
  unfold tailWord_2069195
  simp only [CollatzResearch.WordTrace]
  refine ⟨75469741738667380216265039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50313161159111586810843359 75469741738667380216265039)
  ·
    refine ⟨113204612608001070324397559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75469741738667380216265039 113204612608001070324397559)
    ·
      refine ⟨169806918912001605486596339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113204612608001070324397559 169806918912001605486596339)
      ·
        refine ⟨254710378368002408229894509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169806918912001605486596339 254710378368002408229894509)
        ·
          refine ⟨95516391888000903086210441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254710378368002408229894509 95516391888000903086210441)
          ·
            refine ⟨71637293916000677314657831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95516391888000903086210441 71637293916000677314657831)
            ·
              refine ⟨107455940874001015971986747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71637293916000677314657831 107455940874001015971986747)
              ·
                refine ⟨161183911311001523957980121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107455940874001015971986747 161183911311001523957980121)
                ·
                  refine ⟨120887933483251142968485091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161183911311001523957980121 120887933483251142968485091)
                  ·
                    refine ⟨181331900224876714452727637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120887933483251142968485091 181331900224876714452727637)
                    ·
                      refine ⟨1062491602880136998746451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 181331900224876714452727637 1062491602880136998746451)
                      ·
                        rfl

theorem cell23_2069195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_2069195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069195 prefixEnd_2069195 := by exact prefixLift 2069195
  have htrace : WordTrace (prefixWord ++ tailWord_2069195) baseStart_2069195 baseEnd_2069195 := by
    simpa [prefixWord, tailWord_2069195, baseEnd_2069195] using wordTrace_append hprefix tailTrace_2069195
  have hstable : (prefixWord ++ tailWord_2069195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069195).length < 2 ^ (prefixWord ++ tailWord_2069195).sum := by decide
  have hdescent : baseEnd_2069195 < baseStart_2069195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069232 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_2069232 : Nat := 118140960795 + 2069232 * 2 ^ 59
def prefixEnd_2069232 : Nat := 4983230072969 + 3 ^ 40 * 2069232 * 2
def baseEnd_2069232 : Nat := 354170200554784451327927

theorem tailTrace_2069232 : CollatzResearch.WordTrace tailWord_2069232 prefixEnd_2069232 354170200554784451327927 := by
  unfold tailWord_2069232
  simp only [CollatzResearch.WordTrace]
  refine ⟨37735545619766667767680975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50314060826355557023574633 37735545619766667767680975)
  ·
    refine ⟨56603318429650001651521463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37735545619766667767680975 56603318429650001651521463)
    ·
      refine ⟨84904977644475002477282195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56603318429650001651521463 84904977644475002477282195)
      ·
        refine ⟨127357466466712503715923293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84904977644475002477282195 127357466466712503715923293)
        ·
          refine ⟨47759049925017188893471235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127357466466712503715923293 47759049925017188893471235)
          ·
            refine ⟨71638574887525783340206853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47759049925017188893471235 71638574887525783340206853)
            ·
              refine ⟨13432232791411084376288785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71638574887525783340206853 13432232791411084376288785)
              ·
                refine ⟨10074174593558313282216589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13432232791411084376288785 10074174593558313282216589)
                ·
                  refine ⟨3777815472584367480831221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10074174593558313282216589 3777815472584367480831221)
                  ·
                    refine ⟨354170200554784451327927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3777815472584367480831221 354170200554784451327927)
                    ·
                      rfl

theorem cell23_2069232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_2069232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069232 prefixEnd_2069232 := by exact prefixLift 2069232
  have htrace : WordTrace (prefixWord ++ tailWord_2069232) baseStart_2069232 baseEnd_2069232 := by
    simpa [prefixWord, tailWord_2069232, baseEnd_2069232] using wordTrace_append hprefix tailTrace_2069232
  have hstable : (prefixWord ++ tailWord_2069232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069232).length < 2 ^ (prefixWord ++ tailWord_2069232).sum := by decide
  have hdescent : baseEnd_2069232 < baseStart_2069232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069239 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 6, 3, 2]
def baseStart_2069239 : Nat := 118140960795 + 2069239 * 2 ^ 59
def prefixEnd_2069239 : Nat := 4983230072969 + 3 ^ 40 * 2069239 * 2
def baseEnd_2069239 : Nat := 1062514196028934826596249

theorem tailTrace_2069239 : CollatzResearch.WordTrace tailWord_2069239 prefixEnd_2069239 1062514196028934826596249 := by
  unfold tailWord_2069239
  simp only [CollatzResearch.WordTrace]
  refine ⟨75471346550507975730866771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50314231033671983820577847 75471346550507975730866771)
  ·
    refine ⟨113207019825761963596300157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75471346550507975730866771 113207019825761963596300157)
    ·
      refine ⟨42452632434660736348612559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113207019825761963596300157 42452632434660736348612559)
      ·
        refine ⟨63678948651991104522918839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42452632434660736348612559 63678948651991104522918839)
        ·
          refine ⟨95518422977986656784378259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63678948651991104522918839 95518422977986656784378259)
          ·
            refine ⟨143277634466979985176567389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95518422977986656784378259 143277634466979985176567389)
            ·
              refine ⟨53729112925117494441212771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143277634466979985176567389 53729112925117494441212771)
              ·
                refine ⟨80593669387676241661819157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53729112925117494441212771 80593669387676241661819157)
                ·
                  refine ⟨3777828252547323827897773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80593669387676241661819157 3777828252547323827897773)
                  ·
                    refine ⟨1416685594705246435461665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777828252547323827897773 1416685594705246435461665)
                    ·
                      refine ⟨1062514196028934826596249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416685594705246435461665 1062514196028934826596249)
                      ·
                        rfl

theorem cell23_2069239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_2069239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069239 prefixEnd_2069239 := by exact prefixLift 2069239
  have htrace : WordTrace (prefixWord ++ tailWord_2069239) baseStart_2069239 baseEnd_2069239 := by
    simpa [prefixWord, tailWord_2069239, baseEnd_2069239] using wordTrace_append hprefix tailTrace_2069239
  have hstable : (prefixWord ++ tailWord_2069239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069239).length < 2 ^ (prefixWord ++ tailWord_2069239).sum := by decide
  have hdescent : baseEnd_2069239 < baseStart_2069239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069256 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_2069256 : Nat := 118140960795 + 2069256 * 2 ^ 59
def prefixEnd_2069256 : Nat := 4983230072969 + 3 ^ 40 * 2069256 * 2
def baseEnd_2069256 : Nat := 1062522925200061260083671

theorem tailTrace_2069256 : CollatzResearch.WordTrace tailWord_2069256 prefixEnd_2069256 1062522925200061260083671 := by
  unfold tailWord_2069256
  simp only [CollatzResearch.WordTrace]
  refine ⟨37735983295723193817117811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50314644394297591756157081 37735983295723193817117811)
  ·
    refine ⟨56603974943584790725676717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37735983295723193817117811 56603974943584790725676717)
    ·
      refine ⟨21226490603844296522128769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56603974943584790725676717 21226490603844296522128769)
      ·
        refine ⟨15919867952883222391596577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21226490603844296522128769 15919867952883222391596577)
        ·
          refine ⟨11939900964662416793697433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15919867952883222391596577 11939900964662416793697433)
          ·
            refine ⟨8954925723496812595273075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11939900964662416793697433 8954925723496812595273075)
            ·
              refine ⟨13432388585245218892909613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8954925723496812595273075 13432388585245218892909613)
              ·
                refine ⟨5037145719466957084841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13432388585245218892909613 5037145719466957084841105)
                ·
                  refine ⟨3777859289600217813630829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037145719466957084841105 3777859289600217813630829)
                  ·
                    refine ⟨1416697233600081680111561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3777859289600217813630829 1416697233600081680111561)
                    ·
                      refine ⟨1062522925200061260083671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416697233600081680111561 1062522925200061260083671)
                      ·
                        rfl

theorem cell23_2069256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_2069256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069256 prefixEnd_2069256 := by exact prefixLift 2069256
  have htrace : WordTrace (prefixWord ++ tailWord_2069256) baseStart_2069256 baseEnd_2069256 := by
    simpa [prefixWord, tailWord_2069256, baseEnd_2069256] using wordTrace_append hprefix tailTrace_2069256
  have hstable : (prefixWord ++ tailWord_2069256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069256).length < 2 ^ (prefixWord ++ tailWord_2069256).sum := by decide
  have hdescent : baseEnd_2069256 < baseStart_2069256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069280 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 1, 1, 3]
def baseStart_2069280 : Nat := 118140960795 + 2069280 * 2 ^ 59
def prefixEnd_2069280 : Nat := 4983230072969 + 3 ^ 40 * 2069280 * 2
def baseEnd_2069280 : Nat := 1062535248735769166183561

theorem tailTrace_2069280 : CollatzResearch.WordTrace tailWord_2069280 prefixEnd_2069280 1062535248735769166183561 := by
  unfold tailWord_2069280
  simp only [CollatzResearch.WordTrace]
  refine ⟨37736420971679719866554647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50315227962239626488739529 37736420971679719866554647)
  ·
    refine ⟨56604631457519579799831971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37736420971679719866554647 56604631457519579799831971)
    ·
      refine ⟨84906947186279369699747957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56604631457519579799831971 84906947186279369699747957)
      ·
        refine ⟨7960026298713690909351371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84906947186279369699747957 7960026298713690909351371)
        ·
          refine ⟨11940039448070536364027057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960026298713690909351371 11940039448070536364027057)
          ·
            refine ⟨8955029586052902273020293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11940039448070536364027057 8955029586052902273020293)
            ·
              refine ⟨1679068047384919176191305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8955029586052902273020293 1679068047384919176191305)
              ·
                refine ⟨1259301035538689382143479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679068047384919176191305 1259301035538689382143479)
                ·
                  refine ⟨1888951553308034073215219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259301035538689382143479 1888951553308034073215219)
                  ·
                    refine ⟨2833427329962051109822829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1888951553308034073215219 2833427329962051109822829)
                    ·
                      refine ⟨1062535248735769166183561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2833427329962051109822829 1062535248735769166183561)
                      ·
                        rfl

theorem cell23_2069280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_2069280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069280 prefixEnd_2069280 := by exact prefixLift 2069280
  have htrace : WordTrace (prefixWord ++ tailWord_2069280) baseStart_2069280 baseEnd_2069280 := by
    simpa [prefixWord, tailWord_2069280, baseEnd_2069280] using wordTrace_append hprefix tailTrace_2069280
  have hstable : (prefixWord ++ tailWord_2069280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069280).length < 2 ^ (prefixWord ++ tailWord_2069280).sum := by decide
  have hdescent : baseEnd_2069280 < baseStart_2069280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069299 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4]
def baseStart_2069299 : Nat := 118140960795 + 2069299 * 2 ^ 59
def prefixEnd_2069299 : Nat := 4983230072969 + 3 ^ 40 * 2069299 * 2
def baseEnd_2069299 : Nat := 1062545004868204591845973

theorem tailTrace_2069299 : CollatzResearch.WordTrace tailWord_2069299 prefixEnd_2069299 1062545004868204591845973 := by
  unfold tailWord_2069299
  simp only [CollatzResearch.WordTrace]
  refine ⟨75473534930290605978050951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50315689953527070652033967 75473534930290605978050951)
  ·
    refine ⟨113210302395435908967076427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75473534930290605978050951 113210302395435908967076427)
    ·
      refine ⟨169815453593153863450614641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113210302395435908967076427 169815453593153863450614641)
      ·
        refine ⟨127361590194865397587960981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169815453593153863450614641 127361590194865397587960981)
        ·
          refine ⟨5970074540384315511935671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127361590194865397587960981 5970074540384315511935671)
          ·
            refine ⟨8955111810576473267903507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970074540384315511935671 8955111810576473267903507)
            ·
              refine ⟨13432667715864709901855261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955111810576473267903507 13432667715864709901855261)
              ·
                refine ⟨5037250393449266213195723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13432667715864709901855261 5037250393449266213195723)
                ·
                  refine ⟨7555875590173899319793585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037250393449266213195723 7555875590173899319793585)
                  ·
                    refine ⟨5666906692630424489845189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7555875590173899319793585 5666906692630424489845189)
                    ·
                      refine ⟨1062545004868204591845973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5666906692630424489845189 1062545004868204591845973)
                      ·
                        rfl

theorem cell23_2069299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_2069299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069299 prefixEnd_2069299 := by exact prefixLift 2069299
  have htrace : WordTrace (prefixWord ++ tailWord_2069299) baseStart_2069299 baseEnd_2069299 := by
    simpa [prefixWord, tailWord_2069299, baseEnd_2069299] using wordTrace_append hprefix tailTrace_2069299
  have hstable : (prefixWord ++ tailWord_2069299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069299).length < 2 ^ (prefixWord ++ tailWord_2069299).sum := by decide
  have hdescent : baseEnd_2069299 < baseStart_2069299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069320 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_2069320 : Nat := 118140960795 + 2069320 * 2 ^ 59
def prefixEnd_2069320 : Nat := 4983230072969 + 3 ^ 40 * 2069320 * 2
def baseEnd_2069320 : Nat := 1062555787961949009683377

theorem tailTrace_2069320 : CollatzResearch.WordTrace tailWord_2069320 prefixEnd_2069320 1062555787961949009683377 := by
  unfold tailWord_2069320
  simp only [CollatzResearch.WordTrace]
  refine ⟨37737150431607263282282707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50316200575476351043043609 37737150431607263282282707)
  ·
    refine ⟨56605725647410894923424061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37737150431607263282282707 56605725647410894923424061)
    ·
      refine ⟨21227147117779085596284023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56605725647410894923424061 21227147117779085596284023)
      ·
        refine ⟨31840720676668628394426035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227147117779085596284023 31840720676668628394426035)
        ·
          refine ⟨47761081015002942591639053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31840720676668628394426035 47761081015002942591639053)
          ·
            refine ⟨17910405380626103471864645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47761081015002942591639053 17910405380626103471864645)
            ·
              refine ⟨3358201008867394400974621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17910405380626103471864645 3358201008867394400974621)
              ·
                refine ⟨1259325378325272900365483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3358201008867394400974621 1259325378325272900365483)
                ·
                  refine ⟨1888988067487909350548225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259325378325272900365483 1888988067487909350548225)
                  ·
                    refine ⟨1416741050615932012911169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1888988067487909350548225 1416741050615932012911169)
                    ·
                      refine ⟨1062555787961949009683377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416741050615932012911169 1062555787961949009683377)
                      ·
                        rfl

theorem cell23_2069320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_2069320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069320 prefixEnd_2069320 := by exact prefixLift 2069320
  have htrace : WordTrace (prefixWord ++ tailWord_2069320) baseStart_2069320 baseEnd_2069320 := by
    simpa [prefixWord, tailWord_2069320, baseEnd_2069320] using wordTrace_append hprefix tailTrace_2069320
  have hstable : (prefixWord ++ tailWord_2069320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069320).length < 2 ^ (prefixWord ++ tailWord_2069320).sum := by decide
  have hdescent : baseEnd_2069320 < baseStart_2069320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069322 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_2069322 : Nat := 118140960795 + 2069322 * 2 ^ 59
def prefixEnd_2069322 : Nat := 4983230072969 + 3 ^ 40 * 2069322 * 2
def baseEnd_2069322 : Nat := 354185604974419333952789

theorem tailTrace_2069322 : CollatzResearch.WordTrace tailWord_2069322 prefixEnd_2069322 354185604974419333952789 := by
  unfold tailWord_2069322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868593452301820226534555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50316249206138187270758813 18868593452301820226534555)
  ·
    refine ⟨28302890178452730339801833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18868593452301820226534555 28302890178452730339801833)
    ·
      refine ⟨21227167633839547754851375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28302890178452730339801833 21227167633839547754851375)
      ·
        refine ⟨31840751450759321632277063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227167633839547754851375 31840751450759321632277063)
        ·
          refine ⟨47761127176138982448415595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31840751450759321632277063 47761127176138982448415595)
          ·
            refine ⟨71641690764208473672623393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47761127176138982448415595 71641690764208473672623393)
            ·
              refine ⟨53731268073156355254467545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71641690764208473672623393 53731268073156355254467545)
              ·
                refine ⟨40298451054867266440850659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53731268073156355254467545 40298451054867266440850659)
                ·
                  refine ⟨60447676582300899661275989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40298451054867266440850659 60447676582300899661275989)
                  ·
                    refine ⟨354185604974419333952789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 60447676582300899661275989 354185604974419333952789)
                    ·
                      rfl

theorem cell23_2069322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_2069322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069322 prefixEnd_2069322 := by exact prefixLift 2069322
  have htrace : WordTrace (prefixWord ++ tailWord_2069322) baseStart_2069322 baseEnd_2069322 := by
    simpa [prefixWord, tailWord_2069322, baseEnd_2069322] using wordTrace_append hprefix tailTrace_2069322
  have hstable : (prefixWord ++ tailWord_2069322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069322).length < 2 ^ (prefixWord ++ tailWord_2069322).sum := by decide
  have hdescent : baseEnd_2069322 < baseStart_2069322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069366 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2069366 : Nat := 118140960795 + 2069366 * 2 ^ 59
def prefixEnd_2069366 : Nat := 4983230072969 + 3 ^ 40 * 2069366 * 2
def baseEnd_2069366 : Nat := 1062579408072055829708165

theorem tailTrace_2069366 : CollatzResearch.WordTrace tailWord_2069366 prefixEnd_2069366 1062579408072055829708165 := by
  unfold tailWord_2069366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717248663815492276296247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50317319080698584280493301 4717248663815492276296247)
  ·
    refine ⟨7075872995723238414444371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717248663815492276296247 7075872995723238414444371)
    ·
      refine ⟨10613809493584857621666557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7075872995723238414444371 10613809493584857621666557)
      ·
        refine ⟨3980178560094321608124959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10613809493584857621666557 3980178560094321608124959)
        ·
          refine ⟨5970267840141482412187439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980178560094321608124959 5970267840141482412187439)
          ·
            refine ⟨8955401760212223618281159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5970267840141482412187439 8955401760212223618281159)
            ·
              refine ⟨13433102640318335427421739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8955401760212223618281159 13433102640318335427421739)
              ·
                refine ⟨20149653960477503141132609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433102640318335427421739 20149653960477503141132609)
                ·
                  refine ⟨15112240470358127355849457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20149653960477503141132609 15112240470358127355849457)
                  ·
                    refine ⟨11334180352768595516887093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15112240470358127355849457 11334180352768595516887093)
                    ·
                      refine ⟨1062579408072055829708165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11334180352768595516887093 1062579408072055829708165)
                      ·
                        rfl

theorem cell23_2069366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2069366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069366 prefixEnd_2069366 := by exact prefixLift 2069366
  have htrace : WordTrace (prefixWord ++ tailWord_2069366) baseStart_2069366 baseEnd_2069366 := by
    simpa [prefixWord, tailWord_2069366, baseEnd_2069366] using wordTrace_append hprefix tailTrace_2069366
  have hstable : (prefixWord ++ tailWord_2069366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069366).length < 2 ^ (prefixWord ++ tailWord_2069366).sum := by decide
  have hdescent : baseEnd_2069366 < baseStart_2069366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069379 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5]
def baseStart_2069379 : Nat := 118140960795 + 2069379 * 2 ^ 59
def prefixEnd_2069379 : Nat := 4983230072969 + 3 ^ 40 * 2069379 * 2
def baseEnd_2069379 : Nat := 1062586083320564278845605

theorem tailTrace_2069379 : CollatzResearch.WordTrace tailWord_2069379 prefixEnd_2069379 1062586083320564278845605 := by
  unfold tailWord_2069379
  simp only [CollatzResearch.WordTrace]
  refine ⟨75476452770000779640963191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50317635180000519760642127 75476452770000779640963191)
  ·
    refine ⟨113214679155001169461444787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75476452770000779640963191 113214679155001169461444787)
    ·
      refine ⟨169822018732501754192167181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113214679155001169461444787 169822018732501754192167181)
      ·
        refine ⟨63683257024688157822062693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169822018732501754192167181 63683257024688157822062693)
        ·
          refine ⟨11940610692129029591636755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63683257024688157822062693 11940610692129029591636755)
          ·
            refine ⟨17910916038193544387455133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11940610692129029591636755 17910916038193544387455133)
            ·
              refine ⟨6716593514322579145295675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17910916038193544387455133 6716593514322579145295675)
              ·
                refine ⟨10074890271483868717943513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716593514322579145295675 10074890271483868717943513)
                ·
                  refine ⟨7556167703612901538457635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10074890271483868717943513 7556167703612901538457635)
                  ·
                    refine ⟨11334251555419352307686453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556167703612901538457635 11334251555419352307686453)
                    ·
                      refine ⟨1062586083320564278845605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11334251555419352307686453 1062586083320564278845605)
                      ·
                        rfl

theorem cell23_2069379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_2069379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069379 prefixEnd_2069379 := by exact prefixLift 2069379
  have htrace : WordTrace (prefixWord ++ tailWord_2069379) baseStart_2069379 baseEnd_2069379 := by
    simpa [prefixWord, tailWord_2069379, baseEnd_2069379] using wordTrace_append hprefix tailTrace_2069379
  have hstable : (prefixWord ++ tailWord_2069379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069379).length < 2 ^ (prefixWord ++ tailWord_2069379).sum := by decide
  have hdescent : baseEnd_2069379 < baseStart_2069379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069393 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 2, 2, 2]
def baseStart_2069393 : Nat := 118140960795 + 2069393 * 2 ^ 59
def prefixEnd_2069393 : Nat := 4983230072969 + 3 ^ 40 * 2069393 * 2
def baseEnd_2069393 : Nat := 1062593272049727224070541

theorem tailTrace_2069393 : CollatzResearch.WordTrace tailWord_2069393 prefixEnd_2069393 1062593272049727224070541 := by
  unfold tailWord_2069393
  simp only [CollatzResearch.WordTrace]
  refine ⟨75476963391950060031972833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50317975594633373354648555 75476963391950060031972833)
  ·
    refine ⟨56607722543962545023979625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75476963391950060031972833 56607722543962545023979625)
    ·
      refine ⟨42455791907971908767984719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56607722543962545023979625 42455791907971908767984719)
      ·
        refine ⟨63683687861957863151977079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42455791907971908767984719 63683687861957863151977079)
        ·
          refine ⟨95525531792936794727965619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63683687861957863151977079 95525531792936794727965619)
          ·
            refine ⟨143288297689405192091948429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95525531792936794727965619 143288297689405192091948429)
            ·
              refine ⟨53733111633526947034480661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143288297689405192091948429 53733111633526947034480661)
              ·
                refine ⟨2518739607821575642241281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53733111633526947034480661 2518739607821575642241281)
                ·
                  refine ⟨1889054705866181731680961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518739607821575642241281 1889054705866181731680961)
                  ·
                    refine ⟨1416791029399636298760721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889054705866181731680961 1416791029399636298760721)
                    ·
                      refine ⟨1062593272049727224070541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416791029399636298760721 1062593272049727224070541)
                      ·
                        rfl

theorem cell23_2069393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_2069393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069393 prefixEnd_2069393 := by exact prefixLift 2069393
  have htrace : WordTrace (prefixWord ++ tailWord_2069393) baseStart_2069393 baseEnd_2069393 := by
    simpa [prefixWord, tailWord_2069393, baseEnd_2069393] using wordTrace_append hprefix tailTrace_2069393
  have hstable : (prefixWord ++ tailWord_2069393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069393).length < 2 ^ (prefixWord ++ tailWord_2069393).sum := by decide
  have hdescent : baseEnd_2069393 < baseStart_2069393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069396 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2069396 : Nat := 118140960795 + 2069396 * 2 ^ 59
def prefixEnd_2069396 : Nat := 4983230072969 + 3 ^ 40 * 2069396 * 2
def baseEnd_2069396 : Nat := 1062594812491690712333027

theorem tailTrace_2069396 : CollatzResearch.WordTrace tailWord_2069396 prefixEnd_2069396 1062594812491690712333027 := by
  unfold tailWord_2069396
  simp only [CollatzResearch.WordTrace]
  refine ⟨37738536405469595772166021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50318048540626127696221361 37738536405469595772166021)
  ·
    refine ⟨7075975576025549207281129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37738536405469595772166021 7075975576025549207281129)
    ·
      refine ⟨5306981682019161905460847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7075975576025549207281129 5306981682019161905460847)
      ·
        refine ⟨7960472523028742858191271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306981682019161905460847 7960472523028742858191271)
        ·
          refine ⟨11940708784543114287286907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7960472523028742858191271 11940708784543114287286907)
          ·
            refine ⟨17911063176814671430930361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11940708784543114287286907 17911063176814671430930361)
            ·
              refine ⟨13433297382611003573197771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17911063176814671430930361 13433297382611003573197771)
              ·
                refine ⟨20149946073916505359796657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13433297382611003573197771 20149946073916505359796657)
                ·
                  refine ⟨15112459555437379019847493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20149946073916505359796657 15112459555437379019847493)
                  ·
                    refine ⟨2833586166644508566221405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15112459555437379019847493 2833586166644508566221405)
                    ·
                      refine ⟨1062594812491690712333027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2833586166644508566221405 1062594812491690712333027)
                      ·
                        rfl

theorem cell23_2069396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2069396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069396 prefixEnd_2069396 := by exact prefixLift 2069396
  have htrace : WordTrace (prefixWord ++ tailWord_2069396) baseStart_2069396 baseEnd_2069396 := by
    simpa [prefixWord, tailWord_2069396, baseEnd_2069396] using wordTrace_append hprefix tailTrace_2069396
  have hstable : (prefixWord ++ tailWord_2069396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069396).length < 2 ^ (prefixWord ++ tailWord_2069396).sum := by decide
  have hdescent : baseEnd_2069396 < baseStart_2069396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069404 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2069404 : Nat := 118140960795 + 2069404 * 2 ^ 59
def prefixEnd_2069404 : Nat := 4983230072969 + 3 ^ 40 * 2069404 * 2
def baseEnd_2069404 : Nat := 1062598920336926681032991

theorem tailTrace_2069404 : CollatzResearch.WordTrace tailWord_2069404 prefixEnd_2069404 1062598920336926681032991 := by
  unfold tailWord_2069404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37738682297455104455311633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50318243063273472607082177 37738682297455104455311633)
  ·
    refine ⟨28304011723091328341483725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37738682297455104455311633 28304011723091328341483725)
    ·
      refine ⟨10614004396159248128056397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28304011723091328341483725 10614004396159248128056397)
      ·
        refine ⟨3980251648559718048021149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10614004396159248128056397 3980251648559718048021149)
        ·
          refine ⟨1492594368209894268007931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3980251648559718048021149 1492594368209894268007931)
          ·
            refine ⟨2238891552314841402011897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492594368209894268007931 2238891552314841402011897)
            ·
              refine ⟨1679168664236131051508923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238891552314841402011897 1679168664236131051508923)
              ·
                refine ⟨2518752996354196577263385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679168664236131051508923 2518752996354196577263385)
                ·
                  refine ⟨1889064747265647432947539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518752996354196577263385 1889064747265647432947539)
                  ·
                    refine ⟨2833597120898471149421309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1889064747265647432947539 2833597120898471149421309)
                    ·
                      refine ⟨1062598920336926681032991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2833597120898471149421309 1062598920336926681032991)
                      ·
                        rfl

theorem cell23_2069404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2069404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069404 prefixEnd_2069404 := by exact prefixLift 2069404
  have htrace : WordTrace (prefixWord ++ tailWord_2069404) baseStart_2069404 baseEnd_2069404 := by
    simpa [prefixWord, tailWord_2069404, baseEnd_2069404] using wordTrace_append hprefix tailTrace_2069404
  have hstable : (prefixWord ++ tailWord_2069404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069404).length < 2 ^ (prefixWord ++ tailWord_2069404).sum := by decide
  have hdescent : baseEnd_2069404 < baseStart_2069404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069444 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2069444 : Nat := 118140960795 + 2069444 * 2 ^ 59
def prefixEnd_2069444 : Nat := 4983230072969 + 3 ^ 40 * 2069444 * 2
def baseEnd_2069444 : Nat := 1062619459563106524532807

theorem tailTrace_2069444 : CollatzResearch.WordTrace tailWord_2069444 prefixEnd_2069444 1062619459563106524532807 := by
  unfold tailWord_2069444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37739411757382647871039693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50319215676510197161386257 37739411757382647871039693)
  ·
    refine ⟨14152279409018492951639885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37739411757382647871039693 14152279409018492951639885)
    ·
      refine ⟨5307104778381934856864957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14152279409018492951639885 5307104778381934856864957)
      ·
        refine ⟨1990164291893225571324359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5307104778381934856864957 1990164291893225571324359)
        ·
          refine ⟨2985246437839838356986539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990164291893225571324359 2985246437839838356986539)
          ·
            refine ⟨4477869656759757535479809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985246437839838356986539 4477869656759757535479809)
            ·
              refine ⟨3358402242569818151609857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477869656759757535479809 3358402242569818151609857)
              ·
                refine ⟨2518801681927363613707393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358402242569818151609857 2518801681927363613707393)
                ·
                  refine ⟨1889101261445522710280545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2518801681927363613707393 1889101261445522710280545)
                  ·
                    refine ⟨1416825946084142032710409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889101261445522710280545 1416825946084142032710409)
                    ·
                      refine ⟨1062619459563106524532807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416825946084142032710409 1062619459563106524532807)
                      ·
                        rfl

theorem cell23_2069444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2069444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069444 prefixEnd_2069444 := by exact prefixLift 2069444
  have htrace : WordTrace (prefixWord ++ tailWord_2069444) baseStart_2069444 baseEnd_2069444 := by
    simpa [prefixWord, tailWord_2069444, baseEnd_2069444] using wordTrace_append hprefix tailTrace_2069444
  have hstable : (prefixWord ++ tailWord_2069444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069444).length < 2 ^ (prefixWord ++ tailWord_2069444).sum := by decide
  have hdescent : baseEnd_2069444 < baseStart_2069444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069509 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_2069509 : Nat := 118140960795 + 2069509 * 2 ^ 59
def prefixEnd_2069509 : Nat := 4983230072969 + 3 ^ 40 * 2069509 * 2
def baseEnd_2069509 : Nat := 1062652835805648770220007

theorem tailTrace_2069509 : CollatzResearch.WordTrace tailWord_2069509 prefixEnd_2069509 1062652835805648770220007 := by
  unfold tailWord_2069509
  simp only [CollatzResearch.WordTrace]
  refine ⟨75481194259529811843195581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50320796173019874562130387 75481194259529811843195581)
  ·
    refine ⟨28305447847323679441198343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75481194259529811843195581 28305447847323679441198343)
    ·
      refine ⟨42458171770985519161797515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28305447847323679441198343 42458171770985519161797515)
      ·
        refine ⟨63687257656478278742696273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42458171770985519161797515 63687257656478278742696273)
        ·
          refine ⟨47765443242358709057022205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63687257656478278742696273 47765443242358709057022205)
          ·
            refine ⟨17912041215884515896383327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47765443242358709057022205 17912041215884515896383327)
            ·
              refine ⟨26868061823826773844574991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17912041215884515896383327 26868061823826773844574991)
              ·
                refine ⟨40302092735740160766862487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26868061823826773844574991 40302092735740160766862487)
                ·
                  refine ⟨60453139103610241150293731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40302092735740160766862487 60453139103610241150293731)
                  ·
                    refine ⟨90679708655415361725440597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60453139103610241150293731 90679708655415361725440597)
                    ·
                      refine ⟨1062652835805648770220007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 90679708655415361725440597 1062652835805648770220007)
                      ·
                        rfl

theorem cell23_2069509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_2069509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069509 prefixEnd_2069509 := by exact prefixLift 2069509
  have htrace : WordTrace (prefixWord ++ tailWord_2069509) baseStart_2069509 baseEnd_2069509 := by
    simpa [prefixWord, tailWord_2069509, baseEnd_2069509] using wordTrace_append hprefix tailTrace_2069509
  have hstable : (prefixWord ++ tailWord_2069509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069509).length < 2 ^ (prefixWord ++ tailWord_2069509).sum := by decide
  have hdescent : baseEnd_2069509 < baseStart_2069509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069529 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_2069529 : Nat := 118140960795 + 2069529 * 2 ^ 59
def prefixEnd_2069529 : Nat := 4983230072969 + 3 ^ 40 * 2069529 * 2
def baseEnd_2069529 : Nat := 1062663105418738691969915

theorem tailTrace_2069529 : CollatzResearch.WordTrace tailWord_2069529 prefixEnd_2069529 1062663105418738691969915 := by
  unfold tailWord_2069529
  simp only [CollatzResearch.WordTrace]
  refine ⟨75481923719457355258923641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50321282479638236839282427 75481923719457355258923641)
  ·
    refine ⟨56611442789593016444192731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75481923719457355258923641 56611442789593016444192731)
    ·
      refine ⟨84917164184389524666289097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56611442789593016444192731 84917164184389524666289097)
      ·
        refine ⟨63687873138292143499716823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84917164184389524666289097 63687873138292143499716823)
        ·
          refine ⟨95531809707438215249575235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63687873138292143499716823 95531809707438215249575235)
          ·
            refine ⟨143297714561157322874362853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95531809707438215249575235 143297714561157322874362853)
            ·
              refine ⟨26868321480216998038943035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143297714561157322874362853 26868321480216998038943035)
              ·
                refine ⟨40302482220325497058414553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26868321480216998038943035 40302482220325497058414553)
                ·
                  refine ⟨30226861665244122793810915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40302482220325497058414553 30226861665244122793810915)
                  ·
                    refine ⟨45340292497866184190716373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30226861665244122793810915 45340292497866184190716373)
                    ·
                      refine ⟨1062663105418738691969915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45340292497866184190716373 1062663105418738691969915)
                      ·
                        rfl

theorem cell23_2069529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_2069529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069529 prefixEnd_2069529 := by exact prefixLift 2069529
  have htrace : WordTrace (prefixWord ++ tailWord_2069529) baseStart_2069529 baseEnd_2069529 := by
    simpa [prefixWord, tailWord_2069529, baseEnd_2069529] using wordTrace_append hprefix tailTrace_2069529
  have hstable : (prefixWord ++ tailWord_2069529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069529).length < 2 ^ (prefixWord ++ tailWord_2069529).sum := by decide
  have hdescent : baseEnd_2069529 < baseStart_2069529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069560 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 2, 3, 2]
def baseStart_2069560 : Nat := 118140960795 + 2069560 * 2 ^ 59
def prefixEnd_2069560 : Nat := 4983230072969 + 3 ^ 40 * 2069560 * 2
def baseEnd_2069560 : Nat := 1062679023319028070682273

theorem tailTrace_2069560 : CollatzResearch.WordTrace tailWord_2069560 prefixEnd_2069560 1062679023319028070682273 := by
  unfold tailWord_2069560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37741527191172523776651067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50322036254896698368868089 37741527191172523776651067)
  ·
    refine ⟨56612290786758785664976601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37741527191172523776651067 56612290786758785664976601)
    ·
      refine ⟨42459218090069089248732451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56612290786758785664976601 42459218090069089248732451)
      ·
        refine ⟨63688827135103633873098677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42459218090069089248732451 63688827135103633873098677)
        ·
          refine ⟨5970827543915965675603001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63688827135103633873098677 5970827543915965675603001)
          ·
            refine ⟨4478120657936974256702251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5970827543915965675603001 4478120657936974256702251)
            ·
              refine ⟨6717180986905461385053377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478120657936974256702251 6717180986905461385053377)
              ·
                refine ⟨5037885740179096038790033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6717180986905461385053377 5037885740179096038790033)
                ·
                  refine ⟨3778414305134322029092525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037885740179096038790033 3778414305134322029092525)
                  ·
                    refine ⟨1416905364425370760909697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3778414305134322029092525 1416905364425370760909697)
                    ·
                      refine ⟨1062679023319028070682273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416905364425370760909697 1062679023319028070682273)
                      ·
                        rfl

theorem cell23_2069560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_2069560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069560 prefixEnd_2069560 := by exact prefixLift 2069560
  have htrace : WordTrace (prefixWord ++ tailWord_2069560) baseStart_2069560 baseEnd_2069560 := by
    simpa [prefixWord, tailWord_2069560, baseEnd_2069560] using wordTrace_append hprefix tailTrace_2069560
  have hstable : (prefixWord ++ tailWord_2069560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069560).length < 2 ^ (prefixWord ++ tailWord_2069560).sum := by decide
  have hdescent : baseEnd_2069560 < baseStart_2069560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069576 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_2069576 : Nat := 118140960795 + 2069576 * 2 ^ 59
def prefixEnd_2069576 : Nat := 4983230072969 + 3 ^ 40 * 2069576 * 2
def baseEnd_2069576 : Nat := 1062687239009500008082199

theorem tailTrace_2069576 : CollatzResearch.WordTrace tailWord_2069576 prefixEnd_2069576 1062687239009500008082199 := by
  unfold tailWord_2069576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37741818975143541142942291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50322425300191388190589721 37741818975143541142942291)
  ·
    refine ⟨56612728462715311714413437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37741818975143541142942291 56612728462715311714413437)
    ·
      refine ⟨21229773173518241892905039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56612728462715311714413437 21229773173518241892905039)
      ·
        refine ⟨31844659760277362839357559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21229773173518241892905039 31844659760277362839357559)
        ·
          refine ⟨47766989640416044259036339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31844659760277362839357559 47766989640416044259036339)
          ·
            refine ⟨71650484460624066388554509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47766989640416044259036339 71650484460624066388554509)
            ·
              refine ⟨26868931672734024895707941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71650484460624066388554509 26868931672734024895707941)
              ·
                refine ⟨5037924688637629667945239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26868931672734024895707941 5037924688637629667945239)
                ·
                  refine ⟨7556887032956444501917859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5037924688637629667945239 7556887032956444501917859)
                  ·
                    refine ⟨11335330549434666752876789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7556887032956444501917859 11335330549434666752876789)
                    ·
                      refine ⟨1062687239009500008082199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11335330549434666752876789 1062687239009500008082199)
                      ·
                        rfl

theorem cell23_2069576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_2069576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069576 prefixEnd_2069576 := by exact prefixLift 2069576
  have htrace : WordTrace (prefixWord ++ tailWord_2069576) baseStart_2069576 baseEnd_2069576 := by
    simpa [prefixWord, tailWord_2069576, baseEnd_2069576] using wordTrace_append hprefix tailTrace_2069576
  have hstable : (prefixWord ++ tailWord_2069576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069576).length < 2 ^ (prefixWord ++ tailWord_2069576).sum := by decide
  have hdescent : baseEnd_2069576 < baseStart_2069576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069593 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 3]
def baseStart_2069593 : Nat := 118140960795 + 2069593 * 2 ^ 59
def prefixEnd_2069593 : Nat := 4983230072969 + 3 ^ 40 * 2069593 * 2
def baseEnd_2069593 : Nat := 1062695968180626441569621

theorem tailTrace_2069593 : CollatzResearch.WordTrace tailWord_2069593 prefixEnd_2069593 1062695968180626441569621 := by
  unfold tailWord_2069593
  simp only [CollatzResearch.WordTrace]
  refine ⟨75484257991225494189253433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50322838660816996126168955 75484257991225494189253433)
  ·
    refine ⟨56613193493419120641940075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75484257991225494189253433 56613193493419120641940075)
    ·
      refine ⟨84919790240128680962910113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56613193493419120641940075 84919790240128680962910113)
      ·
        refine ⟨63689842680096510722182585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84919790240128680962910113 63689842680096510722182585)
        ·
          refine ⟨47767382010072383041636939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63689842680096510722182585 47767382010072383041636939)
          ·
            refine ⟨71651073015108574562455409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47767382010072383041636939 71651073015108574562455409)
            ·
              refine ⟨53738304761331430921841557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71651073015108574562455409 53738304761331430921841557)
              ·
                refine ⟨2518983035687410824461323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53738304761331430921841557 2518983035687410824461323)
                ·
                  refine ⟨3778474553531116236691985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2518983035687410824461323 3778474553531116236691985)
                  ·
                    refine ⟨2833855915148337177518989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3778474553531116236691985 2833855915148337177518989)
                    ·
                      refine ⟨1062695968180626441569621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2833855915148337177518989 1062695968180626441569621)
                      ·
                        rfl

theorem cell23_2069593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_2069593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069593 prefixEnd_2069593 := by exact prefixLift 2069593
  have htrace : WordTrace (prefixWord ++ tailWord_2069593) baseStart_2069593 baseEnd_2069593 := by
    simpa [prefixWord, tailWord_2069593, baseEnd_2069593] using wordTrace_append hprefix tailTrace_2069593
  have hstable : (prefixWord ++ tailWord_2069593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069593).length < 2 ^ (prefixWord ++ tailWord_2069593).sum := by decide
  have hdescent : baseEnd_2069593 < baseStart_2069593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069596 : List Nat := [2, 2, 4, 1, 1, 1, 1, 11]
def baseStart_2069596 : Nat := 118140960795 + 2069596 * 2 ^ 59
def prefixEnd_2069596 : Nat := 4983230072969 + 3 ^ 40 * 2069596 * 2
def baseEnd_2069596 : Nat := 39359166986021849253041

theorem tailTrace_2069596 : CollatzResearch.WordTrace tailWord_2069596 prefixEnd_2069596 39359166986021849253041 := by
  unfold tailWord_2069596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742183705107312850806321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50322911606809750467741761 37742183705107312850806321)
  ·
    refine ⟨28306637778830484638104741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37742183705107312850806321 28306637778830484638104741)
    ·
      refine ⟨5307494583530715869644639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28306637778830484638104741 5307494583530715869644639)
      ·
        refine ⟨7961241875296073804466959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307494583530715869644639 7961241875296073804466959)
        ·
          refine ⟨11941862812944110706700439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961241875296073804466959 11941862812944110706700439)
          ·
            refine ⟨17912794219416166060050659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11941862812944110706700439 17912794219416166060050659)
            ·
              refine ⟨26869191329124249090075989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17912794219416166060050659 26869191329124249090075989)
              ·
                refine ⟨39359166986021849253041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26869191329124249090075989 39359166986021849253041)
                ·
                  rfl

theorem cell23_2069596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 11].length) (baseStart_2069596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069596 prefixEnd_2069596 := by exact prefixLift 2069596
  have htrace : WordTrace (prefixWord ++ tailWord_2069596) baseStart_2069596 baseEnd_2069596 := by
    simpa [prefixWord, tailWord_2069596, baseEnd_2069596] using wordTrace_append hprefix tailTrace_2069596
  have hstable : (prefixWord ++ tailWord_2069596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069596).length < 2 ^ (prefixWord ++ tailWord_2069596).sum := by decide
  have hdescent : baseEnd_2069596 < baseStart_2069596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069610 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2069610 : Nat := 118140960795 + 2069610 * 2 ^ 59
def prefixEnd_2069610 : Nat := 4983230072969 + 3 ^ 40 * 2069610 * 2
def baseEnd_2069610 : Nat := 1062704697351752875057043

theorem tailTrace_2069610 : CollatzResearch.WordTrace tailWord_2069610 prefixEnd_2069610 1062704697351752875057043 := by
  unfold tailWord_2069610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871219508040976523155571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50323252021442604061748189 18871219508040976523155571)
  ·
    refine ⟨28306829262061464784733357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18871219508040976523155571 28306829262061464784733357)
    ·
      refine ⟨10615060973273049294275009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28306829262061464784733357 10615060973273049294275009)
      ·
        refine ⟨7961295729954786970706257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10615060973273049294275009 7961295729954786970706257)
        ·
          refine ⟨5970971797466090228029693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7961295729954786970706257 5970971797466090228029693)
          ·
            refine ⟨2239114424049783835511135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5970971797466090228029693 2239114424049783835511135)
            ·
              refine ⟨3358671636074675753266703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239114424049783835511135 3358671636074675753266703)
              ·
                refine ⟨5038007454112013629900055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358671636074675753266703 5038007454112013629900055)
                ·
                  refine ⟨7557011181168020444850083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038007454112013629900055 7557011181168020444850083)
                  ·
                    refine ⟨11335516771752030667275125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7557011181168020444850083 11335516771752030667275125)
                    ·
                      refine ⟨1062704697351752875057043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11335516771752030667275125 1062704697351752875057043)
                      ·
                        rfl

theorem cell23_2069610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2069610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069610 prefixEnd_2069610 := by exact prefixLift 2069610
  have htrace : WordTrace (prefixWord ++ tailWord_2069610) baseStart_2069610 baseEnd_2069610 := by
    simpa [prefixWord, tailWord_2069610, baseEnd_2069610] using wordTrace_append hprefix tailTrace_2069610
  have hstable : (prefixWord ++ tailWord_2069610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069610).length < 2 ^ (prefixWord ++ tailWord_2069610).sum := by decide
  have hdescent : baseEnd_2069610 < baseStart_2069610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069624 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 1, 2, 2]
def baseStart_2069624 : Nat := 118140960795 + 2069624 * 2 ^ 59
def prefixEnd_2069624 : Nat := 4983230072969 + 3 ^ 40 * 2069624 * 2
def baseEnd_2069624 : Nat := 1062711886080915820281979

theorem tailTrace_2069624 : CollatzResearch.WordTrace tailWord_2069624 prefixEnd_2069624 1062711886080915820281979 := by
  unfold tailWord_2069624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742694327056593241815963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50323592436075457655754617 37742694327056593241815963)
  ·
    refine ⟨56614041490584889862723945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37742694327056593241815963 56614041490584889862723945)
    ·
      refine ⟨42460531117938667397042959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56614041490584889862723945 42460531117938667397042959)
      ·
        refine ⟨63690796676908001095564439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42460531117938667397042959 63690796676908001095564439)
        ·
          refine ⟨95536195015362001643346659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63690796676908001095564439 95536195015362001643346659)
          ·
            refine ⟨143304292523043002465019989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95536195015362001643346659 143304292523043002465019989)
            ·
              refine ⟨1679347178004410185136953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 143304292523043002465019989 1679347178004410185136953)
              ·
                refine ⟨1259510383503307638852715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679347178004410185136953 1259510383503307638852715)
                ·
                  refine ⟨1889265575254961458279073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1259510383503307638852715 1889265575254961458279073)
                  ·
                    refine ⟨1416949181441221093709305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889265575254961458279073 1416949181441221093709305)
                    ·
                      refine ⟨1062711886080915820281979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416949181441221093709305 1062711886080915820281979)
                      ·
                        rfl

theorem cell23_2069624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_2069624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069624 prefixEnd_2069624 := by exact prefixLift 2069624
  have htrace : WordTrace (prefixWord ++ tailWord_2069624) baseStart_2069624 baseEnd_2069624 := by
    simpa [prefixWord, tailWord_2069624, baseEnd_2069624] using wordTrace_append hprefix tailTrace_2069624
  have hstable : (prefixWord ++ tailWord_2069624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069624).length < 2 ^ (prefixWord ++ tailWord_2069624).sum := by decide
  have hdescent : baseEnd_2069624 < baseStart_2069624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069674 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2069674 : Nat := 118140960795 + 2069674 * 2 ^ 59
def prefixEnd_2069674 : Nat := 4983230072969 + 3 ^ 40 * 2069674 * 2
def baseEnd_2069674 : Nat := 1062737560113640624656749

theorem tailTrace_2069674 : CollatzResearch.WordTrace tailWord_2069674 prefixEnd_2069674 1062737560113640624656749 := by
  unfold tailWord_2069674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871803075983011255738019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50324808202621363348634717 18871803075983011255738019)
  ·
    refine ⟨28307704613974516883607029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18871803075983011255738019 28307704613974516883607029)
    ·
      refine ⟨2653847307560110957838159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28307704613974516883607029 2653847307560110957838159)
      ·
        refine ⟨3980770961340166436757239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653847307560110957838159 3980770961340166436757239)
        ·
          refine ⟨5971156442010249655135859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980770961340166436757239 5971156442010249655135859)
          ·
            refine ⟨8956734663015374482703789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971156442010249655135859 8956734663015374482703789)
            ·
              refine ⟨3358775498630765431013921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8956734663015374482703789 3358775498630765431013921)
              ·
                refine ⟨2519081623973074073260441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358775498630765431013921 2519081623973074073260441)
                ·
                  refine ⟨1889311217979805554945331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519081623973074073260441 1889311217979805554945331)
                  ·
                    refine ⟨2833966826969708332417997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1889311217979805554945331 2833966826969708332417997)
                    ·
                      refine ⟨1062737560113640624656749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2833966826969708332417997 1062737560113640624656749)
                      ·
                        rfl

theorem cell23_2069674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2069674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069674 prefixEnd_2069674 := by exact prefixLift 2069674
  have htrace : WordTrace (prefixWord ++ tailWord_2069674) baseStart_2069674 baseEnd_2069674 := by
    simpa [prefixWord, tailWord_2069674, baseEnd_2069674] using wordTrace_append hprefix tailTrace_2069674
  have hstable : (prefixWord ++ tailWord_2069674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069674).length < 2 ^ (prefixWord ++ tailWord_2069674).sum := by decide
  have hdescent : baseEnd_2069674 < baseStart_2069674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069680 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 4, 2, 2]
def baseStart_2069680 : Nat := 118140960795 + 2069680 * 2 ^ 59
def prefixEnd_2069680 : Nat := 4983230072969 + 3 ^ 40 * 2069680 * 2
def baseEnd_2069680 : Nat := 1062740640997567601181721

theorem tailTrace_2069680 : CollatzResearch.WordTrace tailWord_2069680 prefixEnd_2069680 1062740640997567601181721 := by
  unfold tailWord_2069680
  simp only [CollatzResearch.WordTrace]
  refine ⟨37743715570955154023835247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50324954094606872031780329 37743715570955154023835247)
  ·
    refine ⟨56615573356432731035752871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37743715570955154023835247 56615573356432731035752871)
    ·
      refine ⟨84923360034649096553629307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56615573356432731035752871 84923360034649096553629307)
      ·
        refine ⟨127385040051973644830443961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84923360034649096553629307 127385040051973644830443961)
        ·
          refine ⟨95538780038980233622832971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127385040051973644830443961 95538780038980233622832971)
          ·
            refine ⟨143308170058470350434249457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95538780038980233622832971 143308170058470350434249457)
            ·
              refine ⟨107481127543852762825687093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143308170058470350434249457 107481127543852762825687093)
              ·
                refine ⟨10076355707236196514908165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107481127543852762825687093 10076355707236196514908165)
                ·
                  refine ⟨1889316695106786846545281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10076355707236196514908165 1889316695106786846545281)
                  ·
                    refine ⟨1416987521330090134908961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889316695106786846545281 1416987521330090134908961)
                    ·
                      refine ⟨1062740640997567601181721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1416987521330090134908961 1062740640997567601181721)
                      ·
                        rfl

theorem cell23_2069680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 2, 2].length) (baseStart_2069680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069680 prefixEnd_2069680 := by exact prefixLift 2069680
  have htrace : WordTrace (prefixWord ++ tailWord_2069680) baseStart_2069680 baseEnd_2069680 := by
    simpa [prefixWord, tailWord_2069680, baseEnd_2069680] using wordTrace_append hprefix tailTrace_2069680
  have hstable : (prefixWord ++ tailWord_2069680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069680).length < 2 ^ (prefixWord ++ tailWord_2069680).sum := by decide
  have hdescent : baseEnd_2069680 < baseStart_2069680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069693 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2069693 : Nat := 118140960795 + 2069693 * 2 ^ 59
def prefixEnd_2069693 : Nat := 4983230072969 + 3 ^ 40 * 2069693 * 2
def baseEnd_2069693 : Nat := 1062747316246076050319161

theorem tailTrace_2069693 : CollatzResearch.WordTrace tailWord_2069693 prefixEnd_2069693 1062747316246076050319161 := by
  unfold tailWord_2069693
  simp only [CollatzResearch.WordTrace]
  refine ⟨75487905290863211267893733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50325270193908807511929155 75487905290863211267893733)
  ·
    refine ⟨14153982242036852112730075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75487905290863211267893733 14153982242036852112730075)
    ·
      refine ⟨21230973363055278169095113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14153982242036852112730075 21230973363055278169095113)
      ·
        refine ⟨15923230022291458626821335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21230973363055278169095113 15923230022291458626821335)
        ·
          refine ⟨23884845033437187940232003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15923230022291458626821335 23884845033437187940232003)
          ·
            refine ⟨35827267550155781910348005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23884845033437187940232003 35827267550155781910348005)
            ·
              refine ⟨6717612665654209108190251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35827267550155781910348005 6717612665654209108190251)
              ·
                refine ⟨10076418998481313662285377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6717612665654209108190251 10076418998481313662285377)
                ·
                  refine ⟨7557314248860985246714033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10076418998481313662285377 7557314248860985246714033)
                  ·
                    refine ⟨5667985686645738935035525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7557314248860985246714033 5667985686645738935035525)
                    ·
                      refine ⟨1062747316246076050319161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5667985686645738935035525 1062747316246076050319161)
                      ·
                        rfl

theorem cell23_2069693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2069693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069693 prefixEnd_2069693 := by exact prefixLift 2069693
  have htrace : WordTrace (prefixWord ++ tailWord_2069693) baseStart_2069693 baseEnd_2069693 := by
    simpa [prefixWord, tailWord_2069693, baseEnd_2069693] using wordTrace_append hprefix tailTrace_2069693
  have hstable : (prefixWord ++ tailWord_2069693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069693).length < 2 ^ (prefixWord ++ tailWord_2069693).sum := by decide
  have hdescent : baseEnd_2069693 < baseStart_2069693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069753 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2069753 : Nat := 118140960795 + 2069753 * 2 ^ 59
def prefixEnd_2069753 : Nat := 4983230072969 + 3 ^ 40 * 2069753 * 2
def baseEnd_2069753 : Nat := 1062778125085345815568885

theorem tailTrace_2069753 : CollatzResearch.WordTrace tailWord_2069753 prefixEnd_2069753 1062778125085345815568885 := by
  unfold tailWord_2069753
  simp only [CollatzResearch.WordTrace]
  refine ⟨75490093670645841515077913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50326729113763894343385275 75490093670645841515077913)
  ·
    refine ⟨56617570252984381136308435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75490093670645841515077913 56617570252984381136308435)
    ·
      refine ⟨84926355379476571704462653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56617570252984381136308435 84926355379476571704462653)
      ·
        refine ⟨31847383267303714389173495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84926355379476571704462653 31847383267303714389173495)
        ·
          refine ⟨47771074900955571583760243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31847383267303714389173495 47771074900955571583760243)
          ·
            refine ⟨71656612351433357375640365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47771074900955571583760243 71656612351433357375640365)
            ·
              refine ⟨26871229631787509015865137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71656612351433357375640365 26871229631787509015865137)
              ·
                refine ⟨20153422223840631761898853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26871229631787509015865137 20153422223840631761898853)
                ·
                  refine ⟨3778766666970118455356035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20153422223840631761898853 3778766666970118455356035)
                  ·
                    refine ⟨5668150000455177683034053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3778766666970118455356035 5668150000455177683034053)
                    ·
                      refine ⟨1062778125085345815568885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5668150000455177683034053 1062778125085345815568885)
                      ·
                        rfl

theorem cell23_2069753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2069753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069753 prefixEnd_2069753 := by exact prefixLift 2069753
  have htrace : WordTrace (prefixWord ++ tailWord_2069753) baseStart_2069753 baseEnd_2069753 := by
    simpa [prefixWord, tailWord_2069753, baseEnd_2069753] using wordTrace_append hprefix tailTrace_2069753
  have hstable : (prefixWord ++ tailWord_2069753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069753).length < 2 ^ (prefixWord ++ tailWord_2069753).sum := by decide
  have hdescent : baseEnd_2069753 < baseStart_2069753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069770 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_2069770 : Nat := 118140960795 + 2069770 * 2 ^ 59
def prefixEnd_2069770 : Nat := 4983230072969 + 3 ^ 40 * 2069770 * 2
def baseEnd_2069770 : Nat := 1062786854256472249056307

theorem tailTrace_2069770 : CollatzResearch.WordTrace tailWord_2069770 prefixEnd_2069770 1062786854256472249056307 := by
  unfold tailWord_2069770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872678427896063354611691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50327142474389502278964509 18872678427896063354611691)
  ·
    refine ⟨28309017641844095031917537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18872678427896063354611691 28309017641844095031917537)
    ·
      refine ⟨21231763231383071273938153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28309017641844095031917537 21231763231383071273938153)
      ·
        refine ⟨15923822423537303455453615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21231763231383071273938153 15923822423537303455453615)
        ·
          refine ⟨23885733635305955183180423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15923822423537303455453615 23885733635305955183180423)
          ·
            refine ⟨35828600452958932774770635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23885733635305955183180423 35828600452958932774770635)
            ·
              refine ⟨53742900679438399162155953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35828600452958932774770635 53742900679438399162155953)
              ·
                refine ⟨40307175509578799371616965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53742900679438399162155953 40307175509578799371616965)
                ·
                  refine ⟨7557595408046024882178181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40307175509578799371616965 7557595408046024882178181)
                  ·
                    refine ⟨1417049139008629665408409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7557595408046024882178181 1417049139008629665408409)
                    ·
                      refine ⟨1062786854256472249056307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417049139008629665408409 1062786854256472249056307)
                      ·
                        rfl

theorem cell23_2069770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_2069770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069770 prefixEnd_2069770 := by exact prefixLift 2069770
  have htrace : WordTrace (prefixWord ++ tailWord_2069770) baseStart_2069770 baseEnd_2069770 := by
    simpa [prefixWord, tailWord_2069770, baseEnd_2069770] using wordTrace_append hprefix tailTrace_2069770
  have hstable : (prefixWord ++ tailWord_2069770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069770).length < 2 ^ (prefixWord ++ tailWord_2069770).sum := by decide
  have hdescent : baseEnd_2069770 < baseStart_2069770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069783 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2069783 : Nat := 118140960795 + 2069783 * 2 ^ 59
def prefixEnd_2069783 : Nat := 4983230072969 + 3 ^ 40 * 2069783 * 2
def baseEnd_2069783 : Nat := 1062793529504980698193747

theorem tailTrace_2069783 : CollatzResearch.WordTrace tailWord_2069783 prefixEnd_2069783 1062793529504980698193747 := by
  unfold tailWord_2069783
  simp only [CollatzResearch.WordTrace]
  refine ⟨75491187860537156638670003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50327458573691437759113335 75491187860537156638670003)
  ·
    refine ⟨113236781790805734958005005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75491187860537156638670003 113236781790805734958005005)
    ·
      refine ⟨42463793171552150609251877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113236781790805734958005005 42463793171552150609251877)
      ·
        refine ⟨7961961219666028239234727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42463793171552150609251877 7961961219666028239234727)
        ·
          refine ⟨11942941829499042358852091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961961219666028239234727 11942941829499042358852091)
          ·
            refine ⟨17914412744248563538278137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11942941829499042358852091 17914412744248563538278137)
            ·
              refine ⟨13435809558186422653708603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17914412744248563538278137 13435809558186422653708603)
              ·
                refine ⟨20153714337279633980562905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13435809558186422653708603 20153714337279633980562905)
                ·
                  refine ⟨15115285752959725485422179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20153714337279633980562905 15115285752959725485422179)
                  ·
                    refine ⟨22672928629439588228133269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15115285752959725485422179 22672928629439588228133269)
                    ·
                      refine ⟨1062793529504980698193747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22672928629439588228133269 1062793529504980698193747)
                      ·
                        rfl

theorem cell23_2069783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2069783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069783 prefixEnd_2069783 := by exact prefixLift 2069783
  have htrace : WordTrace (prefixWord ++ tailWord_2069783) baseStart_2069783 baseEnd_2069783 := by
    simpa [prefixWord, tailWord_2069783, baseEnd_2069783] using wordTrace_append hprefix tailTrace_2069783
  have hstable : (prefixWord ++ tailWord_2069783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069783).length < 2 ^ (prefixWord ++ tailWord_2069783).sum := by decide
  have hdescent : baseEnd_2069783 < baseStart_2069783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069810 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_2069810 : Nat := 118140960795 + 2069810 * 2 ^ 59
def prefixEnd_2069810 : Nat := 4983230072969 + 3 ^ 40 * 2069810 * 2
def baseEnd_2069810 : Nat := 118089710386961343617347

theorem tailTrace_2069810 : CollatzResearch.WordTrace tailWord_2069810 prefixEnd_2069810 118089710386961343617347 := by
  unfold tailWord_2069810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873043157859835062475721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50328115087626226833268589 18873043157859835062475721)
  ·
    refine ⟨14154782368394876296856791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18873043157859835062475721 14154782368394876296856791)
    ·
      refine ⟨21232173552592314445285187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154782368394876296856791 21232173552592314445285187)
      ·
        refine ⟨31848260328888471667927781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21232173552592314445285187 31848260328888471667927781)
        ·
          refine ⟨5971548811666588437736459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31848260328888471667927781 5971548811666588437736459)
          ·
            refine ⟨8957323217499882656604689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971548811666588437736459 8957323217499882656604689)
            ·
              refine ⟨6717992413124911992453517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8957323217499882656604689 6717992413124911992453517)
              ·
                refine ⟨2519247154921841997170069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6717992413124911992453517 2519247154921841997170069)
                ·
                  refine ⟨118089710386961343617347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2519247154921841997170069 118089710386961343617347)
                  ·
                    rfl

theorem cell23_2069810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_2069810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069810 prefixEnd_2069810 := by exact prefixLift 2069810
  have htrace : WordTrace (prefixWord ++ tailWord_2069810) baseStart_2069810 baseEnd_2069810 := by
    simpa [prefixWord, tailWord_2069810, baseEnd_2069810] using wordTrace_append hprefix tailTrace_2069810
  have hstable : (prefixWord ++ tailWord_2069810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069810).length < 2 ^ (prefixWord ++ tailWord_2069810).sum := by decide
  have hdescent : baseEnd_2069810 < baseStart_2069810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069821 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2069821 : Nat := 118140960795 + 2069821 * 2 ^ 59
def prefixEnd_2069821 : Nat := 4983230072969 + 3 ^ 40 * 2069821 * 2
def baseEnd_2069821 : Nat := 1062813041769851549518573

theorem tailTrace_2069821 : CollatzResearch.WordTrace tailWord_2069821 prefixEnd_2069821 1062813041769851549518573 := by
  unfold tailWord_2069821
  simp only [CollatzResearch.WordTrace]
  refine ⟨75492573834399489128553317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50328382556266326085702211 75492573834399489128553317)
  ·
    refine ⟨14154857593949904211603747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75492573834399489128553317 14154857593949904211603747)
    ·
      refine ⟨21232286390924856317405621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14154857593949904211603747 21232286390924856317405621)
      ·
        refine ⟨1990526849149205279756777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21232286390924856317405621 1990526849149205279756777)
        ·
          refine ⟨1492895136861903959817583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1990526849149205279756777 1492895136861903959817583)
          ·
            refine ⟨2239342705292855939726375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492895136861903959817583 2239342705292855939726375)
            ·
              refine ⟨3359014057939283909589563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239342705292855939726375 3359014057939283909589563)
              ·
                refine ⟨5038521086908925864384345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359014057939283909589563 5038521086908925864384345)
                ·
                  refine ⟨3778890815181694398288259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5038521086908925864384345 3778890815181694398288259)
                  ·
                    refine ⟨5668336222772541597432389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3778890815181694398288259 5668336222772541597432389)
                    ·
                      refine ⟨1062813041769851549518573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5668336222772541597432389 1062813041769851549518573)
                      ·
                        rfl

theorem cell23_2069821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2069821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069821 prefixEnd_2069821 := by exact prefixLift 2069821
  have htrace : WordTrace (prefixWord ++ tailWord_2069821) baseStart_2069821 baseEnd_2069821 := by
    simpa [prefixWord, tailWord_2069821, baseEnd_2069821] using wordTrace_append hprefix tailTrace_2069821
  have hstable : (prefixWord ++ tailWord_2069821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069821).length < 2 ^ (prefixWord ++ tailWord_2069821).sum := by decide
  have hdescent : baseEnd_2069821 < baseStart_2069821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069840 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 1, 5]
def baseStart_2069840 : Nat := 118140960795 + 2069840 * 2 ^ 59
def prefixEnd_2069840 : Nat := 4983230072969 + 3 ^ 40 * 2069840 * 2
def baseEnd_2069840 : Nat := 354274265967428991726995

theorem tailTrace_2069840 : CollatzResearch.WordTrace tailWord_2069840 prefixEnd_2069840 354274265967428991726995 := by
  unfold tailWord_2069840
  simp only [CollatzResearch.WordTrace]
  refine ⟨37746633410665327686747487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50328844547553770248996649 37746633410665327686747487)
  ·
    refine ⟨56619950115997991530121231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37746633410665327686747487 56619950115997991530121231)
    ·
      refine ⟨84929925173996987295181847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56619950115997991530121231 84929925173996987295181847)
      ·
        refine ⟨127394887760995480942772771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84929925173996987295181847 127394887760995480942772771)
        ·
          refine ⟨191092331641493221414159157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127394887760995480942772771 191092331641493221414159157)
          ·
            refine ⟨17914906091389989507577421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191092331641493221414159157 17914906091389989507577421)
            ·
              refine ⟨6718089784271246065341533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17914906091389989507577421 6718089784271246065341533)
              ·
                refine ⟨2519283669101717274503075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6718089784271246065341533 2519283669101717274503075)
                ·
                  refine ⟨3778925503652575911754613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519283669101717274503075 3778925503652575911754613)
                  ·
                    refine ⟨354274265967428991726995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3778925503652575911754613 354274265967428991726995)
                    ·
                      rfl

theorem cell23_2069840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_2069840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069840 prefixEnd_2069840 := by exact prefixLift 2069840
  have htrace : WordTrace (prefixWord ++ tailWord_2069840) baseStart_2069840 baseEnd_2069840 := by
    simpa [prefixWord, tailWord_2069840, baseEnd_2069840] using wordTrace_append hprefix tailTrace_2069840
  have hstable : (prefixWord ++ tailWord_2069840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069840).length < 2 ^ (prefixWord ++ tailWord_2069840).sum := by decide
  have hdescent : baseEnd_2069840 < baseStart_2069840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069883 : List Nat := [1, 1, 1, 1, 1, 6, 3, 9]
def baseStart_2069883 : Nat := 118140960795 + 2069883 * 2 ^ 59
def prefixEnd_2069883 : Nat := 4983230072969 + 3 ^ 40 * 2069883 * 2
def baseEnd_2069883 : Nat := 39364625095201122479381

theorem tailTrace_2069883 : CollatzResearch.WordTrace tailWord_2069883 prefixEnd_2069883 39364625095201122479381 := by
  unfold tailWord_2069883
  simp only [CollatzResearch.WordTrace]
  refine ⟨75494835160174873717310303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50329890106783249144873535 75494835160174873717310303)
  ·
    refine ⟨113242252740262310575965455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75494835160174873717310303 113242252740262310575965455)
    ·
      refine ⟨169863379110393465863948183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113242252740262310575965455 169863379110393465863948183)
      ·
        refine ⟨254795068665590198795922275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169863379110393465863948183 254795068665590198795922275)
        ·
          refine ⟨382192602998385298193883413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254795068665590198795922275 382192602998385298193883413)
          ·
            refine ⟨17915278265549310852838285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382192602998385298193883413 17915278265549310852838285)
            ·
              refine ⟨6718229349580991569814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17915278265549310852838285 6718229349580991569814357)
              ·
                refine ⟨39364625095201122479381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6718229349580991569814357 39364625095201122479381)
                ·
                  rfl

theorem cell23_2069883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 9].length) (baseStart_2069883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069883 prefixEnd_2069883 := by exact prefixLift 2069883
  have htrace : WordTrace (prefixWord ++ tailWord_2069883) baseStart_2069883 baseEnd_2069883 := by
    simpa [prefixWord, tailWord_2069883, baseEnd_2069883] using wordTrace_append hprefix tailTrace_2069883
  have hstable : (prefixWord ++ tailWord_2069883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069883).length < 2 ^ (prefixWord ++ tailWord_2069883).sum := by decide
  have hdescent : baseEnd_2069883 < baseStart_2069883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069897 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 5]
def baseStart_2069897 : Nat := 118140960795 + 2069897 * 2 ^ 59
def prefixEnd_2069897 : Nat := 4983230072969 + 3 ^ 40 * 2069897 * 2
def baseEnd_2069897 : Nat := 1062852066299593252168223

theorem tailTrace_2069897 : CollatzResearch.WordTrace tailWord_2069897 prefixEnd_2069897 1062852066299593252168223 := by
  unfold tailWord_2069897
  simp only [CollatzResearch.WordTrace]
  refine ⟨75495345782124154108319945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50330230521416102738879963 75495345782124154108319945)
  ·
    refine ⟨56621509336593115581239959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75495345782124154108319945 56621509336593115581239959)
    ·
      refine ⟨84932264004889673371859939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56621509336593115581239959 84932264004889673371859939)
      ·
        refine ⟨127398396007334510057789909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84932264004889673371859939 127398396007334510057789909)
        ·
          refine ⟨2985899906421902579479451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127398396007334510057789909 2985899906421902579479451)
          ·
            refine ⟨4478849859632853869219177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985899906421902579479451 4478849859632853869219177)
            ·
              refine ⟨3359137394724640401914383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478849859632853869219177 3359137394724640401914383)
              ·
                refine ⟨5038706092086960602871575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359137394724640401914383 5038706092086960602871575)
                ·
                  refine ⟨7558059138130440904307363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038706092086960602871575 7558059138130440904307363)
                  ·
                    refine ⟨11337088707195661356461045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7558059138130440904307363 11337088707195661356461045)
                    ·
                      refine ⟨1062852066299593252168223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11337088707195661356461045 1062852066299593252168223)
                      ·
                        rfl

theorem cell23_2069897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_2069897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069897 prefixEnd_2069897 := by exact prefixLift 2069897
  have htrace : WordTrace (prefixWord ++ tailWord_2069897) baseStart_2069897 baseEnd_2069897 := by
    simpa [prefixWord, tailWord_2069897, baseEnd_2069897] using wordTrace_append hprefix tailTrace_2069897
  have hstable : (prefixWord ++ tailWord_2069897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069897).length < 2 ^ (prefixWord ++ tailWord_2069897).sum := by decide
  have hdescent : baseEnd_2069897 < baseStart_2069897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069927 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2069927 : Nat := 118140960795 + 2069927 * 2 ^ 59
def prefixEnd_2069927 : Nat := 4983230072969 + 3 ^ 40 * 2069927 * 2
def baseEnd_2069927 : Nat := 1062867470719228134793085

theorem tailTrace_2069927 : CollatzResearch.WordTrace tailWord_2069927 prefixEnd_2069927 1062867470719228134793085 := by
  unfold tailWord_2069927
  simp only [CollatzResearch.WordTrace]
  refine ⟨75496439972015469231912035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50330959981343646154608023 75496439972015469231912035)
  ·
    refine ⟨113244659958023203847868053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75496439972015469231912035 113244659958023203847868053)
    ·
      refine ⟨5308343435532337680368815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113244659958023203847868053 5308343435532337680368815)
      ·
        refine ⟨7962515153298506520553223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308343435532337680368815 7962515153298506520553223)
        ·
          refine ⟨11943772729947759780829835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7962515153298506520553223 11943772729947759780829835)
          ·
            refine ⟨17915659094921639671244753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943772729947759780829835 17915659094921639671244753)
            ·
              refine ⟨13436744321191229753433565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17915659094921639671244753 13436744321191229753433565)
              ·
                refine ⟨5038779120446711157537587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13436744321191229753433565 5038779120446711157537587)
                ·
                  refine ⟨7558168680670066736306381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5038779120446711157537587 7558168680670066736306381)
                  ·
                    refine ⟨2834313255251275026114893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7558168680670066736306381 2834313255251275026114893)
                    ·
                      refine ⟨1062867470719228134793085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2834313255251275026114893 1062867470719228134793085)
                      ·
                        rfl

theorem cell23_2069927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2069927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069927 prefixEnd_2069927 := by exact prefixLift 2069927
  have htrace : WordTrace (prefixWord ++ tailWord_2069927) baseStart_2069927 baseEnd_2069927 := by
    simpa [prefixWord, tailWord_2069927, baseEnd_2069927] using wordTrace_append hprefix tailTrace_2069927
  have hstable : (prefixWord ++ tailWord_2069927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069927).length < 2 ^ (prefixWord ++ tailWord_2069927).sum := by decide
  have hdescent : baseEnd_2069927 < baseStart_2069927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069928 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2069928 : Nat := 118140960795 + 2069928 * 2 ^ 59
def prefixEnd_2069928 : Nat := 4983230072969 + 3 ^ 40 * 2069928 * 2
def baseEnd_2069928 : Nat := 1062867984199882630880581

theorem tailTrace_2069928 : CollatzResearch.WordTrace tailWord_2069928 prefixEnd_2069928 1062867984199882630880581 := by
  unfold tailWord_2069928
  simp only [CollatzResearch.WordTrace]
  refine ⟨37748238222505923201349219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50330984296674564268465625 37748238222505923201349219)
  ·
    refine ⟨56622357333758884802023829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37748238222505923201349219 56622357333758884802023829)
    ·
      refine ⟨2654173000019947725094867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56622357333758884802023829 2654173000019947725094867)
      ·
        refine ⟨3981259500029921587642301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654173000019947725094867 3981259500029921587642301)
        ·
          refine ⟨1492972312511220595365863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3981259500029921587642301 1492972312511220595365863)
          ·
            refine ⟨2239458468766830893048795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492972312511220595365863 2239458468766830893048795)
            ·
              refine ⟨3359187703150246339573193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239458468766830893048795 3359187703150246339573193)
              ·
                refine ⟨2519390777362684754679895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359187703150246339573193 2519390777362684754679895)
                ·
                  refine ⟨3779086166044027132019843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519390777362684754679895 3779086166044027132019843)
                  ·
                    refine ⟨5668629249066040698029765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3779086166044027132019843 5668629249066040698029765)
                    ·
                      refine ⟨1062867984199882630880581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5668629249066040698029765 1062867984199882630880581)
                      ·
                        rfl

theorem cell23_2069928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2069928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069928 prefixEnd_2069928 := by exact prefixLift 2069928
  have htrace : WordTrace (prefixWord ++ tailWord_2069928) baseStart_2069928 baseEnd_2069928 := by
    simpa [prefixWord, tailWord_2069928, baseEnd_2069928] using wordTrace_append hprefix tailTrace_2069928
  have hstable : (prefixWord ++ tailWord_2069928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069928).length < 2 ^ (prefixWord ++ tailWord_2069928).sum := by decide
  have hdescent : baseEnd_2069928 < baseStart_2069928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069960 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_2069960 : Nat := 118140960795 + 2069960 * 2 ^ 59
def prefixEnd_2069960 : Nat := 4983230072969 + 3 ^ 40 * 2069960 * 2
def baseEnd_2069960 : Nat := 354294805193608835226811

theorem tailTrace_2069960 : CollatzResearch.WordTrace tailWord_2069960 prefixEnd_2069960 354294805193608835226811 := by
  unfold tailWord_2069960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37748821790447957933931667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50331762387263943911908889 37748821790447957933931667)
  ·
    refine ⟨56623232685671936900897501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37748821790447957933931667 56623232685671936900897501)
    ·
      refine ⟨21233712257126976337836563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56623232685671936900897501 21233712257126976337836563)
      ·
        refine ⟨31850568385690464506754845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21233712257126976337836563 31850568385690464506754845)
        ·
          refine ⟨11943963144633924190033067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31850568385690464506754845 11943963144633924190033067)
          ·
            refine ⟨17915944716950886285049601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11943963144633924190033067 17915944716950886285049601)
            ·
              refine ⟨13436958537713164713787201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17915944716950886285049601 13436958537713164713787201)
              ·
                refine ⟨10077718903284873535340401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13436958537713164713787201 10077718903284873535340401)
                ·
                  refine ⟨7558289177463655151505301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10077718903284873535340401 7558289177463655151505301)
                  ·
                    refine ⟨354294805193608835226811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7558289177463655151505301 354294805193608835226811)
                    ·
                      rfl

theorem cell23_2069960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_2069960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2069960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2069960 prefixEnd_2069960 := by exact prefixLift 2069960
  have htrace : WordTrace (prefixWord ++ tailWord_2069960) baseStart_2069960 baseEnd_2069960 := by
    simpa [prefixWord, tailWord_2069960, baseEnd_2069960] using wordTrace_append hprefix tailTrace_2069960
  have hstable : (prefixWord ++ tailWord_2069960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069960).length < 2 ^ (prefixWord ++ tailWord_2069960).sum := by decide
  have hdescent : baseEnd_2069960 < baseStart_2069960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070005 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2070005 : Nat := 118140960795 + 2070005 * 2 ^ 59
def prefixEnd_2070005 : Nat := 4983230072969 + 3 ^ 40 * 2070005 * 2
def baseEnd_2070005 : Nat := 1062907522210278829617727

theorem tailTrace_2070005 : CollatzResearch.WordTrace tailWord_2070005 prefixEnd_2070005 1062907522210278829617727 := by
  unfold tailWord_2070005
  simp only [CollatzResearch.WordTrace]
  refine ⟨75499284865732888553251469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50332856577155259035500979 75499284865732888553251469)
  ·
    refine ⟨28312231824649833207469301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75499284865732888553251469 28312231824649833207469301)
    ·
      refine ⟨2654271733560921863200247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28312231824649833207469301 2654271733560921863200247)
      ·
        refine ⟨3981407600341382794800371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654271733560921863200247 3981407600341382794800371)
        ·
          refine ⟨5972111400512074192200557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981407600341382794800371 5972111400512074192200557)
          ·
            refine ⟨2239541775192027822075209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5972111400512074192200557 2239541775192027822075209)
            ·
              refine ⟨1679656331394020866556407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239541775192027822075209 1679656331394020866556407)
              ·
                refine ⟨2519484497091031299834611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679656331394020866556407 2519484497091031299834611)
                ·
                  refine ⟨3779226745636546949751917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519484497091031299834611 3779226745636546949751917)
                  ·
                    refine ⟨1417210029613705106156969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3779226745636546949751917 1417210029613705106156969)
                    ·
                      refine ⟨1062907522210278829617727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417210029613705106156969 1062907522210278829617727)
                      ·
                        rfl

theorem cell23_2070005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2070005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070005 prefixEnd_2070005 := by exact prefixLift 2070005
  have htrace : WordTrace (prefixWord ++ tailWord_2070005) baseStart_2070005 baseEnd_2070005 := by
    simpa [prefixWord, tailWord_2070005, baseEnd_2070005] using wordTrace_append hprefix tailTrace_2070005
  have hstable : (prefixWord ++ tailWord_2070005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070005).length < 2 ^ (prefixWord ++ tailWord_2070005).sum := by decide
  have hdescent : baseEnd_2070005 < baseStart_2070005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070018 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2070018 : Nat := 118140960795 + 2070018 * 2 ^ 59
def prefixEnd_2070018 : Nat := 4983230072969 + 3 ^ 40 * 2070018 * 2
def baseEnd_2070018 : Nat := 1062914197458787278755167

theorem tailTrace_2070018 : CollatzResearch.WordTrace tailWord_2070018 prefixEnd_2070018 1062914197458787278755167 := by
  unfold tailWord_2070018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874939753671447943368677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50333172676457194515649805 18874939753671447943368677)
  ·
    refine ⟨3539051203813396489381627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18874939753671447943368677 3539051203813396489381627)
    ·
      refine ⟨5308576805720094734072441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539051203813396489381627 5308576805720094734072441)
      ·
        refine ⟨3981432604290071050554331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5308576805720094734072441 3981432604290071050554331)
        ·
          refine ⟨5972148906435106575831497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981432604290071050554331 5972148906435106575831497)
          ·
            refine ⟨4479111679826329931873623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5972148906435106575831497 4479111679826329931873623)
            ·
              refine ⟨6718667519739494897810435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479111679826329931873623 6718667519739494897810435)
              ·
                refine ⟨10078001279609242346715653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6718667519739494897810435 10078001279609242346715653)
                ·
                  refine ⟨1889625239926732940009185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10078001279609242346715653 1889625239926732940009185)
                  ·
                    refine ⟨1417218929945049705006889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889625239926732940009185 1417218929945049705006889)
                    ·
                      refine ⟨1062914197458787278755167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417218929945049705006889 1062914197458787278755167)
                      ·
                        rfl

theorem cell23_2070018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2070018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070018 prefixEnd_2070018 := by exact prefixLift 2070018
  have htrace : WordTrace (prefixWord ++ tailWord_2070018) baseStart_2070018 baseEnd_2070018 := by
    simpa [prefixWord, tailWord_2070018, baseEnd_2070018] using wordTrace_append hprefix tailTrace_2070018
  have hstable : (prefixWord ++ tailWord_2070018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070018).length < 2 ^ (prefixWord ++ tailWord_2070018).sum := by decide
  have hdescent : baseEnd_2070018 < baseStart_2070018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070060 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_2070060 : Nat := 118140960795 + 2070060 * 2 ^ 59
def prefixEnd_2070060 : Nat := 4983230072969 + 3 ^ 40 * 2070060 * 2
def baseEnd_2070060 : Nat := 1062935763646276114429973

theorem tailTrace_2070060 : CollatzResearch.WordTrace tailWord_2070060 prefixEnd_2070060 1062935763646276114429973 := by
  unfold tailWord_2070060
  simp only [CollatzResearch.WordTrace]
  refine ⟨37750645440266816473251817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50334193920355755297669089 37750645440266816473251817)
  ·
    refine ⟨28312984080200112354938863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37750645440266816473251817 28312984080200112354938863)
    ·
      refine ⟨42469476120300168532408295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28312984080200112354938863 42469476120300168532408295)
      ·
        refine ⟨63704214180450252798612443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42469476120300168532408295 63704214180450252798612443)
        ·
          refine ⟨95556321270675379197918665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63704214180450252798612443 95556321270675379197918665)
          ·
            refine ⟨71667240953006534398438999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95556321270675379197918665 71667240953006534398438999)
            ·
              refine ⟨107500861429509801597658499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71667240953006534398438999 107500861429509801597658499)
              ·
                refine ⟨161251292144264702396487749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107500861429509801597658499 161251292144264702396487749)
                ·
                  refine ⟨30234617277049631699341453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161251292144264702396487749 30234617277049631699341453)
                  ·
                    refine ⟨11337981478893611887253045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30234617277049631699341453 11337981478893611887253045)
                    ·
                      refine ⟨1062935763646276114429973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11337981478893611887253045 1062935763646276114429973)
                      ·
                        rfl

theorem cell23_2070060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_2070060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070060 prefixEnd_2070060 := by exact prefixLift 2070060
  have htrace : WordTrace (prefixWord ++ tailWord_2070060) baseStart_2070060 baseEnd_2070060 := by
    simpa [prefixWord, tailWord_2070060, baseEnd_2070060] using wordTrace_append hprefix tailTrace_2070060
  have hstable : (prefixWord ++ tailWord_2070060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070060).length < 2 ^ (prefixWord ++ tailWord_2070060).sum := by decide
  have hdescent : baseEnd_2070060 < baseStart_2070060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070097 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 6]
def baseStart_2070097 : Nat := 118140960795 + 2070097 * 2 ^ 59
def prefixEnd_2070097 : Nat := 4983230072969 + 3 ^ 40 * 2070097 * 2
def baseEnd_2070097 : Nat := 118106084714499163296367

theorem tailTrace_2070097 : CollatzResearch.WordTrace tailWord_2070097 prefixEnd_2070097 118106084714499163296367 := by
  unfold tailWord_2070097
  simp only [CollatzResearch.WordTrace]
  refine ⟨75502640381399588265600545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50335093587599725510400363 75502640381399588265600545)
  ·
    refine ⟨56626980286049691199200409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75502640381399588265600545 56626980286049691199200409)
    ·
      refine ⟨42470235214537268399400307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56626980286049691199200409 42470235214537268399400307)
      ·
        refine ⟨63705352821805902599100461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42470235214537268399400307 63705352821805902599100461)
        ·
          refine ⟨23889507308177213474662673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63705352821805902599100461 23889507308177213474662673)
          ·
            refine ⟨17917130481132910105997005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23889507308177213474662673 17917130481132910105997005)
            ·
              refine ⟨6718923930424841289748877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17917130481132910105997005 6718923930424841289748877)
              ·
                refine ⟨2519596473909315483655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6718923930424841289748877 2519596473909315483655829)
                ·
                  refine ⟨118106084714499163296367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2519596473909315483655829 118106084714499163296367)
                  ·
                    rfl

theorem cell23_2070097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 6].length) (baseStart_2070097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070097 prefixEnd_2070097 := by exact prefixLift 2070097
  have htrace : WordTrace (prefixWord ++ tailWord_2070097) baseStart_2070097 baseEnd_2070097 := by
    simpa [prefixWord, tailWord_2070097, baseEnd_2070097] using wordTrace_append hprefix tailTrace_2070097
  have hstable : (prefixWord ++ tailWord_2070097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070097).length < 2 ^ (prefixWord ++ tailWord_2070097).sum := by decide
  have hdescent : baseEnd_2070097 < baseStart_2070097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070168 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 2, 3, 2]
def baseStart_2070168 : Nat := 118140960795 + 2070168 * 2 ^ 59
def prefixEnd_2070168 : Nat := 4983230072969 + 3 ^ 40 * 2070168 * 2
def baseEnd_2070168 : Nat := 1062991219556961691879477

theorem tailTrace_2070168 : CollatzResearch.WordTrace tailWord_2070168 prefixEnd_2070168 1062991219556961691879477 := by
  unfold tailWord_2070168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37752614982071183695717579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50336819976094911594290105 37752614982071183695717579)
  ·
    refine ⟨56628922473106775543576369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37752614982071183695717579 56628922473106775543576369)
    ·
      refine ⟨42471691854830081657682277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56628922473106775543576369 42471691854830081657682277)
      ·
        refine ⟨7963442222780640310815427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42471691854830081657682277 7963442222780640310815427)
        ·
          refine ⟨11945163334170960466223141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963442222780640310815427 11945163334170960466223141)
          ·
            refine ⟨2239718125157055087416839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11945163334170960466223141 2239718125157055087416839)
            ·
              refine ⟨3359577187735582631125259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239718125157055087416839 3359577187735582631125259)
              ·
                refine ⟨5039365781603373946687889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359577187735582631125259 5039365781603373946687889)
                ·
                  refine ⟨3779524336202530460015917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5039365781603373946687889 3779524336202530460015917)
                  ·
                    refine ⟨1417321626075948922505969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3779524336202530460015917 1417321626075948922505969)
                    ·
                      refine ⟨1062991219556961691879477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417321626075948922505969 1062991219556961691879477)
                      ·
                        rfl

theorem cell23_2070168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_2070168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070168 prefixEnd_2070168 := by exact prefixLift 2070168
  have htrace : WordTrace (prefixWord ++ tailWord_2070168) baseStart_2070168 baseEnd_2070168 := by
    simpa [prefixWord, tailWord_2070168, baseEnd_2070168] using wordTrace_append hprefix tailTrace_2070168
  have hstable : (prefixWord ++ tailWord_2070168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070168).length < 2 ^ (prefixWord ++ tailWord_2070168).sum := by decide
  have hdescent : baseEnd_2070168 < baseStart_2070168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070178 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2070178 : Nat := 118140960795 + 2070178 * 2 ^ 59
def prefixEnd_2070178 : Nat := 4983230072969 + 3 ^ 40 * 2070178 * 2
def baseEnd_2070178 : Nat := 354332118121168884251477

theorem tailTrace_2070178 : CollatzResearch.WordTrace tailWord_2070178 prefixEnd_2070178 354332118121168884251477 := by
  unfold tailWord_2070178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18876398673526534774824797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50337063129404092732866125 18876398673526534774824797)
  ·
    refine ⟨7078649502572450540559299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18876398673526534774824797 7078649502572450540559299)
    ·
      refine ⟨10617974253858675810838949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7078649502572450540559299 10617974253858675810838949)
      ·
        refine ⟨1990870172598501714532303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10617974253858675810838949 1990870172598501714532303)
        ·
          refine ⟨2986305258897752571798455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990870172598501714532303 2986305258897752571798455)
          ·
            refine ⟨4479457888346628857697683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986305258897752571798455 4479457888346628857697683)
            ·
              refine ⟨6719186832519943286546525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479457888346628857697683 6719186832519943286546525)
              ·
                refine ⟨2519695062194978732454947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6719186832519943286546525 2519695062194978732454947)
                ·
                  refine ⟨3779542593292468098682421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519695062194978732454947 3779542593292468098682421)
                  ·
                    refine ⟨354332118121168884251477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3779542593292468098682421 354332118121168884251477)
                    ·
                      rfl

theorem cell23_2070178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2070178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070178 prefixEnd_2070178 := by exact prefixLift 2070178
  have htrace : WordTrace (prefixWord ++ tailWord_2070178) baseStart_2070178 baseEnd_2070178 := by
    simpa [prefixWord, tailWord_2070178, baseEnd_2070178] using wordTrace_append hprefix tailTrace_2070178
  have hstable : (prefixWord ++ tailWord_2070178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070178).length < 2 ^ (prefixWord ++ tailWord_2070178).sum := by decide
  have hdescent : baseEnd_2070178 < baseStart_2070178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070181 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 1, 1, 4]
def baseStart_2070181 : Nat := 118140960795 + 2070181 * 2 ^ 59
def prefixEnd_2070181 : Nat := 4983230072969 + 3 ^ 40 * 2070181 * 2
def baseEnd_2070181 : Nat := 1062997894805470141016917

theorem tailTrace_2070181 : CollatzResearch.WordTrace tailWord_2070181 prefixEnd_2070181 1062997894805470141016917 := by
  unfold tailWord_2070181
  simp only [CollatzResearch.WordTrace]
  refine ⟨75505704113095270611658397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50337136075396847074438931 75505704113095270611658397)
  ·
    refine ⟨28314639042410726479371899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75505704113095270611658397 28314639042410726479371899)
    ·
      refine ⟨42471958563616089719057849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28314639042410726479371899 42471958563616089719057849)
      ·
        refine ⟨31853968922712067289293387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42471958563616089719057849 31853968922712067289293387)
        ·
          refine ⟨47780953384068100933940081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31853968922712067289293387 47780953384068100933940081)
          ·
            refine ⟨35835715038051075700455061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47780953384068100933940081 35835715038051075700455061)
            ·
              refine ⟨1679799142408644173458831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35835715038051075700455061 1679799142408644173458831)
              ·
                refine ⟨2519698713612966260188247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679799142408644173458831 2519698713612966260188247)
                ·
                  refine ⟨3779548070419449390282371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519698713612966260188247 3779548070419449390282371)
                  ·
                    refine ⟨5669322105629174085423557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3779548070419449390282371 5669322105629174085423557)
                    ·
                      refine ⟨1062997894805470141016917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5669322105629174085423557 1062997894805470141016917)
                      ·
                        rfl

theorem cell23_2070181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_2070181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070181 prefixEnd_2070181 := by exact prefixLift 2070181
  have htrace : WordTrace (prefixWord ++ tailWord_2070181) baseStart_2070181 baseEnd_2070181 := by
    simpa [prefixWord, tailWord_2070181, baseEnd_2070181] using wordTrace_append hprefix tailTrace_2070181
  have hstable : (prefixWord ++ tailWord_2070181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070181).length < 2 ^ (prefixWord ++ tailWord_2070181).sum := by decide
  have hdescent : baseEnd_2070181 < baseStart_2070181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070218 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_2070218 : Nat := 118140960795 + 2070218 * 2 ^ 59
def prefixEnd_2070218 : Nat := 4983230072969 + 3 ^ 40 * 2070218 * 2
def baseEnd_2070218 : Nat := 1063016893589686496254247

theorem tailTrace_2070218 : CollatzResearch.WordTrace tailWord_2070218 prefixEnd_2070218 1063016893589686496254247 := by
  unfold tailWord_2070218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18876763403490306482688827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50338035742640817287170205 18876763403490306482688827)
  ·
    refine ⟨28315145105235459724033241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18876763403490306482688827 28315145105235459724033241)
    ·
      refine ⟨21236358828926594793024931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28315145105235459724033241 21236358828926594793024931)
      ·
        refine ⟨31854538243389892189537397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21236358828926594793024931 31854538243389892189537397)
        ·
          refine ⟨2986362960317802392769131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31854538243389892189537397 2986362960317802392769131)
          ·
            refine ⟨4479544440476703589153697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986362960317802392769131 4479544440476703589153697)
            ·
              refine ⟨3359658330357527691865273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4479544440476703589153697 3359658330357527691865273)
              ·
                refine ⟨2519743747768145768898955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359658330357527691865273 2519743747768145768898955)
                ·
                  refine ⟨3779615621652218653348433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519743747768145768898955 3779615621652218653348433)
                  ·
                    refine ⟨2834711716239163990011325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3779615621652218653348433 2834711716239163990011325)
                    ·
                      refine ⟨1063016893589686496254247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2834711716239163990011325 1063016893589686496254247)
                      ·
                        rfl

theorem cell23_2070218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_2070218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070218 prefixEnd_2070218 := by exact prefixLift 2070218
  have htrace : WordTrace (prefixWord ++ tailWord_2070218) baseStart_2070218 baseEnd_2070218 := by
    simpa [prefixWord, tailWord_2070218, baseEnd_2070218] using wordTrace_append hprefix tailTrace_2070218
  have hstable : (prefixWord ++ tailWord_2070218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070218).length < 2 ^ (prefixWord ++ tailWord_2070218).sum := by decide
  have hdescent : baseEnd_2070218 < baseStart_2070218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070221 : List Nat := [1, 6, 2, 1, 1, 2, 1, 9]
def baseStart_2070221 : Nat := 118140960795 + 2070221 * 2 ^ 59
def prefixEnd_2070221 : Nat := 4983230072969 + 3 ^ 40 * 2070221 * 2
def baseEnd_2070221 : Nat := 39371053112283332759879

theorem tailTrace_2070221 : CollatzResearch.WordTrace tailWord_2070221 prefixEnd_2070221 39371053112283332759879 := by
  unfold tailWord_2070221
  simp only [CollatzResearch.WordTrace]
  refine ⟨75507163032950357443114517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50338108688633571628743011 75507163032950357443114517)
  ·
    refine ⟨3539398267169548005145993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75507163032950357443114517 3539398267169548005145993)
    ·
      refine ⟨2654548700377161003859495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3539398267169548005145993 2654548700377161003859495)
      ·
        refine ⟨3981823050565741505789243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654548700377161003859495 3981823050565741505789243)
        ·
          refine ⟨5972734575848612258683865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981823050565741505789243 5972734575848612258683865)
          ·
            refine ⟨4479550931886459194012899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5972734575848612258683865 4479550931886459194012899)
            ·
              refine ⟨6719326397829688791019349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479550931886459194012899 6719326397829688791019349)
              ·
                refine ⟨39371053112283332759879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6719326397829688791019349 39371053112283332759879)
                ·
                  rfl

theorem cell23_2070221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 9].length) (baseStart_2070221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070221 prefixEnd_2070221 := by exact prefixLift 2070221
  have htrace : WordTrace (prefixWord ++ tailWord_2070221) baseStart_2070221 baseEnd_2070221 := by
    simpa [prefixWord, tailWord_2070221, baseEnd_2070221] using wordTrace_append hprefix tailTrace_2070221
  have hstable : (prefixWord ++ tailWord_2070221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070221).length < 2 ^ (prefixWord ++ tailWord_2070221).sum := by decide
  have hdescent : baseEnd_2070221 < baseStart_2070221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070254 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_2070254 : Nat := 118140960795 + 2070254 * 2 ^ 59
def prefixEnd_2070254 : Nat := 4983230072969 + 3 ^ 40 * 2070254 * 2
def baseEnd_2070254 : Nat := 1063035378893248355404081

theorem tailTrace_2070254 : CollatzResearch.WordTrace tailWord_2070254 prefixEnd_2070254 1063035378893248355404081 := by
  unfold tailWord_2070254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9438545830228850509883227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50338911094553869386043877 9438545830228850509883227)
  ·
    refine ⟨14157818745343275764824841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9438545830228850509883227 14157818745343275764824841)
    ·
      refine ⟨10618364059007456823618631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14157818745343275764824841 10618364059007456823618631)
      ·
        refine ⟨15927546088511185235427947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10618364059007456823618631 15927546088511185235427947)
        ·
          refine ⟨23891319132766777853141921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15927546088511185235427947 23891319132766777853141921)
          ·
            refine ⟨17918489349575083389856441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23891319132766777853141921 17918489349575083389856441)
            ·
              refine ⟨13438867012181312542392331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17918489349575083389856441 13438867012181312542392331)
              ·
                refine ⟨20158300518271968813588497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13438867012181312542392331 20158300518271968813588497)
                ·
                  refine ⟨15118725388703976610191373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20158300518271968813588497 15118725388703976610191373)
                  ·
                    refine ⟨5669522020763991228821765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15118725388703976610191373 5669522020763991228821765)
                    ·
                      refine ⟨1063035378893248355404081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5669522020763991228821765 1063035378893248355404081)
                      ·
                        rfl

theorem cell23_2070254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_2070254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070254 prefixEnd_2070254 := by exact prefixLift 2070254
  have htrace : WordTrace (prefixWord ++ tailWord_2070254) baseStart_2070254 baseEnd_2070254 := by
    simpa [prefixWord, tailWord_2070254, baseEnd_2070254] using wordTrace_append hprefix tailTrace_2070254
  have hstable : (prefixWord ++ tailWord_2070254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070254).length < 2 ^ (prefixWord ++ tailWord_2070254).sum := by decide
  have hdescent : baseEnd_2070254 < baseStart_2070254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070287 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 7]
def baseStart_2070287 : Nat := 118140960795 + 2070287 * 2 ^ 59
def prefixEnd_2070287 : Nat := 4983230072969 + 3 ^ 40 * 2070287 * 2
def baseEnd_2070287 : Nat := 1063052323754846726291429

theorem tailTrace_2070287 : CollatzResearch.WordTrace tailWord_2070287 prefixEnd_2070287 1063052323754846726291429 := by
  unfold tailWord_2070287
  simp only [CollatzResearch.WordTrace]
  refine ⟨75509570250711250715017115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50339713500474167143344743 75509570250711250715017115)
  ·
    refine ⟨113264355376066876072525673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75509570250711250715017115 113264355376066876072525673)
    ·
      refine ⟨84948266532050157054394255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113264355376066876072525673 84948266532050157054394255)
      ·
        refine ⟨127422399798075235581591383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84948266532050157054394255 127422399798075235581591383)
        ·
          refine ⟨191133599697112853372387075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127422399798075235581591383 191133599697112853372387075)
          ·
            refine ⟨286700399545669280058580613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191133599697112853372387075 286700399545669280058580613)
            ·
              refine ⟨53756324914812990010983865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286700399545669280058580613 53756324914812990010983865)
              ·
                refine ⟨40317243686109742508237899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53756324914812990010983865 40317243686109742508237899)
                ·
                  refine ⟨60475865529164613762356849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40317243686109742508237899 60475865529164613762356849)
                  ·
                    refine ⟨45356899146873460321767637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60475865529164613762356849 45356899146873460321767637)
                    ·
                      refine ⟨1063052323754846726291429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 45356899146873460321767637 1063052323754846726291429)
                      ·
                        rfl

theorem cell23_2070287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_2070287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070287 prefixEnd_2070287 := by exact prefixLift 2070287
  have htrace : WordTrace (prefixWord ++ tailWord_2070287) baseStart_2070287 baseEnd_2070287 := by
    simpa [prefixWord, tailWord_2070287, baseEnd_2070287] using wordTrace_append hprefix tailTrace_2070287
  have hstable : (prefixWord ++ tailWord_2070287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070287).length < 2 ^ (prefixWord ++ tailWord_2070287).sum := by decide
  have hdescent : baseEnd_2070287 < baseStart_2070287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070297 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_2070297 : Nat := 118140960795 + 2070297 * 2 ^ 59
def prefixEnd_2070297 : Nat := 4983230072969 + 3 ^ 40 * 2070297 * 2
def baseEnd_2070297 : Nat := 1063057458561391687166383

theorem tailTrace_2070297 : CollatzResearch.WordTrace tailWord_2070297 prefixEnd_2070297 1063057458561391687166383 := by
  unfold tailWord_2070297
  simp only [CollatzResearch.WordTrace]
  refine ⟨75509934980675022422881145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50339956653783348281920763 75509934980675022422881145)
  ·
    refine ⟨56632451235506266817160859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75509934980675022422881145 56632451235506266817160859)
    ·
      refine ⟨84948676853259400225741289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56632451235506266817160859 84948676853259400225741289)
      ·
        refine ⟨63711507639944550169305967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84948676853259400225741289 63711507639944550169305967)
        ·
          refine ⟨95567261459916825253958951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63711507639944550169305967 95567261459916825253958951)
          ·
            refine ⟨143350892189875237880938427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95567261459916825253958951 143350892189875237880938427)
            ·
              refine ⟨215026338284812856821407641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143350892189875237880938427 215026338284812856821407641)
              ·
                refine ⟨161269753713609642616055731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215026338284812856821407641 161269753713609642616055731)
                ·
                  refine ⟨241904630570414463924083597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161269753713609642616055731 241904630570414463924083597)
                  ·
                    refine ⟨90714236463905423971531349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241904630570414463924083597 90714236463905423971531349)
                    ·
                      refine ⟨1063057458561391687166383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 90714236463905423971531349 1063057458561391687166383)
                      ·
                        rfl

theorem cell23_2070297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_2070297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070297 prefixEnd_2070297 := by exact prefixLift 2070297
  have htrace : WordTrace (prefixWord ++ tailWord_2070297) baseStart_2070297 baseEnd_2070297 := by
    simpa [prefixWord, tailWord_2070297, baseEnd_2070297] using wordTrace_append hprefix tailTrace_2070297
  have hstable : (prefixWord ++ tailWord_2070297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070297).length < 2 ^ (prefixWord ++ tailWord_2070297).sum := by decide
  have hdescent : baseEnd_2070297 < baseStart_2070297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070305 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_2070305 : Nat := 118140960795 + 2070305 * 2 ^ 59
def prefixEnd_2070305 : Nat := 4983230072969 + 3 ^ 40 * 2070305 * 2
def baseEnd_2070305 : Nat := 1063061566406627655866347

theorem tailTrace_2070305 : CollatzResearch.WordTrace tailWord_2070305 prefixEnd_2070305 1063061566406627655866347 := by
  unfold tailWord_2070305
  simp only [CollatzResearch.WordTrace]
  refine ⟨75510226764646039789172369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50340151176430693192781579 75510226764646039789172369)
  ·
    refine ⟨56632670073484529841879277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75510226764646039789172369 56632670073484529841879277)
    ·
      refine ⟨21237251277556698690704729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56632670073484529841879277 21237251277556698690704729)
      ·
        refine ⟨15927938458167524018028547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21237251277556698690704729 15927938458167524018028547)
        ·
          refine ⟨23891907687251286027042821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15927938458167524018028547 23891907687251286027042821)
          ·
            refine ⟨4479732691359616130070529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23891907687251286027042821 4479732691359616130070529)
            ·
              refine ⟨3359799518519712097552897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4479732691359616130070529 3359799518519712097552897)
              ·
                refine ⟨2519849638889784073164673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359799518519712097552897 2519849638889784073164673)
                ·
                  refine ⟨1889887229167338054873505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2519849638889784073164673 1889887229167338054873505)
                  ·
                    refine ⟨1417415421875503541155129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1889887229167338054873505 1417415421875503541155129)
                    ·
                      refine ⟨1063061566406627655866347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417415421875503541155129 1063061566406627655866347)
                      ·
                        rfl

theorem cell23_2070305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_2070305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070305 prefixEnd_2070305 := by exact prefixLift 2070305
  have htrace : WordTrace (prefixWord ++ tailWord_2070305) baseStart_2070305 baseEnd_2070305 := by
    simpa [prefixWord, tailWord_2070305, baseEnd_2070305] using wordTrace_append hprefix tailTrace_2070305
  have hstable : (prefixWord ++ tailWord_2070305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070305).length < 2 ^ (prefixWord ++ tailWord_2070305).sum := by decide
  have hdescent : baseEnd_2070305 < baseStart_2070305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070318 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2070318 : Nat := 118140960795 + 2070318 * 2 ^ 59
def prefixEnd_2070318 : Nat := 4983230072969 + 3 ^ 40 * 2070318 * 2
def baseEnd_2070318 : Nat := 1063068241655136105003787

theorem tailTrace_2070318 : CollatzResearch.WordTrace tailWord_2070318 prefixEnd_2070318 1063068241655136105003787 := by
  unfold tailWord_2070318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9438837614199867876174451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50340467275732628672930405 9438837614199867876174451)
  ·
    refine ⟨14158256421299801814261677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9438837614199867876174451 14158256421299801814261677)
    ·
      refine ⟨5309346157987425680348129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14158256421299801814261677 5309346157987425680348129)
      ·
        refine ⟨3982009618490569260261097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5309346157987425680348129 3982009618490569260261097)
        ·
          refine ⟨2986507213867926945195823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982009618490569260261097 2986507213867926945195823)
          ·
            refine ⟨4479760820801890417793735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986507213867926945195823 4479760820801890417793735)
            ·
              refine ⟨6719641231202835626690603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479760820801890417793735 6719641231202835626690603)
              ·
                refine ⟨10079461846804253440035905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719641231202835626690603 10079461846804253440035905)
                ·
                  refine ⟨7559596385103190080026929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10079461846804253440035905 7559596385103190080026929)
                  ·
                    refine ⟨5669697288827392560020197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559596385103190080026929 5669697288827392560020197)
                    ·
                      refine ⟨1063068241655136105003787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5669697288827392560020197 1063068241655136105003787)
                      ·
                        rfl

theorem cell23_2070318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2070318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070318 prefixEnd_2070318 := by exact prefixLift 2070318
  have htrace : WordTrace (prefixWord ++ tailWord_2070318) baseStart_2070318 baseEnd_2070318 := by
    simpa [prefixWord, tailWord_2070318, baseEnd_2070318] using wordTrace_append hprefix tailTrace_2070318
  have hstable : (prefixWord ++ tailWord_2070318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070318).length < 2 ^ (prefixWord ++ tailWord_2070318).sum := by decide
  have hdescent : baseEnd_2070318 < baseStart_2070318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070321 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 3]
def baseStart_2070321 : Nat := 118140960795 + 2070321 * 2 ^ 59
def prefixEnd_2070321 : Nat := 4983230072969 + 3 ^ 40 * 2070321 * 2
def baseEnd_2070321 : Nat := 1063069782097099593266273

theorem tailTrace_2070321 : CollatzResearch.WordTrace tailWord_2070321 prefixEnd_2070321 1063069782097099593266273 := by
  unfold tailWord_2070321
  simp only [CollatzResearch.WordTrace]
  refine ⟨75510810332588074521754817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50340540221725383014503211 75510810332588074521754817)
  ·
    refine ⟨56633107749441055891316113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75510810332588074521754817 56633107749441055891316113)
    ·
      refine ⟨42474830812080791918487085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56633107749441055891316113 42474830812080791918487085)
      ·
        refine ⟨15928061554530296969432657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42474830812080791918487085 15928061554530296969432657)
        ·
          refine ⟨11946046165897722727074493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15928061554530296969432657 11946046165897722727074493)
          ·
            refine ⟨4479767312211646022652935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11946046165897722727074493 4479767312211646022652935)
            ·
              refine ⟨6719650968317469033979403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479767312211646022652935 6719650968317469033979403)
              ·
                refine ⟨10079476452476203550969105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6719650968317469033979403 10079476452476203550969105)
                ·
                  refine ⟨7559607339357152663226829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10079476452476203550969105 7559607339357152663226829)
                  ·
                    refine ⟨2834852752258932248710061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7559607339357152663226829 2834852752258932248710061)
                    ·
                      refine ⟨1063069782097099593266273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2834852752258932248710061 1063069782097099593266273)
                      ·
                        rfl

theorem cell23_2070321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_2070321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070321 prefixEnd_2070321 := by exact prefixLift 2070321
  have htrace : WordTrace (prefixWord ++ tailWord_2070321) baseStart_2070321 baseEnd_2070321 := by
    simpa [prefixWord, tailWord_2070321, baseEnd_2070321] using wordTrace_append hprefix tailTrace_2070321
  have hstable : (prefixWord ++ tailWord_2070321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070321).length < 2 ^ (prefixWord ++ tailWord_2070321).sum := by decide
  have hdescent : baseEnd_2070321 < baseStart_2070321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070361 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 4, 4, 2]
def baseStart_2070361 : Nat := 118140960795 + 2070361 * 2 ^ 59
def prefixEnd_2070361 : Nat := 4983230072969 + 3 ^ 40 * 2070361 * 2
def baseEnd_2070361 : Nat := 1063090321323279436766089

theorem tailTrace_2070361 : CollatzResearch.WordTrace tailWord_2070361 prefixEnd_2070361 1063090321323279436766089 := by
  unfold tailWord_2070361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75512269252443161353210937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50341512834962107568807291 75512269252443161353210937)
  ·
    refine ⟨56634201939332371014908203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75512269252443161353210937 56634201939332371014908203)
    ·
      refine ⟨84951302908998556522362305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56634201939332371014908203 84951302908998556522362305)
      ·
        refine ⟨63713477181748917391771729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84951302908998556522362305 63713477181748917391771729)
        ·
          refine ⟨47785107886311688043828797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63713477181748917391771729 47785107886311688043828797)
          ·
            refine ⟨17919415457366883016435799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47785107886311688043828797 17919415457366883016435799)
            ·
              refine ⟨26879123186050324524653699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17919415457366883016435799 26879123186050324524653699)
              ·
                refine ⟨40318684779075486786980549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26879123186050324524653699 40318684779075486786980549)
                ·
                  refine ⟨7559753396076653772558853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40318684779075486786980549 7559753396076653772558853)
                  ·
                    refine ⟨1417453761764372582354785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7559753396076653772558853 1417453761764372582354785)
                    ·
                      refine ⟨1063090321323279436766089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417453761764372582354785 1063090321323279436766089)
                      ·
                        rfl

theorem cell23_2070361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_2070361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070361 prefixEnd_2070361 := by exact prefixLift 2070361
  have htrace : WordTrace (prefixWord ++ tailWord_2070361) baseStart_2070361 baseEnd_2070361 := by
    simpa [prefixWord, tailWord_2070361, baseEnd_2070361] using wordTrace_append hprefix tailTrace_2070361
  have hstable : (prefixWord ++ tailWord_2070361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070361).length < 2 ^ (prefixWord ++ tailWord_2070361).sum := by decide
  have hdescent : baseEnd_2070361 < baseStart_2070361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070381 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2070381 : Nat := 118140960795 + 2070381 * 2 ^ 59
def prefixEnd_2070381 : Nat := 4983230072969 + 3 ^ 40 * 2070381 * 2
def baseEnd_2070381 : Nat := 1063100590936369358515997

theorem tailTrace_2070381 : CollatzResearch.WordTrace tailWord_2070381 prefixEnd_2070381 1063100590936369358515997 := by
  unfold tailWord_2070381
  simp only [CollatzResearch.WordTrace]
  refine ⟨75512998712370704768938997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50341999141580469845959331 75512998712370704768938997)
  ·
    refine ⟨7079343629284753572088031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75512998712370704768938997 7079343629284753572088031)
    ·
      refine ⟨10619015443927130358132047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079343629284753572088031 10619015443927130358132047)
      ·
        refine ⟨15928523165890695537198071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619015443927130358132047 15928523165890695537198071)
        ·
          refine ⟨23892784748836043305797107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15928523165890695537198071 23892784748836043305797107)
          ·
            refine ⟨35839177123254064958695661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23892784748836043305797107 35839177123254064958695661)
            ·
              refine ⟨13439691421220274359510873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35839177123254064958695661 13439691421220274359510873)
              ·
                refine ⟨10079768565915205769633155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13439691421220274359510873 10079768565915205769633155)
                ·
                  refine ⟨15119652848872808654449733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10079768565915205769633155 15119652848872808654449733)
                  ·
                    refine ⟨2834934909163651622709325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15119652848872808654449733 2834934909163651622709325)
                    ·
                      refine ⟨1063100590936369358515997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2834934909163651622709325 1063100590936369358515997)
                      ·
                        rfl

theorem cell23_2070381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2070381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070381 prefixEnd_2070381 := by exact prefixLift 2070381
  have htrace : WordTrace (prefixWord ++ tailWord_2070381) baseStart_2070381 baseEnd_2070381 := by
    simpa [prefixWord, tailWord_2070381, baseEnd_2070381] using wordTrace_append hprefix tailTrace_2070381
  have hstable : (prefixWord ++ tailWord_2070381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070381).length < 2 ^ (prefixWord ++ tailWord_2070381).sum := by decide
  have hdescent : baseEnd_2070381 < baseStart_2070381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070451 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 4]
def baseStart_2070451 : Nat := 118140960795 + 2070451 * 2 ^ 59
def prefixEnd_2070451 : Nat := 4983230072969 + 3 ^ 40 * 2070451 * 2
def baseEnd_2070451 : Nat := 1063136534582184084640675

theorem tailTrace_2070451 : CollatzResearch.WordTrace tailWord_2070451 prefixEnd_2070451 1063136534582184084640675 := by
  unfold tailWord_2070451
  simp only [CollatzResearch.WordTrace]
  refine ⟨75515551822117106723987207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50343701214744737815991471 75515551822117106723987207)
  ·
    refine ⟨113273327733175660085980811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75515551822117106723987207 113273327733175660085980811)
    ·
      refine ⟨169909991599763490128971217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113273327733175660085980811 169909991599763490128971217)
      ·
        refine ⟨127432493699822617596728413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169909991599763490128971217 127432493699822617596728413)
        ·
          refine ⟨47787185137433481598773155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127432493699822617596728413 47787185137433481598773155)
          ·
            refine ⟨71680777706150222398159733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47787185137433481598773155 71680777706150222398159733)
            ·
              refine ⟨6720072909951583349827475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71680777706150222398159733 6720072909951583349827475)
              ·
                refine ⟨10080109364927375024741213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720072909951583349827475 10080109364927375024741213)
                ·
                  refine ⟨3780041011847765634277955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10080109364927375024741213 3780041011847765634277955)
                  ·
                    refine ⟨5670061517771648451416933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3780041011847765634277955 5670061517771648451416933)
                    ·
                      refine ⟨1063136534582184084640675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5670061517771648451416933 1063136534582184084640675)
                      ·
                        rfl

theorem cell23_2070451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_2070451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070451 prefixEnd_2070451 := by exact prefixLift 2070451
  have htrace : WordTrace (prefixWord ++ tailWord_2070451) baseStart_2070451 baseEnd_2070451 := by
    simpa [prefixWord, tailWord_2070451, baseEnd_2070451] using wordTrace_append hprefix tailTrace_2070451
  have hstable : (prefixWord ++ tailWord_2070451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070451).length < 2 ^ (prefixWord ++ tailWord_2070451).sum := by decide
  have hdescent : baseEnd_2070451 < baseStart_2070451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070461 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2070461 : Nat := 118140960795 + 2070461 * 2 ^ 59
def prefixEnd_2070461 : Nat := 4983230072969 + 3 ^ 40 * 2070461 * 2
def baseEnd_2070461 : Nat := 354380556462909681838543

theorem tailTrace_2070461 : CollatzResearch.WordTrace tailWord_2070461 prefixEnd_2070461 354380556462909681838543 := by
  unfold tailWord_2070461
  simp only [CollatzResearch.WordTrace]
  refine ⟨75515916552080878431851237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50343944368053918954567491 75515916552080878431851237)
  ·
    refine ⟨14159234353515164705972107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75515916552080878431851237 14159234353515164705972107)
    ·
      refine ⟨21238851530272747058958161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14159234353515164705972107 21238851530272747058958161)
      ·
        refine ⟨15929138647704560294218621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21238851530272747058958161 15929138647704560294218621)
        ·
          refine ⟨5973426992889210110331983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15929138647704560294218621 5973426992889210110331983)
          ·
            refine ⟨8960140489333815165497975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5973426992889210110331983 8960140489333815165497975)
            ·
              refine ⟨13440210734000722748246963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960140489333815165497975 13440210734000722748246963)
              ·
                refine ⟨20160316101001084122370445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13440210734000722748246963 20160316101001084122370445)
                ·
                  refine ⟨7560118537875406545888917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20160316101001084122370445 7560118537875406545888917)
                  ·
                    refine ⟨354380556462909681838543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7560118537875406545888917 354380556462909681838543)
                    ·
                      rfl

theorem cell23_2070461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2070461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070461 prefixEnd_2070461 := by exact prefixLift 2070461
  have htrace : WordTrace (prefixWord ++ tailWord_2070461) baseStart_2070461 baseEnd_2070461 := by
    simpa [prefixWord, tailWord_2070461, baseEnd_2070461] using wordTrace_append hprefix tailTrace_2070461
  have hstable : (prefixWord ++ tailWord_2070461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070461).length < 2 ^ (prefixWord ++ tailWord_2070461).sum := by decide
  have hdescent : baseEnd_2070461 < baseStart_2070461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070528 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 5, 3, 2]
def baseStart_2070528 : Nat := 118140960795 + 2070528 * 2 ^ 59
def prefixEnd_2070528 : Nat := 4983230072969 + 3 ^ 40 * 2070528 * 2
def baseEnd_2070528 : Nat := 1063176072592580283377821

theorem tailTrace_2070528 : CollatzResearch.WordTrace tailWord_2070528 prefixEnd_2070528 1063176072592580283377821 := by
  unfold tailWord_2070528
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759180121419074437270119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50345573495225432583026825 37759180121419074437270119)
  ·
    refine ⟨56638770182128611655905179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37759180121419074437270119 56638770182128611655905179)
    ·
      refine ⟨84958155273192917483857769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56638770182128611655905179 84958155273192917483857769)
      ·
        refine ⟨63718616454894688112893327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84958155273192917483857769 63718616454894688112893327)
        ·
          refine ⟨95577924682342032169339991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63718616454894688112893327 95577924682342032169339991)
          ·
            refine ⟨143366887023513048254009987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95577924682342032169339991 143366887023513048254009987)
            ·
              refine ⟨215050330535269572381014981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143366887023513048254009987 215050330535269572381014981)
              ·
                refine ⟨40321936975363044821440309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215050330535269572381014981 40321936975363044821440309)
                ·
                  refine ⟨3780181591440285452010029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40321936975363044821440309 3780181591440285452010029)
                  ·
                    refine ⟨1417568096790107044503761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780181591440285452010029 1417568096790107044503761)
                    ·
                      refine ⟨1063176072592580283377821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417568096790107044503761 1063176072592580283377821)
                      ·
                        rfl

theorem cell23_2070528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_2070528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070528 prefixEnd_2070528 := by exact prefixLift 2070528
  have htrace : WordTrace (prefixWord ++ tailWord_2070528) baseStart_2070528 baseEnd_2070528 := by
    simpa [prefixWord, tailWord_2070528, baseEnd_2070528] using wordTrace_append hprefix tailTrace_2070528
  have hstable : (prefixWord ++ tailWord_2070528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070528).length < 2 ^ (prefixWord ++ tailWord_2070528).sum := by decide
  have hdescent : baseEnd_2070528 < baseStart_2070528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070535 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2070535 : Nat := 118140960795 + 2070535 * 2 ^ 59
def prefixEnd_2070535 : Nat := 4983230072969 + 3 ^ 40 * 2070535 * 2
def baseEnd_2070535 : Nat := 1063179666957161755990289

theorem tailTrace_2070535 : CollatzResearch.WordTrace tailWord_2070535 prefixEnd_2070535 1063179666957161755990289 := by
  unfold tailWord_2070535
  simp only [CollatzResearch.WordTrace]
  refine ⟨75518615553812789070045059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50345743702541859380030039 75518615553812789070045059)
  ·
    refine ⟨113277923330719183605067589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75518615553812789070045059 113277923330719183605067589)
    ·
      refine ⟨21239610624509846925950173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113277923330719183605067589 21239610624509846925950173)
      ·
        refine ⟨7964853984191192597231315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21239610624509846925950173 7964853984191192597231315)
        ·
          refine ⟨11947280976286788895846973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964853984191192597231315 11947280976286788895846973)
          ·
            refine ⟨4480230366107545835942615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11947280976286788895846973 4480230366107545835942615)
            ·
              refine ⟨6720345549161318753913923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480230366107545835942615 6720345549161318753913923)
              ·
                refine ⟨10080518323741978130870885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720345549161318753913923 10080518323741978130870885)
                ·
                  refine ⟨1890097185701620899538291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10080518323741978130870885 1890097185701620899538291)
                  ·
                    refine ⟨2835145778552431349307437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890097185701620899538291 2835145778552431349307437)
                    ·
                      refine ⟨1063179666957161755990289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2835145778552431349307437 1063179666957161755990289)
                      ·
                        rfl

theorem cell23_2070535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2070535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070535 prefixEnd_2070535 := by exact prefixLift 2070535
  have htrace : WordTrace (prefixWord ++ tailWord_2070535) baseStart_2070535 baseEnd_2070535 := by
    simpa [prefixWord, tailWord_2070535, baseEnd_2070535] using wordTrace_append hprefix tailTrace_2070535
  have hstable : (prefixWord ++ tailWord_2070535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070535).length < 2 ^ (prefixWord ++ tailWord_2070535).sum := by decide
  have hdescent : baseEnd_2070535 < baseStart_2070535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070552 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 2, 1, 3]
def baseStart_2070552 : Nat := 118140960795 + 2070552 * 2 ^ 59
def prefixEnd_2070552 : Nat := 4983230072969 + 3 ^ 40 * 2070552 * 2
def baseEnd_2070552 : Nat := 1063188396128288189477711

theorem tailTrace_2070552 : CollatzResearch.WordTrace tailWord_2070552 prefixEnd_2070552 1063188396128288189477711 := by
  unfold tailWord_2070552
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759617797375600486706955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50346157063167467315609273 37759617797375600486706955)
  ·
    refine ⟨56639426696063400730060433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37759617797375600486706955 56639426696063400730060433)
    ·
      refine ⟨42479570022047550547545325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56639426696063400730060433 42479570022047550547545325)
      ·
        refine ⟨15929838758267831455329497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42479570022047550547545325 15929838758267831455329497)
        ·
          refine ⟨11947379068700873591497123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15929838758267831455329497 11947379068700873591497123)
          ·
            refine ⟨17921068603051310387245685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947379068700873591497123 17921068603051310387245685)
            ·
              refine ⟨1680100181536060348804283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17921068603051310387245685 1680100181536060348804283)
              ·
                refine ⟨2520150272304090523206425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680100181536060348804283 2520150272304090523206425)
                ·
                  refine ⟨1890112704228067892404819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2520150272304090523206425 1890112704228067892404819)
                  ·
                    refine ⟨2835169056342101838607229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1890112704228067892404819 2835169056342101838607229)
                    ·
                      refine ⟨1063188396128288189477711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2835169056342101838607229 1063188396128288189477711)
                      ·
                        rfl

theorem cell23_2070552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_2070552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070552 prefixEnd_2070552 := by exact prefixLift 2070552
  have htrace : WordTrace (prefixWord ++ tailWord_2070552) baseStart_2070552 baseEnd_2070552 := by
    simpa [prefixWord, tailWord_2070552, baseEnd_2070552] using wordTrace_append hprefix tailTrace_2070552
  have hstable : (prefixWord ++ tailWord_2070552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070552).length < 2 ^ (prefixWord ++ tailWord_2070552).sum := by decide
  have hdescent : baseEnd_2070552 < baseStart_2070552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070562 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_2070562 : Nat := 118140960795 + 2070562 * 2 ^ 59
def prefixEnd_2070562 : Nat := 4983230072969 + 3 ^ 40 * 2070562 * 2
def baseEnd_2070562 : Nat := 1063193530934833150352665

theorem tailTrace_2070562 : CollatzResearch.WordTrace tailWord_2070562 prefixEnd_2070562 1063193530934833150352665 := by
  unfold tailWord_2070562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18879900081178743170319485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50346400216476648454185293 18879900081178743170319485)
  ·
    refine ⟨7079962530442028688869807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18879900081178743170319485 7079962530442028688869807)
    ·
      refine ⟨10619943795663043033304711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079962530442028688869807 10619943795663043033304711)
      ·
        refine ⟨15929915693494564549957067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619943795663043033304711 15929915693494564549957067)
        ·
          refine ⟨23894873540241846824935601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15929915693494564549957067 23894873540241846824935601)
          ·
            refine ⟨17921155155181385118701701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23894873540241846824935601 17921155155181385118701701)
            ·
              refine ⟨3360216591596509709756569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17921155155181385118701701 3360216591596509709756569)
              ·
                refine ⟨2520162443697382282317427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360216591596509709756569 2520162443697382282317427)
                ·
                  refine ⟨3780243665546073423476141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2520162443697382282317427 3780243665546073423476141)
                  ·
                    refine ⟨1417591374579777533803553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3780243665546073423476141 1417591374579777533803553)
                    ·
                      refine ⟨1063193530934833150352665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1417591374579777533803553 1063193530934833150352665)
                      ·
                        rfl

theorem cell23_2070562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_2070562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2070562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2070562 prefixEnd_2070562 := by exact prefixLift 2070562
  have htrace : WordTrace (prefixWord ++ tailWord_2070562) baseStart_2070562 baseEnd_2070562 := by
    simpa [prefixWord, tailWord_2070562, baseEnd_2070562] using wordTrace_append hprefix tailTrace_2070562
  have hstable : (prefixWord ++ tailWord_2070562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070562).length < 2 ^ (prefixWord ++ tailWord_2070562).sum := by decide
  have hdescent : baseEnd_2070562 < baseStart_2070562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
