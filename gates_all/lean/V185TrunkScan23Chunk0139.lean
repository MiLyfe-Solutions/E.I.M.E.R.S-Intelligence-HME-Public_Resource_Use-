import V185TrunkScan23Chunk0138

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_822834 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_822834 : Nat := 118140960795 + 822834 * 2 ^ 59
def prefixEnd_822834 : Nat := 4983230072969 + 3 ^ 40 * 822834 * 2
def baseEnd_822834 : Nat := 422509340861738891890861

theorem tailTrace_822834 : CollatzResearch.WordTrace tailWord_822834 prefixEnd_822834 422509340861738891890861 := by
  unfold tailWord_822834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7502805375255105426058889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20007481000680281136157037 7502805375255105426058889)
  ·
    refine ⟨5627104031441329069544167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7502805375255105426058889 5627104031441329069544167)
    ·
      refine ⟨8440656047161993604316251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627104031441329069544167 8440656047161993604316251)
      ·
        refine ⟨12660984070742990406474377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8440656047161993604316251 12660984070742990406474377)
        ·
          refine ⟨9495738053057242804855783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12660984070742990406474377 9495738053057242804855783)
          ·
            refine ⟨14243607079585864207283675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495738053057242804855783 14243607079585864207283675)
            ·
              refine ⟨21365410619378796310925513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14243607079585864207283675 21365410619378796310925513)
              ·
                refine ⟨16024057964534097233194135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21365410619378796310925513 16024057964534097233194135)
                ·
                  refine ⟨24036086946801145849791203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16024057964534097233194135 24036086946801145849791203)
                  ·
                    refine ⟨36054130420201718774686805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24036086946801145849791203 36054130420201718774686805)
                    ·
                      refine ⟨422509340861738891890861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36054130420201718774686805 422509340861738891890861)
                      ·
                        rfl

theorem cell23_822834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_822834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822834 prefixEnd_822834 := by exact prefixLift 822834
  have htrace : WordTrace (prefixWord ++ tailWord_822834) baseStart_822834 baseEnd_822834 := by
    simpa [prefixWord, tailWord_822834, baseEnd_822834] using wordTrace_append hprefix tailTrace_822834
  have hstable : (prefixWord ++ tailWord_822834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822834).length < 2 ^ (prefixWord ++ tailWord_822834).sum := by decide
  have hdescent : baseEnd_822834 < baseStart_822834 := by decide
  rcases family_descends (prefixWord ++ tailWord_822834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822851 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 5, 5, 2]
def baseStart_822851 : Nat := 118140960795 + 822851 * 2 ^ 59
def prefixEnd_822851 : Nat := 4983230072969 + 3 ^ 40 * 822851 * 2
def baseEnd_822851 : Nat := 422518070032865325378283

theorem tailTrace_822851 : CollatzResearch.WordTrace tailWord_822851 prefixEnd_822851 422518070032865325378283 := by
  unfold tailWord_822851
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011841541958833607604407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20007894361305889071736271 30011841541958833607604407)
  ·
    refine ⟨45017762312938250411406611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30011841541958833607604407 45017762312938250411406611)
    ·
      refine ⟨67526643469407375617109917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45017762312938250411406611 67526643469407375617109917)
      ·
        refine ⟨25322491301027765856416219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67526643469407375617109917 25322491301027765856416219)
        ·
          refine ⟨37983736951541648784624329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25322491301027765856416219 37983736951541648784624329)
          ·
            refine ⟨28487802713656236588468247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37983736951541648784624329 28487802713656236588468247)
            ·
              refine ⟨42731704070484354882702371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28487802713656236588468247 42731704070484354882702371)
              ·
                refine ⟨64097556105726532324053557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42731704070484354882702371 64097556105726532324053557)
                ·
                  refine ⟨6009145884911862405380021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64097556105726532324053557 6009145884911862405380021)
                  ·
                    refine ⟨563357426710487100504377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6009145884911862405380021 563357426710487100504377)
                    ·
                      refine ⟨422518070032865325378283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563357426710487100504377 422518070032865325378283)
                      ·
                        rfl

theorem cell23_822851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_822851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822851 prefixEnd_822851 := by exact prefixLift 822851
  have htrace : WordTrace (prefixWord ++ tailWord_822851) baseStart_822851 baseEnd_822851 := by
    simpa [prefixWord, tailWord_822851, baseEnd_822851] using wordTrace_append hprefix tailTrace_822851
  have hstable : (prefixWord ++ tailWord_822851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822851).length < 2 ^ (prefixWord ++ tailWord_822851).sum := by decide
  have hdescent : baseEnd_822851 < baseStart_822851 := by decide
  rcases family_descends (prefixWord ++ tailWord_822851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822858 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_822858 : Nat := 118140960795 + 822858 * 2 ^ 59
def prefixEnd_822858 : Nat := 4983230072969 + 3 ^ 40 * 822858 * 2
def baseEnd_822858 : Nat := 422521664397446797990751

theorem tailTrace_822858 : CollatzResearch.WordTrace tailWord_822858 prefixEnd_822858 422521664397446797990751 := by
  unfold tailWord_822858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7503024213233368450777307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20008064568622315868739485 7503024213233368450777307)
  ·
    refine ⟨11254536319850052676165961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7503024213233368450777307 11254536319850052676165961)
    ·
      refine ⟨8440902239887539507124471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11254536319850052676165961 8440902239887539507124471)
      ·
        refine ⟨12661353359831309260686707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8440902239887539507124471 12661353359831309260686707)
        ·
          refine ⟨18992030039746963891030061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12661353359831309260686707 18992030039746963891030061)
          ·
            refine ⟨7122011264905111459136273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18992030039746963891030061 7122011264905111459136273)
            ·
              refine ⟨5341508448678833594352205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7122011264905111459136273 5341508448678833594352205)
              ·
                refine ⟨2003065668254562597882077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5341508448678833594352205 2003065668254562597882077)
                ·
                  refine ⟨751149625595460974205779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2003065668254562597882077 751149625595460974205779)
                  ·
                    refine ⟨1126724438393191461308669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 751149625595460974205779 1126724438393191461308669)
                    ·
                      refine ⟨422521664397446797990751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1126724438393191461308669 422521664397446797990751)
                      ·
                        rfl

theorem cell23_822858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_822858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822858 prefixEnd_822858 := by exact prefixLift 822858
  have htrace : WordTrace (prefixWord ++ tailWord_822858) baseStart_822858 baseEnd_822858 := by
    simpa [prefixWord, tailWord_822858, baseEnd_822858] using wordTrace_append hprefix tailTrace_822858
  have hstable : (prefixWord ++ tailWord_822858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822858).length < 2 ^ (prefixWord ++ tailWord_822858).sum := by decide
  have hdescent : baseEnd_822858 < baseStart_822858 := by decide
  rcases family_descends (prefixWord ++ tailWord_822858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822868 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_822868 : Nat := 118140960795 + 822868 * 2 ^ 59
def prefixEnd_822868 : Nat := 4983230072969 + 3 ^ 40 * 822868 * 2
def baseEnd_822868 : Nat := 422526799203991758865705

theorem tailTrace_822868 : CollatzResearch.WordTrace tailWord_822868 prefixEnd_822868 422526799203991758865705 := by
  unfold tailWord_822868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15006230791448622755486629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20008307721931497007315505 15006230791448622755486629)
  ·
    refine ⟨2813668273396616766653743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15006230791448622755486629 2813668273396616766653743)
    ·
      refine ⟨4220502410094925149980615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813668273396616766653743 4220502410094925149980615)
      ·
        refine ⟨6330753615142387724970923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4220502410094925149980615 6330753615142387724970923)
        ·
          refine ⟨9496130422713581587456385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6330753615142387724970923 9496130422713581587456385)
          ·
            refine ⟨7122097817035186190592289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9496130422713581587456385 7122097817035186190592289)
            ·
              refine ⟨5341573362776389642944217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7122097817035186190592289 5341573362776389642944217)
              ·
                refine ⟨4006180022082292232208163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5341573362776389642944217 4006180022082292232208163)
                ·
                  refine ⟨6009270033123438348312245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4006180022082292232208163 6009270033123438348312245)
                  ·
                    refine ⟨563369065605322345154273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6009270033123438348312245 563369065605322345154273)
                    ·
                      refine ⟨422526799203991758865705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563369065605322345154273 422526799203991758865705)
                      ·
                        rfl

theorem cell23_822868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_822868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822868 prefixEnd_822868 := by exact prefixLift 822868
  have htrace : WordTrace (prefixWord ++ tailWord_822868) baseStart_822868 baseEnd_822868 := by
    simpa [prefixWord, tailWord_822868, baseEnd_822868] using wordTrace_append hprefix tailTrace_822868
  have hstable : (prefixWord ++ tailWord_822868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822868).length < 2 ^ (prefixWord ++ tailWord_822868).sum := by decide
  have hdescent : baseEnd_822868 < baseStart_822868 := by decide
  rcases family_descends (prefixWord ++ tailWord_822868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822881 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_822881 : Nat := 118140960795 + 822881 * 2 ^ 59
def prefixEnd_822881 : Nat := 4983230072969 + 3 ^ 40 * 822881 * 2
def baseEnd_822881 : Nat := 422533474452500208003145

theorem tailTrace_822881 : CollatzResearch.WordTrace tailWord_822881 prefixEnd_822881 422533474452500208003145 := by
  unfold tailWord_822881
  simp only [CollatzResearch.WordTrace]
  refine ⟨30012935731850148731196497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20008623821233432487464331 30012935731850148731196497)
  ·
    refine ⟨22509701798887611548397373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30012935731850148731196497 22509701798887611548397373)
    ·
      refine ⟨8441138174582854330649015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22509701798887611548397373 8441138174582854330649015)
      ·
        refine ⟨12661707261874281495973523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8441138174582854330649015 12661707261874281495973523)
        ·
          refine ⟨18992560892811422243960285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12661707261874281495973523 18992560892811422243960285)
          ·
            refine ⟨7122210334804283341485107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18992560892811422243960285 7122210334804283341485107)
            ·
              refine ⟨10683315502206425012227661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7122210334804283341485107 10683315502206425012227661)
              ·
                refine ⟨4006243313327409379585373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10683315502206425012227661 4006243313327409379585373)
                ·
                  refine ⟨1502341242497778517344515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4006243313327409379585373 1502341242497778517344515)
                  ·
                    refine ⟨2253511863746667776016773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502341242497778517344515 2253511863746667776016773)
                    ·
                      refine ⟨422533474452500208003145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2253511863746667776016773 422533474452500208003145)
                      ·
                        rfl

theorem cell23_822881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_822881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822881 prefixEnd_822881 := by exact prefixLift 822881
  have htrace : WordTrace (prefixWord ++ tailWord_822881) baseStart_822881 baseEnd_822881 := by
    simpa [prefixWord, tailWord_822881, baseEnd_822881] using wordTrace_append hprefix tailTrace_822881
  have hstable : (prefixWord ++ tailWord_822881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822881).length < 2 ^ (prefixWord ++ tailWord_822881).sum := by decide
  have hdescent : baseEnd_822881 < baseStart_822881 := by decide
  rcases family_descends (prefixWord ++ tailWord_822881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822885 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 2, 3, 2]
def baseStart_822885 : Nat := 118140960795 + 822885 * 2 ^ 59
def prefixEnd_822885 : Nat := 4983230072969 + 3 ^ 40 * 822885 * 2
def baseEnd_822885 : Nat := 422535528375118192353127

theorem tailTrace_822885 : CollatzResearch.WordTrace tailWord_822885 prefixEnd_822885 422535528375118192353127 := by
  unfold tailWord_822885
  simp only [CollatzResearch.WordTrace]
  refine ⟨30013081623835657414342109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20008721082557104942894739 30013081623835657414342109)
  ·
    refine ⟨11254905608938371530378291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30013081623835657414342109 11254905608938371530378291)
    ·
      refine ⟨16882358413407557295567437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11254905608938371530378291 16882358413407557295567437)
      ·
        refine ⟨6330884405027833985837789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16882358413407557295567437 6330884405027833985837789)
        ·
          refine ⟨2374081651885437744689171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6330884405027833985837789 2374081651885437744689171)
          ·
            refine ⟨3561122477828156617033757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2374081651885437744689171 3561122477828156617033757)
            ·
              refine ⟨1335420929185558731387659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3561122477828156617033757 1335420929185558731387659)
              ·
                refine ⟨2003131393778338097081489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335420929185558731387659 2003131393778338097081489)
                ·
                  refine ⟨1502348545333753572811117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003131393778338097081489 1502348545333753572811117)
                  ·
                    refine ⟨563380704500157589804169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502348545333753572811117 563380704500157589804169)
                    ·
                      refine ⟨422535528375118192353127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563380704500157589804169 422535528375118192353127)
                      ·
                        rfl

theorem cell23_822885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_822885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822885 prefixEnd_822885 := by exact prefixLift 822885
  have htrace : WordTrace (prefixWord ++ tailWord_822885) baseStart_822885 baseEnd_822885 := by
    simpa [prefixWord, tailWord_822885, baseEnd_822885] using wordTrace_append hprefix tailTrace_822885
  have hstable : (prefixWord ++ tailWord_822885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822885).length < 2 ^ (prefixWord ++ tailWord_822885).sum := by decide
  have hdescent : baseEnd_822885 < baseStart_822885 := by decide
  rcases family_descends (prefixWord ++ tailWord_822885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822932 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_822932 : Nat := 118140960795 + 822932 * 2 ^ 59
def prefixEnd_822932 : Nat := 4983230072969 + 3 ^ 40 * 822932 * 2
def baseEnd_822932 : Nat := 422559661965879508465411

theorem tailTrace_822932 : CollatzResearch.WordTrace tailWord_822932 prefixEnd_822932 422559661965879508465411 := by
  unfold tailWord_822932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007397927332692220651525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20009863903110256294202033 15007397927332692220651525)
  ·
    refine ⟨2813887111374879791372161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15007397927332692220651525 2813887111374879791372161)
    ·
      refine ⟨2110415333531159843529121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2813887111374879791372161 2110415333531159843529121)
      ·
        refine ⟨1582811500148369882646841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2110415333531159843529121 1582811500148369882646841)
        ·
          refine ⟨1187108625111277411985131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1582811500148369882646841 1187108625111277411985131)
          ·
            refine ⟨1780662937666916117977697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187108625111277411985131 1780662937666916117977697)
            ·
              refine ⟨1335497203250187088483273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780662937666916117977697 1335497203250187088483273)
              ·
                refine ⟨1001622902437640316362455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335497203250187088483273 1001622902437640316362455)
                ·
                  refine ⟨1502434353656460474543683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001622902437640316362455 1502434353656460474543683)
                  ·
                    refine ⟨2253651530484690711815525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502434353656460474543683 2253651530484690711815525)
                    ·
                      refine ⟨422559661965879508465411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2253651530484690711815525 422559661965879508465411)
                      ·
                        rfl

theorem cell23_822932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_822932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822932 prefixEnd_822932 := by exact prefixLift 822932
  have htrace : WordTrace (prefixWord ++ tailWord_822932) baseStart_822932 baseEnd_822932 := by
    simpa [prefixWord, tailWord_822932, baseEnd_822932] using wordTrace_append hprefix tailTrace_822932
  have hstable : (prefixWord ++ tailWord_822932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822932).length < 2 ^ (prefixWord ++ tailWord_822932).sum := by decide
  have hdescent : baseEnd_822932 < baseStart_822932 := by decide
  rcases family_descends (prefixWord ++ tailWord_822932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822935 : List Nat := [1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_822935 : Nat := 118140960795 + 822935 * 2 ^ 59
def prefixEnd_822935 : Nat := 4983230072969 + 3 ^ 40 * 822935 * 2
def baseEnd_822935 : Nat := 422561202407842996727897

theorem tailTrace_822935 : CollatzResearch.WordTrace tailWord_822935 prefixEnd_822935 422561202407842996727897 := by
  unfold tailWord_822935
  simp only [CollatzResearch.WordTrace]
  refine ⟨30014905273654515953662259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20009936849103010635774839 30014905273654515953662259)
  ·
    refine ⟨45022357910481773930493389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30014905273654515953662259 45022357910481773930493389)
    ·
      refine ⟨16883384216430665223935021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45022357910481773930493389 16883384216430665223935021)
      ·
        refine ⟨6331269081161499458975633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16883384216430665223935021 6331269081161499458975633)
        ·
          refine ⟨4748451810871124594231725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6331269081161499458975633 4748451810871124594231725)
          ·
            refine ⟨1780669429076671722836897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4748451810871124594231725 1780669429076671722836897)
            ·
              refine ⟨1335502071807503792127673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780669429076671722836897 1335502071807503792127673)
              ·
                refine ⟨1001626553855627844095755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335502071807503792127673 1001626553855627844095755)
                ·
                  refine ⟨1502439830783441766143633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001626553855627844095755 1502439830783441766143633)
                  ·
                    refine ⟨1126829873087581324607725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1502439830783441766143633 1126829873087581324607725)
                    ·
                      refine ⟨422561202407842996727897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1126829873087581324607725 422561202407842996727897)
                      ·
                        rfl

theorem cell23_822935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_822935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822935 prefixEnd_822935 := by exact prefixLift 822935
  have htrace : WordTrace (prefixWord ++ tailWord_822935) baseStart_822935 baseEnd_822935 := by
    simpa [prefixWord, tailWord_822935, baseEnd_822935] using wordTrace_append hprefix tailTrace_822935
  have hstable : (prefixWord ++ tailWord_822935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822935).length < 2 ^ (prefixWord ++ tailWord_822935).sum := by decide
  have hdescent : baseEnd_822935 < baseStart_822935 := by decide
  rcases family_descends (prefixWord ++ tailWord_822935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822966 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_822966 : Nat := 118140960795 + 822966 * 2 ^ 59
def prefixEnd_822966 : Nat := 4983230072969 + 3 ^ 40 * 822966 * 2
def baseEnd_822966 : Nat := 422577120308132375440255

theorem tailTrace_822966 : CollatzResearch.WordTrace tailWord_822966 prefixEnd_822966 422577120308132375440255 := by
  unfold tailWord_822966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876002246033888015502547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20010690624361472165360501 1876002246033888015502547)
  ·
    refine ⟨2814003369050832023253821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876002246033888015502547 2814003369050832023253821)
    ·
      refine ⟨1055251263394062008720183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2814003369050832023253821 1055251263394062008720183)
      ·
        refine ⟨1582876895091093013080275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055251263394062008720183 1582876895091093013080275)
        ·
          refine ⟨2374315342636639519620413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582876895091093013080275 2374315342636639519620413)
          ·
            refine ⟨890368253488739819857655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2374315342636639519620413 890368253488739819857655)
            ·
              refine ⟨1335552380233109729786483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890368253488739819857655 1335552380233109729786483)
              ·
                refine ⟨2003328570349664594679725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335552380233109729786483 2003328570349664594679725)
                ·
                  refine ⟨751248213881124223004897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2003328570349664594679725 751248213881124223004897)
                  ·
                    refine ⟨563436160410843167253673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 751248213881124223004897 563436160410843167253673)
                    ·
                      refine ⟨422577120308132375440255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563436160410843167253673 422577120308132375440255)
                      ·
                        rfl

theorem cell23_822966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_822966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_822966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_822966 prefixEnd_822966 := by exact prefixLift 822966
  have htrace : WordTrace (prefixWord ++ tailWord_822966) baseStart_822966 baseEnd_822966 := by
    simpa [prefixWord, tailWord_822966, baseEnd_822966] using wordTrace_append hprefix tailTrace_822966
  have hstable : (prefixWord ++ tailWord_822966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822966).length < 2 ^ (prefixWord ++ tailWord_822966).sum := by decide
  have hdescent : baseEnd_822966 < baseStart_822966 := by decide
  rcases family_descends (prefixWord ++ tailWord_822966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823009 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_823009 : Nat := 118140960795 + 823009 * 2 ^ 59
def prefixEnd_823009 : Nat := 4983230072969 + 3 ^ 40 * 823009 * 2
def baseEnd_823009 : Nat := 422599199976275707202557

theorem tailTrace_823009 : CollatzResearch.WordTrace tailWord_823009 prefixEnd_823009 422599199976275707202557 := by
  unfold tailWord_823009
  simp only [CollatzResearch.WordTrace]
  refine ⟨30017604275386426591856081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20011736183590951061237387 30017604275386426591856081)
  ·
    refine ⟨22513203206539819943892061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30017604275386426591856081 22513203206539819943892061)
    ·
      refine ⟨8442451202452432478959523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22513203206539819943892061 8442451202452432478959523)
      ·
        refine ⟨12663676803678648718439285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442451202452432478959523 12663676803678648718439285)
        ·
          refine ⟨1187219700344873317353683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12663676803678648718439285 1187219700344873317353683)
          ·
            refine ⟨1780829550517309976030525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187219700344873317353683 1780829550517309976030525)
            ·
              refine ⟨667811081443991241011447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780829550517309976030525 667811081443991241011447)
              ·
                refine ⟨1001716622165986861517171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667811081443991241011447 1001716622165986861517171)
                ·
                  refine ⟨1502574933248980292275757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001716622165986861517171 1502574933248980292275757)
                  ·
                    refine ⟨563465599968367609603409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502574933248980292275757 563465599968367609603409)
                    ·
                      refine ⟨422599199976275707202557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563465599968367609603409 422599199976275707202557)
                      ·
                        rfl

theorem cell23_823009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_823009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823009 prefixEnd_823009 := by exact prefixLift 823009
  have htrace : WordTrace (prefixWord ++ tailWord_823009) baseStart_823009 baseEnd_823009 := by
    simpa [prefixWord, tailWord_823009, baseEnd_823009] using wordTrace_append hprefix tailTrace_823009
  have hstable : (prefixWord ++ tailWord_823009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823009).length < 2 ^ (prefixWord ++ tailWord_823009).sum := by decide
  have hdescent : baseEnd_823009 < baseStart_823009 := by decide
  rcases family_descends (prefixWord ++ tailWord_823009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823051 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_823051 : Nat := 118140960795 + 823051 * 2 ^ 59
def prefixEnd_823051 : Nat := 4983230072969 + 3 ^ 40 * 823051 * 2
def baseEnd_823051 : Nat := 422620766163764542877363

theorem tailTrace_823051 : CollatzResearch.WordTrace tailWord_823051 prefixEnd_823051 422620766163764542877363 := by
  unfold tailWord_823051
  simp only [CollatzResearch.WordTrace]
  refine ⟨30019136141234267764885007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20012757427489511843256671 30019136141234267764885007)
  ·
    refine ⟨45028704211851401647327511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30019136141234267764885007 45028704211851401647327511)
    ·
      refine ⟨67543056317777102470991267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45028704211851401647327511 67543056317777102470991267)
      ·
        refine ⟨101314584476665653706486901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67543056317777102470991267 101314584476665653706486901)
        ·
          refine ⟨9498242294687405034983147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101314584476665653706486901 9498242294687405034983147)
          ·
            refine ⟨14247363442031107552474721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9498242294687405034983147 14247363442031107552474721)
            ·
              refine ⟨10685522581523330664356041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14247363442031107552474721 10685522581523330664356041)
              ·
                refine ⟨8014141936142497998267031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10685522581523330664356041 8014141936142497998267031)
                ·
                  refine ⟨12021212904213746997400547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8014141936142497998267031 12021212904213746997400547)
                  ·
                    refine ⟨18031819356320620496100821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12021212904213746997400547 18031819356320620496100821)
                    ·
                      refine ⟨422620766163764542877363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18031819356320620496100821 422620766163764542877363)
                      ·
                        rfl

theorem cell23_823051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_823051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823051 prefixEnd_823051 := by exact prefixLift 823051
  have htrace : WordTrace (prefixWord ++ tailWord_823051) baseStart_823051 baseEnd_823051 := by
    simpa [prefixWord, tailWord_823051, baseEnd_823051] using wordTrace_append hprefix tailTrace_823051
  have hstable : (prefixWord ++ tailWord_823051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823051).length < 2 ^ (prefixWord ++ tailWord_823051).sum := by decide
  have hdescent : baseEnd_823051 < baseStart_823051 := by decide
  rcases family_descends (prefixWord ++ tailWord_823051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823060 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_823060 : Nat := 118140960795 + 823060 * 2 ^ 59
def prefixEnd_823060 : Nat := 4983230072969 + 3 ^ 40 * 823060 * 2
def baseEnd_823060 : Nat := 422625387489655007664823

theorem tailTrace_823060 : CollatzResearch.WordTrace tailWord_823060 prefixEnd_823060 422625387489655007664823 := by
  unfold tailWord_823060
  simp only [CollatzResearch.WordTrace]
  refine ⟨15009732199100831150981317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20012976265467774867975089 15009732199100831150981317)
  ·
    refine ⟨2814324787331405840808997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15009732199100831150981317 2814324787331405840808997)
    ·
      refine ⟨527685897624638595151687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2814324787331405840808997 527685897624638595151687)
      ·
        refine ⟨791528846436957892727531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527685897624638595151687 791528846436957892727531)
        ·
          refine ⟨1187293269655436839091297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791528846436957892727531 1187293269655436839091297)
          ·
            refine ⟨890469952241577629318473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187293269655436839091297 890469952241577629318473)
            ·
              refine ⟨667852464181183221988855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890469952241577629318473 667852464181183221988855)
              ·
                refine ⟨1001778696271774832983283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667852464181183221988855 1001778696271774832983283)
                ·
                  refine ⟨1502668044407662249474925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001778696271774832983283 1502668044407662249474925)
                  ·
                    refine ⟨563500516652873343553097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502668044407662249474925 563500516652873343553097)
                    ·
                      refine ⟨422625387489655007664823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563500516652873343553097 422625387489655007664823)
                      ·
                        rfl

theorem cell23_823060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_823060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823060 prefixEnd_823060 := by exact prefixLift 823060
  have htrace : WordTrace (prefixWord ++ tailWord_823060) baseStart_823060 baseEnd_823060 := by
    simpa [prefixWord, tailWord_823060, baseEnd_823060] using wordTrace_append hprefix tailTrace_823060
  have hstable : (prefixWord ++ tailWord_823060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823060).length < 2 ^ (prefixWord ++ tailWord_823060).sum := by decide
  have hdescent : baseEnd_823060 < baseStart_823060 := by decide
  rcases family_descends (prefixWord ++ tailWord_823060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823139 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 3, 4]
def baseStart_823139 : Nat := 118140960795 + 823139 * 2 ^ 59
def prefixEnd_823139 : Nat := 4983230072969 + 3 ^ 40 * 823139 * 2
def baseEnd_823139 : Nat := 140888650820453399525653

theorem tailTrace_823139 : CollatzResearch.WordTrace tailWord_823139 prefixEnd_823139 140888650820453399525653 := by
  unfold tailWord_823139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022345764915458794088471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20014897176610305862725647 30022345764915458794088471)
  ·
    refine ⟨45033518647373188191132707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30022345764915458794088471 45033518647373188191132707)
    ·
      refine ⟨67550277971059782286699061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45033518647373188191132707 67550277971059782286699061)
      ·
        refine ⟨6332838559786854589378037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67550277971059782286699061 6332838559786854589378037)
        ·
          refine ⟨593703614980017617754191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6332838559786854589378037 593703614980017617754191)
          ·
            refine ⟨890555422470026426631287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593703614980017617754191 890555422470026426631287)
            ·
              refine ⟨1335833133705039639946931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890555422470026426631287 1335833133705039639946931)
              ·
                refine ⟨2003749700557559459920397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335833133705039639946931 2003749700557559459920397)
                ·
                  refine ⟨751406137709084797470149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2003749700557559459920397 751406137709084797470149)
                  ·
                    refine ⟨140888650820453399525653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751406137709084797470149 140888650820453399525653)
                    ·
                      rfl

theorem cell23_823139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 3, 4].length) (baseStart_823139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823139 prefixEnd_823139 := by exact prefixLift 823139
  have htrace : WordTrace (prefixWord ++ tailWord_823139) baseStart_823139 baseEnd_823139 := by
    simpa [prefixWord, tailWord_823139, baseEnd_823139] using wordTrace_append hprefix tailTrace_823139
  have hstable : (prefixWord ++ tailWord_823139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823139).length < 2 ^ (prefixWord ++ tailWord_823139).sum := by decide
  have hdescent : baseEnd_823139 < baseStart_823139 := by decide
  rcases family_descends (prefixWord ++ tailWord_823139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823155 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 6, 3, 2]
def baseStart_823155 : Nat := 118140960795 + 823155 * 2 ^ 59
def prefixEnd_823155 : Nat := 4983230072969 + 3 ^ 40 * 823155 * 2
def baseEnd_823155 : Nat := 422674168151832135976885

theorem tailTrace_823155 : CollatzResearch.WordTrace tailWord_823155 prefixEnd_823155 422674168151832135976885 := by
  unfold tailWord_823155
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022929332857493526670919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20015286221904995684447279 30022929332857493526670919)
  ·
    refine ⟨45034393999286240290006379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30022929332857493526670919 45034393999286240290006379)
    ·
      refine ⟨67551590998929360435009569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45034393999286240290006379 67551590998929360435009569)
      ·
        refine ⟨50663693249197020326257177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67551590998929360435009569 50663693249197020326257177)
        ·
          refine ⟨37997769936897765244692883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50663693249197020326257177 37997769936897765244692883)
          ·
            refine ⟨56996654905346647867039325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37997769936897765244692883 56996654905346647867039325)
            ·
              refine ⟨21373745589504992950139747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56996654905346647867039325 21373745589504992950139747)
              ·
                refine ⟨32060618384257489425209621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21373745589504992950139747 32060618384257489425209621)
                ·
                  refine ⟨1502841486762069816806701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32060618384257489425209621 1502841486762069816806701)
                  ·
                    refine ⟨563565557535776181302513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502841486762069816806701 563565557535776181302513)
                    ·
                      refine ⟨422674168151832135976885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563565557535776181302513 422674168151832135976885)
                      ·
                        rfl

theorem cell23_823155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3, 2].length) (baseStart_823155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823155 prefixEnd_823155 := by exact prefixLift 823155
  have htrace : WordTrace (prefixWord ++ tailWord_823155) baseStart_823155 baseEnd_823155 := by
    simpa [prefixWord, tailWord_823155, baseEnd_823155] using wordTrace_append hprefix tailTrace_823155
  have hstable : (prefixWord ++ tailWord_823155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823155).length < 2 ^ (prefixWord ++ tailWord_823155).sum := by decide
  have hdescent : baseEnd_823155 < baseStart_823155 := by decide
  rcases family_descends (prefixWord ++ tailWord_823155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823172 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_823172 : Nat := 118140960795 + 823172 * 2 ^ 59
def prefixEnd_823172 : Nat := 4983230072969 + 3 ^ 40 * 823172 * 2
def baseEnd_823172 : Nat := 422682897322958569464307

theorem tailTrace_823172 : CollatzResearch.WordTrace tailWord_823172 prefixEnd_823172 422682897322958569464307 := by
  unfold tailWord_823172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15011774686897952715019885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20015699582530603620026513 15011774686897952715019885)
  ·
    refine ⟨5629415507586732268132457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15011774686897952715019885 5629415507586732268132457)
    ·
      refine ⟨4222061630690049201099343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5629415507586732268132457 4222061630690049201099343)
      ·
        refine ⟨6333092446035073801649015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4222061630690049201099343 6333092446035073801649015)
        ·
          refine ⟨9499638669052610702473523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6333092446035073801649015 9499638669052610702473523)
          ·
            refine ⟨14249458003578916053710285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9499638669052610702473523 14249458003578916053710285)
            ·
              refine ⟨5343546751342093520141357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14249458003578916053710285 5343546751342093520141357)
              ·
                refine ⟨2003830031753285070053009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5343546751342093520141357 2003830031753285070053009)
                ·
                  refine ⟨1502872523814963802539757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2003830031753285070053009 1502872523814963802539757)
                  ·
                    refine ⟨563577196430611425952409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1502872523814963802539757 563577196430611425952409)
                    ·
                      refine ⟨422682897322958569464307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563577196430611425952409 422682897322958569464307)
                      ·
                        rfl

theorem cell23_823172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_823172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823172 prefixEnd_823172 := by exact prefixLift 823172
  have htrace : WordTrace (prefixWord ++ tailWord_823172) baseStart_823172 baseEnd_823172 := by
    simpa [prefixWord, tailWord_823172, baseEnd_823172] using wordTrace_append hprefix tailTrace_823172
  have hstable : (prefixWord ++ tailWord_823172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823172).length < 2 ^ (prefixWord ++ tailWord_823172).sum := by decide
  have hdescent : baseEnd_823172 < baseStart_823172 := by decide
  rcases family_descends (prefixWord ++ tailWord_823172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823185 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_823185 : Nat := 118140960795 + 823185 * 2 ^ 59
def prefixEnd_823185 : Nat := 4983230072969 + 3 ^ 40 * 823185 * 2
def baseEnd_823185 : Nat := 422689572571467018601747

theorem tailTrace_823185 : CollatzResearch.WordTrace tailWord_823185 prefixEnd_823185 422689572571467018601747 := by
  unfold tailWord_823185
  simp only [CollatzResearch.WordTrace]
  refine ⟨30024023522748808650263009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20016015681832539100175339 30024023522748808650263009)
  ·
    refine ⟨22518017642061606487697257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30024023522748808650263009 22518017642061606487697257)
    ·
      refine ⟨16888513231546204865772943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22518017642061606487697257 16888513231546204865772943)
      ·
        refine ⟨25332769847319307298659415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16888513231546204865772943 25332769847319307298659415)
        ·
          refine ⟨37999154770978960947989123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25332769847319307298659415 37999154770978960947989123)
          ·
            refine ⟨56998732156468441421983685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37999154770978960947989123 56998732156468441421983685)
            ·
              refine ⟨10687262279337832766621941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56998732156468441421983685 10687262279337832766621941)
              ·
                refine ⟨1001930838687921821870807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10687262279337832766621941 1001930838687921821870807)
                ·
                  refine ⟨1502896258031882732806211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1001930838687921821870807 1502896258031882732806211)
                  ·
                    refine ⟨2254344387047824099209317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1502896258031882732806211 2254344387047824099209317)
                    ·
                      refine ⟨422689572571467018601747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2254344387047824099209317 422689572571467018601747)
                      ·
                        rfl

theorem cell23_823185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_823185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823185 prefixEnd_823185 := by exact prefixLift 823185
  have htrace : WordTrace (prefixWord ++ tailWord_823185) baseStart_823185 baseEnd_823185 := by
    simpa [prefixWord, tailWord_823185, baseEnd_823185] using wordTrace_append hprefix tailTrace_823185
  have hstable : (prefixWord ++ tailWord_823185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823185).length < 2 ^ (prefixWord ++ tailWord_823185).sum := by decide
  have hdescent : baseEnd_823185 < baseStart_823185 := by decide
  rcases family_descends (prefixWord ++ tailWord_823185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823196 : List Nat := [2, 2, 3, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_823196 : Nat := 118140960795 + 823196 * 2 ^ 59
def prefixEnd_823196 : Nat := 4983230072969 + 3 ^ 40 * 823196 * 2
def baseEnd_823196 : Nat := 422695220858666475564197

theorem tailTrace_823196 : CollatzResearch.WordTrace tailWord_823196 prefixEnd_823196 422695220858666475564197 := by
  unfold tailWord_823196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15012212362854478764456721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20016283150472638352608961 15012212362854478764456721)
  ·
    refine ⟨11259159272140859073342541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15012212362854478764456721 11259159272140859073342541)
    ·
      refine ⟨4222184727052822152503453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11259159272140859073342541 4222184727052822152503453)
      ·
        refine ⟨1583319272644808307188795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4222184727052822152503453 1583319272644808307188795)
        ·
          refine ⟨2374978908967212460783193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583319272644808307188795 2374978908967212460783193)
          ·
            refine ⟨1781234181725409345587395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374978908967212460783193 1781234181725409345587395)
            ·
              refine ⟨2671851272588114018381093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781234181725409345587395 2671851272588114018381093)
              ·
                refine ⟨500972113610271378446455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2671851272588114018381093 500972113610271378446455)
                ·
                  refine ⟨751458170415407067669683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500972113610271378446455 751458170415407067669683)
                  ·
                    refine ⟨1127187255623110601504525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 751458170415407067669683 1127187255623110601504525)
                    ·
                      refine ⟨422695220858666475564197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1127187255623110601504525 422695220858666475564197)
                      ·
                        rfl

theorem cell23_823196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_823196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823196 prefixEnd_823196 := by exact prefixLift 823196
  have htrace : WordTrace (prefixWord ++ tailWord_823196) baseStart_823196 baseEnd_823196 := by
    simpa [prefixWord, tailWord_823196, baseEnd_823196] using wordTrace_append hprefix tailTrace_823196
  have hstable : (prefixWord ++ tailWord_823196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823196).length < 2 ^ (prefixWord ++ tailWord_823196).sum := by decide
  have hdescent : baseEnd_823196 < baseStart_823196 := by decide
  rcases family_descends (prefixWord ++ tailWord_823196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823215 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_823215 : Nat := 118140960795 + 823215 * 2 ^ 59
def prefixEnd_823215 : Nat := 4983230072969 + 3 ^ 40 * 823215 * 2
def baseEnd_823215 : Nat := 422704976991101901226609

theorem tailTrace_823215 : CollatzResearch.WordTrace tailWord_823215 prefixEnd_823215 422704976991101901226609 := by
  unfold tailWord_823215
  simp only [CollatzResearch.WordTrace]
  refine ⟨30025117712640123773855099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20016745141760082515903399 30025117712640123773855099)
  ·
    refine ⟨45037676568960185660782649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30025117712640123773855099 45037676568960185660782649)
    ·
      refine ⟨33778257426720139245586987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45037676568960185660782649 33778257426720139245586987)
      ·
        refine ⟨50667386140080208868380481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33778257426720139245586987 50667386140080208868380481)
        ·
          refine ⟨38000539605060156651285361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50667386140080208868380481 38000539605060156651285361)
          ·
            refine ⟨28500404703795117488464021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38000539605060156651285361 28500404703795117488464021)
            ·
              refine ⟨1335956470490396132271751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28500404703795117488464021 1335956470490396132271751)
              ·
                refine ⟨2003934705735594198407627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335956470490396132271751 2003934705735594198407627)
                ·
                  refine ⟨3005902058603391297611441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2003934705735594198407627 3005902058603391297611441)
                  ·
                    refine ⟨2254426543952543473208581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3005902058603391297611441 2254426543952543473208581)
                    ·
                      refine ⟨422704976991101901226609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2254426543952543473208581 422704976991101901226609)
                      ·
                        rfl

theorem cell23_823215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_823215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823215 prefixEnd_823215 := by exact prefixLift 823215
  have htrace : WordTrace (prefixWord ++ tailWord_823215) baseStart_823215 baseEnd_823215 := by
    simpa [prefixWord, tailWord_823215, baseEnd_823215] using wordTrace_append hprefix tailTrace_823215
  have hstable : (prefixWord ++ tailWord_823215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823215).length < 2 ^ (prefixWord ++ tailWord_823215).sum := by decide
  have hdescent : baseEnd_823215 < baseStart_823215 := by decide
  rcases family_descends (prefixWord ++ tailWord_823215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823218 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_823218 : Nat := 118140960795 + 823218 * 2 ^ 59
def prefixEnd_823218 : Nat := 4983230072969 + 3 ^ 40 * 823218 * 2
def baseEnd_823218 : Nat := 422706517433065389489095

theorem tailTrace_823218 : CollatzResearch.WordTrace tailWord_823218 prefixEnd_823218 422706517433065389489095 := by
  unfold tailWord_823218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506306782907313821553577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20016818087752836857476205 7506306782907313821553577)
  ·
    refine ⟨5629730087180485366165183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7506306782907313821553577 5629730087180485366165183)
    ·
      refine ⟨8444595130770728049247775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5629730087180485366165183 8444595130770728049247775)
      ·
        refine ⟨12666892696156092073871663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8444595130770728049247775 12666892696156092073871663)
        ·
          refine ⟨19000339044234138110807495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12666892696156092073871663 19000339044234138110807495)
          ·
            refine ⟨28500508566351207166211243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19000339044234138110807495 28500508566351207166211243)
            ·
              refine ⟨42750762849526810749316865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28500508566351207166211243 42750762849526810749316865)
              ·
                refine ⟨32063072137145108061987649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42750762849526810749316865 32063072137145108061987649)
                ·
                  refine ⟨24047304102858831046490737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32063072137145108061987649 24047304102858831046490737)
                  ·
                    refine ⟨18035478077144123284868053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24047304102858831046490737 18035478077144123284868053)
                    ·
                      refine ⟨422706517433065389489095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18035478077144123284868053 422706517433065389489095)
                      ·
                        rfl

theorem cell23_823218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_823218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823218 prefixEnd_823218 := by exact prefixLift 823218
  have htrace : WordTrace (prefixWord ++ tailWord_823218) baseStart_823218 baseEnd_823218 := by
    simpa [prefixWord, tailWord_823218, baseEnd_823218] using wordTrace_append hprefix tailTrace_823218
  have hstable : (prefixWord ++ tailWord_823218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823218).length < 2 ^ (prefixWord ++ tailWord_823218).sum := by decide
  have hdescent : baseEnd_823218 < baseStart_823218 := by decide
  rcases family_descends (prefixWord ++ tailWord_823218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823225 : List Nat := [1, 2, 1, 4, 2, 1, 5, 7]
def baseStart_823225 : Nat := 118140960795 + 823225 * 2 ^ 59
def prefixEnd_823225 : Nat := 4983230072969 + 3 ^ 40 * 823225 * 2
def baseEnd_823225 : Nat := 15655930066579513411169

theorem tailTrace_823225 : CollatzResearch.WordTrace tailWord_823225 prefixEnd_823225 15655930066579513411169 := by
  unfold tailWord_823225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30025482442603895481719129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20016988295069263654479419 30025482442603895481719129)
  ·
    refine ⟨22519111831952921611289347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30025482442603895481719129 22519111831952921611289347)
    ·
      refine ⟨33778667747929382416934021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22519111831952921611289347 33778667747929382416934021)
      ·
        refine ⟨6333500202736759203175129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33778667747929382416934021 6333500202736759203175129)
        ·
          refine ⟨4750125152052569402381347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6333500202736759203175129 4750125152052569402381347)
          ·
            refine ⟨7125187728078854103572021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4750125152052569402381347 7125187728078854103572021)
            ·
              refine ⟨667986349507392572209877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7125187728078854103572021 667986349507392572209877)
              ·
                refine ⟨15655930066579513411169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 667986349507392572209877 15655930066579513411169)
                ·
                  rfl

theorem cell23_823225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 7].length) (baseStart_823225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823225 prefixEnd_823225 := by exact prefixLift 823225
  have htrace : WordTrace (prefixWord ++ tailWord_823225) baseStart_823225 baseEnd_823225 := by
    simpa [prefixWord, tailWord_823225, baseEnd_823225] using wordTrace_append hprefix tailTrace_823225
  have hstable : (prefixWord ++ tailWord_823225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823225).length < 2 ^ (prefixWord ++ tailWord_823225).sum := by decide
  have hdescent : baseEnd_823225 < baseStart_823225 := by decide
  rcases family_descends (prefixWord ++ tailWord_823225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823266 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_823266 : Nat := 118140960795 + 823266 * 2 ^ 59
def prefixEnd_823266 : Nat := 4983230072969 + 3 ^ 40 * 823266 * 2
def baseEnd_823266 : Nat := 422731164504481201688875

theorem tailTrace_823266 : CollatzResearch.WordTrace tailWord_823266 prefixEnd_823266 422731164504481201688875 := by
  unfold tailWord_823266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506744458863839870990413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20017985223636906322641101 7506744458863839870990413)
  ·
    refine ⟨2815029172073939951621405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7506744458863839870990413 2815029172073939951621405)
    ·
      refine ⟨1055635939527727481858027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2815029172073939951621405 1055635939527727481858027)
      ·
        refine ⟨1583453909291591222787041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055635939527727481858027 1583453909291591222787041)
        ·
          refine ⟨1187590431968693417090281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583453909291591222787041 1187590431968693417090281)
          ·
            refine ⟨890692823976520062817711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187590431968693417090281 890692823976520062817711)
            ·
              refine ⟨1336039235964780094226567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890692823976520062817711 1336039235964780094226567)
              ·
                refine ⟨2004058853947170141339851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336039235964780094226567 2004058853947170141339851)
                ·
                  refine ⟨3006088280920755212009777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2004058853947170141339851 3006088280920755212009777)
                  ·
                    refine ⟨2254566210690566409007333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3006088280920755212009777 2254566210690566409007333)
                    ·
                      refine ⟨422731164504481201688875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2254566210690566409007333 422731164504481201688875)
                      ·
                        rfl

theorem cell23_823266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_823266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823266 prefixEnd_823266 := by exact prefixLift 823266
  have htrace : WordTrace (prefixWord ++ tailWord_823266) baseStart_823266 baseEnd_823266 := by
    simpa [prefixWord, tailWord_823266, baseEnd_823266] using wordTrace_append hprefix tailTrace_823266
  have hstable : (prefixWord ++ tailWord_823266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823266).length < 2 ^ (prefixWord ++ tailWord_823266).sum := by decide
  have hdescent : baseEnd_823266 < baseStart_823266 := by decide
  rcases family_descends (prefixWord ++ tailWord_823266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823279 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 1, 3, 2]
def baseStart_823279 : Nat := 118140960795 + 823279 * 2 ^ 59
def prefixEnd_823279 : Nat := 4983230072969 + 3 ^ 40 * 823279 * 2
def baseEnd_823279 : Nat := 422737839752989650826315

theorem tailTrace_823279 : CollatzResearch.WordTrace tailWord_823279 prefixEnd_823279 422737839752989650826315 := by
  unfold tailWord_823279
  simp only [CollatzResearch.WordTrace]
  refine ⟨30027451984408262704184891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20018301322938841802789927 30027451984408262704184891)
  ·
    refine ⟨45041177976612394056277337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30027451984408262704184891 45041177976612394056277337)
    ·
      refine ⟨33780883482459295542208003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45041177976612394056277337 33780883482459295542208003)
      ·
        refine ⟨50671325223688943313312005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33780883482459295542208003 50671325223688943313312005)
        ·
          refine ⟨9500873479441676871246001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50671325223688943313312005 9500873479441676871246001)
          ·
            refine ⟨7125655109581257653434501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9500873479441676871246001 7125655109581257653434501)
            ·
              refine ⟨1336060333046485810018969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7125655109581257653434501 1336060333046485810018969)
              ·
                refine ⟨1002045249784864357514227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336060333046485810018969 1002045249784864357514227)
                ·
                  refine ⟨1503067874677296536271341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002045249784864357514227 1503067874677296536271341)
                  ·
                    refine ⟨563650453003986201101753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503067874677296536271341 563650453003986201101753)
                    ·
                      refine ⟨422737839752989650826315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563650453003986201101753 422737839752989650826315)
                      ·
                        rfl

theorem cell23_823279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 3, 2].length) (baseStart_823279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823279 prefixEnd_823279 := by exact prefixLift 823279
  have htrace : WordTrace (prefixWord ++ tailWord_823279) baseStart_823279 baseEnd_823279 := by
    simpa [prefixWord, tailWord_823279, baseEnd_823279] using wordTrace_append hprefix tailTrace_823279
  have hstable : (prefixWord ++ tailWord_823279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823279).length < 2 ^ (prefixWord ++ tailWord_823279).sum := by decide
  have hdescent : baseEnd_823279 < baseStart_823279 := by decide
  rcases family_descends (prefixWord ++ tailWord_823279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823292 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_823292 : Nat := 118140960795 + 823292 * 2 ^ 59
def prefixEnd_823292 : Nat := 4983230072969 + 3 ^ 40 * 823292 * 2
def baseEnd_823292 : Nat := 422744515001498099963755

theorem tailTrace_823292 : CollatzResearch.WordTrace tailWord_823292 prefixEnd_823292 422744515001498099963755 := by
  unfold tailWord_823292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15013963066680582962204065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20018617422240777282938753 15013963066680582962204065)
  ·
    refine ⟨11260472300010437221653049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15013963066680582962204065 11260472300010437221653049)
    ·
      refine ⟨8445354225007827916239787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11260472300010437221653049 8445354225007827916239787)
      ·
        refine ⟨12668031337511741874359681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8445354225007827916239787 12668031337511741874359681)
        ·
          refine ⟨9501023503133806405769761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12668031337511741874359681 9501023503133806405769761)
          ·
            refine ⟨7125767627350354804327321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9501023503133806405769761 7125767627350354804327321)
            ·
              refine ⟨5344325720512766103245491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7125767627350354804327321 5344325720512766103245491)
              ·
                refine ⟨8016488580769149154868237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344325720512766103245491 8016488580769149154868237)
                ·
                  refine ⟨3006183217788430933075589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8016488580769149154868237 3006183217788430933075589)
                  ·
                    refine ⟨563659353335330799951673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3006183217788430933075589 563659353335330799951673)
                    ·
                      refine ⟨422744515001498099963755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563659353335330799951673 422744515001498099963755)
                      ·
                        rfl

theorem cell23_823292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_823292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823292 prefixEnd_823292 := by exact prefixLift 823292
  have htrace : WordTrace (prefixWord ++ tailWord_823292) baseStart_823292 baseEnd_823292 := by
    simpa [prefixWord, tailWord_823292, baseEnd_823292] using wordTrace_append hprefix tailTrace_823292
  have hstable : (prefixWord ++ tailWord_823292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823292).length < 2 ^ (prefixWord ++ tailWord_823292).sum := by decide
  have hdescent : baseEnd_823292 < baseStart_823292 := by decide
  rcases family_descends (prefixWord ++ tailWord_823292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823315 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 7]
def baseStart_823315 : Nat := 118140960795 + 823315 * 2 ^ 59
def prefixEnd_823315 : Nat := 4983230072969 + 3 ^ 40 * 823315 * 2
def baseEnd_823315 : Nat := 46972925006283501108461

theorem tailTrace_823315 : CollatzResearch.WordTrace tailWord_823315 prefixEnd_823315 46972925006283501108461 := by
  unfold tailWord_823315
  simp only [CollatzResearch.WordTrace]
  refine ⟨30028765012277840852495399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20019176674851893901663599 30028765012277840852495399)
  ·
    refine ⟨45043147518416761278743099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30028765012277840852495399 45043147518416761278743099)
    ·
      refine ⟨67564721277625141918114649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45043147518416761278743099 67564721277625141918114649)
      ·
        refine ⟨50673540958218856438585987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67564721277625141918114649 50673540958218856438585987)
        ·
          refine ⟨76010311437328284657878981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50673540958218856438585987 76010311437328284657878981)
          ·
            refine ⟨14251933394499053373352309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76010311437328284657878981 14251933394499053373352309)
            ·
              refine ⟨1336118755734286253751779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14251933394499053373352309 1336118755734286253751779)
              ·
                refine ⟨2004178133601429380627669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336118755734286253751779 2004178133601429380627669)
                ·
                  refine ⟨46972925006283501108461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2004178133601429380627669 46972925006283501108461)
                  ·
                    rfl

theorem cell23_823315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 7].length) (baseStart_823315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823315 prefixEnd_823315 := by exact prefixLift 823315
  have htrace : WordTrace (prefixWord ++ tailWord_823315) baseStart_823315 baseEnd_823315 := by
    simpa [prefixWord, tailWord_823315, baseEnd_823315] using wordTrace_append hprefix tailTrace_823315
  have hstable : (prefixWord ++ tailWord_823315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823315).length < 2 ^ (prefixWord ++ tailWord_823315).sum := by decide
  have hdescent : baseEnd_823315 < baseStart_823315 := by decide
  rcases family_descends (prefixWord ++ tailWord_823315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823365 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_823365 : Nat := 118140960795 + 823365 * 2 ^ 59
def prefixEnd_823365 : Nat := 4983230072969 + 3 ^ 40 * 823365 * 2
def baseEnd_823365 : Nat := 422781999089276314350919

theorem tailTrace_823365 : CollatzResearch.WordTrace tailWord_823365 prefixEnd_823365 422781999089276314350919 := by
  unfold tailWord_823365
  simp only [CollatzResearch.WordTrace]
  refine ⟨30030588662096699391815549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20020392441397799594543699 30030588662096699391815549)
  ·
    refine ⟨11261470748286262271930831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30030588662096699391815549 11261470748286262271930831)
    ·
      refine ⟨16892206122429393407896247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11261470748286262271930831 16892206122429393407896247)
      ·
        refine ⟨25338309183644090111844371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16892206122429393407896247 25338309183644090111844371)
        ·
          refine ⟨38007463775466135167766557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25338309183644090111844371 38007463775466135167766557)
          ·
            refine ⟨14252798915799800687912459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38007463775466135167766557 14252798915799800687912459)
            ·
              refine ⟨21379198373699701031868689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14252798915799800687912459 21379198373699701031868689)
              ·
                refine ⟨16034398780274775773901517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21379198373699701031868689 16034398780274775773901517)
                ·
                  refine ⟨6012899542603040915213069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16034398780274775773901517 6012899542603040915213069)
                  ·
                    refine ⟨2254837328476140343204901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6012899542603040915213069 2254837328476140343204901)
                    ·
                      refine ⟨422781999089276314350919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2254837328476140343204901 422781999089276314350919)
                      ·
                        rfl

theorem cell23_823365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_823365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823365 prefixEnd_823365 := by exact prefixLift 823365
  have htrace : WordTrace (prefixWord ++ tailWord_823365) baseStart_823365 baseEnd_823365 := by
    simpa [prefixWord, tailWord_823365, baseEnd_823365] using wordTrace_append hprefix tailTrace_823365
  have hstable : (prefixWord ++ tailWord_823365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823365).length < 2 ^ (prefixWord ++ tailWord_823365).sum := by decide
  have hdescent : baseEnd_823365 < baseStart_823365 := by decide
  rcases family_descends (prefixWord ++ tailWord_823365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823366 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_823366 : Nat := 118140960795 + 823366 * 2 ^ 59
def prefixEnd_823366 : Nat := 4983230072969 + 3 ^ 40 * 823366 * 2
def baseEnd_823366 : Nat := 46975834729992312270935

theorem tailTrace_823366 : CollatzResearch.WordTrace tailWord_823366 prefixEnd_823366 46975834729992312270935 := by
  unfold tailWord_823366
  simp only [CollatzResearch.WordTrace]
  refine ⟨938457035471658642581311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20020416756728717708401301 938457035471658642581311)
  ·
    refine ⟨1407685553207487963871967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 938457035471658642581311 1407685553207487963871967)
    ·
      refine ⟨2111528329811231945807951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407685553207487963871967 2111528329811231945807951)
      ·
        refine ⟨3167292494716847918711927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111528329811231945807951 3167292494716847918711927)
        ·
          refine ⟨4750938742075271878067891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167292494716847918711927 4750938742075271878067891)
          ·
            refine ⟨7126408113112907817101837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4750938742075271878067891 7126408113112907817101837)
            ·
              refine ⟨2672403042417340431413189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7126408113112907817101837 2672403042417340431413189)
              ·
                refine ⟨501075570453251330889973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2672403042417340431413189 501075570453251330889973)
                ·
                  refine ⟨46975834729992312270935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501075570453251330889973 46975834729992312270935)
                  ·
                    rfl

theorem cell23_823366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_823366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823366 prefixEnd_823366 := by exact prefixLift 823366
  have htrace : WordTrace (prefixWord ++ tailWord_823366) baseStart_823366 baseEnd_823366 := by
    simpa [prefixWord, tailWord_823366, baseEnd_823366] using wordTrace_append hprefix tailTrace_823366
  have hstable : (prefixWord ++ tailWord_823366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823366).length < 2 ^ (prefixWord ++ tailWord_823366).sum := by decide
  have hdescent : baseEnd_823366 < baseStart_823366 := by decide
  rcases family_descends (prefixWord ++ tailWord_823366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823392 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 5, 4]
def baseStart_823392 : Nat := 118140960795 + 823392 * 2 ^ 59
def prefixEnd_823392 : Nat := 4983230072969 + 3 ^ 40 * 823392 * 2
def baseEnd_823392 : Nat := 140931954355649236237765

theorem tailTrace_823392 : CollatzResearch.WordTrace tailWord_823392 prefixEnd_823392 140931954355649236237765 := by
  unfold tailWord_823392
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015786716499441501524215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20021048955332588668698953 15015786716499441501524215)
  ·
    refine ⟨22523680074749162252286323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15015786716499441501524215 22523680074749162252286323)
    ·
      refine ⟨33785520112123743378429485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22523680074749162252286323 33785520112123743378429485)
      ·
        refine ⟨12669570042046403766911057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33785520112123743378429485 12669570042046403766911057)
        ·
          refine ⟨9502177531534802825183293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12669570042046403766911057 9502177531534802825183293)
          ·
            refine ⟨3563316574325551059443735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9502177531534802825183293 3563316574325551059443735)
            ·
              refine ⟨5344974861488326589165603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563316574325551059443735 5344974861488326589165603)
              ·
                refine ⟨8017462292232489883748405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344974861488326589165603 8017462292232489883748405)
                ·
                  refine ⟨751637089896795926601413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8017462292232489883748405 751637089896795926601413)
                  ·
                    refine ⟨140931954355649236237765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751637089896795926601413 140931954355649236237765)
                    ·
                      rfl

theorem cell23_823392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_823392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823392 prefixEnd_823392 := by exact prefixLift 823392
  have htrace : WordTrace (prefixWord ++ tailWord_823392) baseStart_823392 baseEnd_823392 := by
    simpa [prefixWord, tailWord_823392, baseEnd_823392] using wordTrace_append hprefix tailTrace_823392
  have hstable : (prefixWord ++ tailWord_823392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823392).length < 2 ^ (prefixWord ++ tailWord_823392).sum := by decide
  have hdescent : baseEnd_823392 < baseStart_823392 := by decide
  rcases family_descends (prefixWord ++ tailWord_823392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823442 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_823442 : Nat := 118140960795 + 823442 * 2 ^ 59
def prefixEnd_823442 : Nat := 4983230072969 + 3 ^ 40 * 823442 * 2
def baseEnd_823442 : Nat := 422821537099672513088065

theorem tailTrace_823442 : CollatzResearch.WordTrace tailWord_823442 prefixEnd_823442 422821537099672513088065 := by
  unfold tailWord_823442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508349270704435385592145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20022264721878494361579053 7508349270704435385592145)
  ·
    refine ⟨5631261953028326539194109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7508349270704435385592145 5631261953028326539194109)
    ·
      refine ⟨2111723232385622452197791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5631261953028326539194109 2111723232385622452197791)
      ·
        refine ⟨3167584848578433678296687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111723232385622452197791 3167584848578433678296687)
        ·
          refine ⟨4751377272867650517445031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167584848578433678296687 4751377272867650517445031)
          ·
            refine ⟨7127065909301475776167547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751377272867650517445031 7127065909301475776167547)
            ·
              refine ⟨10690598863952213664251321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7127065909301475776167547 10690598863952213664251321)
              ·
                refine ⟨8017949147964160248188491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10690598863952213664251321 8017949147964160248188491)
                ·
                  refine ⟨12026923721946240372282737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8017949147964160248188491 12026923721946240372282737)
                  ·
                    refine ⟨9020192791459680279212053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12026923721946240372282737 9020192791459680279212053)
                    ·
                      refine ⟨422821537099672513088065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9020192791459680279212053 422821537099672513088065)
                      ·
                        rfl

theorem cell23_823442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_823442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823442 prefixEnd_823442 := by exact prefixLift 823442
  have htrace : WordTrace (prefixWord ++ tailWord_823442) baseStart_823442 baseEnd_823442 := by
    simpa [prefixWord, tailWord_823442, baseEnd_823442] using wordTrace_append hprefix tailTrace_823442
  have hstable : (prefixWord ++ tailWord_823442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823442).length < 2 ^ (prefixWord ++ tailWord_823442).sum := by decide
  have hdescent : baseEnd_823442 < baseStart_823442 := by decide
  rcases family_descends (prefixWord ++ tailWord_823442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823460 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_823460 : Nat := 118140960795 + 823460 * 2 ^ 59
def prefixEnd_823460 : Nat := 4983230072969 + 3 ^ 40 * 823460 * 2
def baseEnd_823460 : Nat := 140943593250484480887661

theorem tailTrace_823460 : CollatzResearch.WordTrace tailWord_823460 prefixEnd_823460 140943593250484480887661 := by
  unfold tailWord_823460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017026798376265308261917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20022702397835020411015889 15017026798376265308261917)
  ·
    refine ⟨5631385049391099490598219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15017026798376265308261917 5631385049391099490598219)
    ·
      refine ⟨8447077574086649235897329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5631385049391099490598219 8447077574086649235897329)
      ·
        refine ⟨6335308180564986926922997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8447077574086649235897329 6335308180564986926922997)
        ·
          refine ⟨593935141927967524399031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6335308180564986926922997 593935141927967524399031)
          ·
            refine ⟨890902712891951286598547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593935141927967524399031 890902712891951286598547)
            ·
              refine ⟨1336354069337926929897821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890902712891951286598547 1336354069337926929897821)
              ·
                refine ⟨501132776001722598711683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1336354069337926929897821 501132776001722598711683)
                ·
                  refine ⟨751699164002583898067525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501132776001722598711683 751699164002583898067525)
                  ·
                    refine ⟨140943593250484480887661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751699164002583898067525 140943593250484480887661)
                    ·
                      rfl

theorem cell23_823460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_823460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823460 prefixEnd_823460 := by exact prefixLift 823460
  have htrace : WordTrace (prefixWord ++ tailWord_823460) baseStart_823460 baseEnd_823460 := by
    simpa [prefixWord, tailWord_823460, baseEnd_823460] using wordTrace_append hprefix tailTrace_823460
  have hstable : (prefixWord ++ tailWord_823460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823460).length < 2 ^ (prefixWord ++ tailWord_823460).sum := by decide
  have hdescent : baseEnd_823460 < baseStart_823460 := by decide
  rcases family_descends (prefixWord ++ tailWord_823460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823483 : List Nat := [1, 1, 1, 1, 1, 2, 9, 2, 1, 1, 3]
def baseStart_823483 : Nat := 118140960795 + 823483 * 2 ^ 59
def prefixEnd_823483 : Nat := 4983230072969 + 3 ^ 40 * 823483 * 2
def baseEnd_823483 : Nat := 422842589806506852675377

theorem tailTrace_823483 : CollatzResearch.WordTrace tailWord_823483 prefixEnd_823483 422842589806506852675377 := by
  unfold tailWord_823483
  simp only [CollatzResearch.WordTrace]
  refine ⟨30034892475669205544611103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20023261650446137029740735 30034892475669205544611103)
  ·
    refine ⟨45052338713503808316916655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30034892475669205544611103 45052338713503808316916655)
    ·
      refine ⟨67578508070255712475374983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45052338713503808316916655 67578508070255712475374983)
      ·
        refine ⟨101367762105383568713062475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67578508070255712475374983 101367762105383568713062475)
        ·
          refine ⟨152051643158075353069593713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101367762105383568713062475 152051643158075353069593713)
          ·
            refine ⟨114038732368556514802195285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152051643158075353069593713 114038732368556514802195285)
            ·
              refine ⟨668195697472010828919113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 114038732368556514802195285 668195697472010828919113)
              ·
                refine ⟨501146773104008121689335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668195697472010828919113 501146773104008121689335)
                ·
                  refine ⟨751720159656012182534003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501146773104008121689335 751720159656012182534003)
                  ·
                    refine ⟨1127580239484018273801005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 751720159656012182534003 1127580239484018273801005)
                    ·
                      refine ⟨422842589806506852675377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1127580239484018273801005 422842589806506852675377)
                      ·
                        rfl

theorem cell23_823483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 1, 1, 3].length) (baseStart_823483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823483 prefixEnd_823483 := by exact prefixLift 823483
  have htrace : WordTrace (prefixWord ++ tailWord_823483) baseStart_823483 baseEnd_823483 := by
    simpa [prefixWord, tailWord_823483, baseEnd_823483] using wordTrace_append hprefix tailTrace_823483
  have hstable : (prefixWord ++ tailWord_823483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823483).length < 2 ^ (prefixWord ++ tailWord_823483).sum := by decide
  have hdescent : baseEnd_823483 < baseStart_823483 := by decide
  rcases family_descends (prefixWord ++ tailWord_823483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823490 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_823490 : Nat := 118140960795 + 823490 * 2 ^ 59
def prefixEnd_823490 : Nat := 4983230072969 + 3 ^ 40 * 823490 * 2
def baseEnd_823490 : Nat := 46982909352343147254205

theorem tailTrace_823490 : CollatzResearch.WordTrace tailWord_823490 prefixEnd_823490 46982909352343147254205 := by
  unfold tailWord_823490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508786946660961435028981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20023431857762563826743949 7508786946660961435028981)
  ·
    refine ⟨703948776249465134533967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7508786946660961435028981 703948776249465134533967)
    ·
      refine ⟨1055923164374197701800951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703948776249465134533967 1055923164374197701800951)
      ·
        refine ⟨1583884746561296552701427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055923164374197701800951 1583884746561296552701427)
        ·
          refine ⟨2375827119841944829052141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583884746561296552701427 2375827119841944829052141)
          ·
            refine ⟨890935169940729310894553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2375827119841944829052141 890935169940729310894553)
            ·
              refine ⟨668201377455546983170915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890935169940729310894553 668201377455546983170915)
              ·
                refine ⟨1002302066183320474756373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668201377455546983170915 1002302066183320474756373)
                ·
                  refine ⟨46982909352343147254205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1002302066183320474756373 46982909352343147254205)
                  ·
                    rfl

theorem cell23_823490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_823490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823490 prefixEnd_823490 := by exact prefixLift 823490
  have htrace : WordTrace (prefixWord ++ tailWord_823490) baseStart_823490 baseEnd_823490 := by
    simpa [prefixWord, tailWord_823490, baseEnd_823490] using wordTrace_append hprefix tailTrace_823490
  have hstable : (prefixWord ++ tailWord_823490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823490).length < 2 ^ (prefixWord ++ tailWord_823490).sum := by decide
  have hdescent : baseEnd_823490 < baseStart_823490 := by decide
  rcases family_descends (prefixWord ++ tailWord_823490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823499 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 2, 4]
def baseStart_823499 : Nat := 118140960795 + 823499 * 2 ^ 59
def prefixEnd_823499 : Nat := 4983230072969 + 3 ^ 40 * 823499 * 2
def baseEnd_823499 : Nat := 140950268498992930025101

theorem tailTrace_823499 : CollatzResearch.WordTrace tailWord_823499 prefixEnd_823499 140950268498992930025101 := by
  unfold tailWord_823499
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035476043611240277193551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20023650695740826851462367 30035476043611240277193551)
  ·
    refine ⟨45053214065416860415790327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30035476043611240277193551 45053214065416860415790327)
    ·
      refine ⟨67579821098125290623685491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45053214065416860415790327 67579821098125290623685491)
      ·
        refine ⟨101369731647187935935528237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67579821098125290623685491 101369731647187935935528237)
        ·
          refine ⟨38013649367695475975823089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101369731647187935935528237 38013649367695475975823089)
          ·
            refine ⟨28510237025771606981867317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38013649367695475975823089 28510237025771606981867317)
            ·
              refine ⟨2672834721166088154550061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28510237025771606981867317 2672834721166088154550061)
              ·
                refine ⟨1002313020437283057956273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2672834721166088154550061 1002313020437283057956273)
                ·
                  refine ⟨751734765327962293467205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002313020437283057956273 751734765327962293467205)
                  ·
                    refine ⟨140950268498992930025101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751734765327962293467205 140950268498992930025101)
                    ·
                      rfl

theorem cell23_823499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 4].length) (baseStart_823499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823499 prefixEnd_823499 := by exact prefixLift 823499
  have htrace : WordTrace (prefixWord ++ tailWord_823499) baseStart_823499 baseEnd_823499 := by
    simpa [prefixWord, tailWord_823499, baseEnd_823499] using wordTrace_append hprefix tailTrace_823499
  have hstable : (prefixWord ++ tailWord_823499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823499).length < 2 ^ (prefixWord ++ tailWord_823499).sum := by decide
  have hdescent : baseEnd_823499 < baseStart_823499 := by decide
  rcases family_descends (prefixWord ++ tailWord_823499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823506 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_823506 : Nat := 118140960795 + 823506 * 2 ^ 59
def prefixEnd_823506 : Nat := 4983230072969 + 3 ^ 40 * 823506 * 2
def baseEnd_823506 : Nat := 422854399861560262687771

theorem tailTrace_823506 : CollatzResearch.WordTrace tailWord_823506 prefixEnd_823506 422854399861560262687771 := by
  unfold tailWord_823506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7508932838646470118174593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20023820903057253648465581 7508932838646470118174593)
  ·
    refine ⟨5631699628984852588630945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7508932838646470118174593 5631699628984852588630945)
    ·
      refine ⟨4223774721738639441473209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5631699628984852588630945 4223774721738639441473209)
      ·
        refine ⟨3167831041303979581104907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4223774721738639441473209 3167831041303979581104907)
        ·
          refine ⟨4751746561955969371657361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167831041303979581104907 4751746561955969371657361)
          ·
            refine ⟨3563809921466977028743021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4751746561955969371657361 3563809921466977028743021)
            ·
              refine ⟨1336428720550116385778633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3563809921466977028743021 1336428720550116385778633)
              ·
                refine ⟨1002321540412587289333975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336428720550116385778633 1002321540412587289333975)
                ·
                  refine ⟨1503482310618880934000963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002321540412587289333975 1503482310618880934000963)
                  ·
                    refine ⟨2255223465928321401001445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1503482310618880934000963 2255223465928321401001445)
                    ·
                      refine ⟨422854399861560262687771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2255223465928321401001445 422854399861560262687771)
                      ·
                        rfl

theorem cell23_823506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_823506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823506 prefixEnd_823506 := by exact prefixLift 823506
  have htrace : WordTrace (prefixWord ++ tailWord_823506) baseStart_823506 baseEnd_823506 := by
    simpa [prefixWord, tailWord_823506, baseEnd_823506] using wordTrace_append hprefix tailTrace_823506
  have hstable : (prefixWord ++ tailWord_823506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823506).length < 2 ^ (prefixWord ++ tailWord_823506).sum := by decide
  have hdescent : baseEnd_823506 < baseStart_823506 := by decide
  rcases family_descends (prefixWord ++ tailWord_823506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823510 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_823510 : Nat := 118140960795 + 823510 * 2 ^ 59
def prefixEnd_823510 : Nat := 4983230072969 + 3 ^ 40 * 823510 * 2
def baseEnd_823510 : Nat := 422856453784178247037753

theorem tailTrace_823510 : CollatzResearch.WordTrace tailWord_823510 prefixEnd_823510 422856453784178247037753 := by
  unfold tailWord_823510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877242327910711822240249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20023918164380926103895989 1877242327910711822240249)
  ·
    refine ⟨1407931745933033866680187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1877242327910711822240249 1407931745933033866680187)
    ·
      refine ⟨2111897618899550800020281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407931745933033866680187 2111897618899550800020281)
      ·
        refine ⟨1583923214174663100015211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111897618899550800020281 1583923214174663100015211)
        ·
          refine ⟨2375884821261994650022817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583923214174663100015211 2375884821261994650022817)
          ·
            refine ⟨1781913615946495987517113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375884821261994650022817 1781913615946495987517113)
            ·
              refine ⟨1336435211959871990637835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781913615946495987517113 1336435211959871990637835)
              ·
                refine ⟨2004652817939807985956753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336435211959871990637835 2004652817939807985956753)
                ·
                  refine ⟨1503489613454855989467565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2004652817939807985956753 1503489613454855989467565)
                  ·
                    refine ⟨563808605045570996050337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503489613454855989467565 563808605045570996050337)
                    ·
                      refine ⟨422856453784178247037753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563808605045570996050337 422856453784178247037753)
                      ·
                        rfl

theorem cell23_823510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_823510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823510 prefixEnd_823510 := by exact prefixLift 823510
  have htrace : WordTrace (prefixWord ++ tailWord_823510) baseStart_823510 baseEnd_823510 := by
    simpa [prefixWord, tailWord_823510, baseEnd_823510] using wordTrace_append hprefix tailTrace_823510
  have hstable : (prefixWord ++ tailWord_823510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823510).length < 2 ^ (prefixWord ++ tailWord_823510).sum := by decide
  have hdescent : baseEnd_823510 < baseStart_823510 := by decide
  rcases family_descends (prefixWord ++ tailWord_823510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823512 : List Nat := [2, 1, 2, 2, 4, 1, 2, 9]
def baseStart_823512 : Nat := 118140960795 + 823512 * 2 ^ 59
def prefixEnd_823512 : Nat := 4983230072969 + 3 ^ 40 * 823512 * 2
def baseEnd_823512 : Nat := 15661388175758786637509

theorem tailTrace_823512 : CollatzResearch.WordTrace tailWord_823512 prefixEnd_823512 15661388175758786637509 := by
  unfold tailWord_823512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017975096282071748708395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20023966795042762331611193 15017975096282071748708395)
  ·
    refine ⟨22526962644423107623062593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15017975096282071748708395 22526962644423107623062593)
    ·
      refine ⟨16895221983317330717296945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22526962644423107623062593 16895221983317330717296945)
      ·
        refine ⟨12671416487487998037972709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16895221983317330717296945 12671416487487998037972709)
        ·
          refine ⟨2375890591403999632119883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12671416487487998037972709 2375890591403999632119883)
          ·
            refine ⟨3563835887105999448179825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375890591403999632119883 3563835887105999448179825)
            ·
              refine ⟨2672876915329499586134869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563835887105999448179825 2672876915329499586134869)
              ·
                refine ⟨15661388175758786637509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2672876915329499586134869 15661388175758786637509)
                ·
                  rfl

theorem cell23_823512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 9].length) (baseStart_823512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823512 prefixEnd_823512 := by exact prefixLift 823512
  have htrace : WordTrace (prefixWord ++ tailWord_823512) baseStart_823512 baseEnd_823512 := by
    simpa [prefixWord, tailWord_823512, baseEnd_823512] using wordTrace_append hprefix tailTrace_823512
  have hstable : (prefixWord ++ tailWord_823512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823512).length < 2 ^ (prefixWord ++ tailWord_823512).sum := by decide
  have hdescent : baseEnd_823512 < baseStart_823512 := by decide
  rcases family_descends (prefixWord ++ tailWord_823512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823533 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_823533 : Nat := 118140960795 + 823533 * 2 ^ 59
def prefixEnd_823533 : Nat := 4983230072969 + 3 ^ 40 * 823533 * 2
def baseEnd_823533 : Nat := 140956087946410552350049

theorem tailTrace_823533 : CollatzResearch.WordTrace tailWord_823533 prefixEnd_823533 140956087946410552350049 := by
  unfold tailWord_823533
  simp only [CollatzResearch.WordTrace]
  refine ⟨30036716125488064083931253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20024477416992042722620835 30036716125488064083931253)
  ·
    refine ⟨2815942136764506007868555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30036716125488064083931253 2815942136764506007868555)
    ·
      refine ⟨4223913205146759011802833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815942136764506007868555 4223913205146759011802833)
      ·
        refine ⟨3167934903860069258852125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4223913205146759011802833 3167934903860069258852125)
        ·
          refine ⟨1187975588947525972069547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3167934903860069258852125 1187975588947525972069547)
          ·
            refine ⟨1781963383421288958104321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187975588947525972069547 1781963383421288958104321)
            ·
              refine ⟨1336472537565966718578241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781963383421288958104321 1336472537565966718578241)
              ·
                refine ⟨1002354403174475038933681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336472537565966718578241 1002354403174475038933681)
                ·
                  refine ⟨751765802380856279200261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002354403174475038933681 751765802380856279200261)
                  ·
                    refine ⟨140956087946410552350049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 751765802380856279200261 140956087946410552350049)
                    ·
                      rfl

theorem cell23_823533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_823533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823533 prefixEnd_823533 := by exact prefixLift 823533
  have htrace : WordTrace (prefixWord ++ tailWord_823533) baseStart_823533 baseEnd_823533 := by
    simpa [prefixWord, tailWord_823533, baseEnd_823533] using wordTrace_append hprefix tailTrace_823533
  have hstable : (prefixWord ++ tailWord_823533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823533).length < 2 ^ (prefixWord ++ tailWord_823533).sum := by decide
  have hdescent : baseEnd_823533 < baseStart_823533 := by decide
  rcases family_descends (prefixWord ++ tailWord_823533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823566 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2]
def baseStart_823566 : Nat := 118140960795 + 823566 * 2 ^ 59
def prefixEnd_823566 : Nat := 4983230072969 + 3 ^ 40 * 823566 * 2
def baseEnd_823566 : Nat := 422885208700830027937495

theorem tailTrace_823566 : CollatzResearch.WordTrace tailWord_823566 prefixEnd_823566 422885208700830027937495 := by
  unfold tailWord_823566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754739966796063839985319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20025279822912340479921701 3754739966796063839985319)
  ·
    refine ⟨5632109950194095759977979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3754739966796063839985319 5632109950194095759977979)
    ·
      refine ⟨8448164925291143639966969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5632109950194095759977979 8448164925291143639966969)
      ·
        refine ⟨6336123693968357729975227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8448164925291143639966969 6336123693968357729975227)
        ·
          refine ⟨9504185540952536594962841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336123693968357729975227 9504185540952536594962841)
          ·
            refine ⟨7128139155714402446222131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9504185540952536594962841 7128139155714402446222131)
            ·
              refine ⟨10692208733571603669333197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128139155714402446222131 10692208733571603669333197)
              ·
                refine ⟨4009578275089351375999949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10692208733571603669333197 4009578275089351375999949)
                ·
                  refine ⟨1503591853158506765999981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4009578275089351375999949 1503591853158506765999981)
                  ·
                    refine ⟨563846944934440037249993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503591853158506765999981 563846944934440037249993)
                    ·
                      refine ⟨422885208700830027937495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563846944934440037249993 422885208700830027937495)
                      ·
                        rfl

theorem cell23_823566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_823566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823566 prefixEnd_823566 := by exact prefixLift 823566
  have htrace : WordTrace (prefixWord ++ tailWord_823566) baseStart_823566 baseEnd_823566 := by
    simpa [prefixWord, tailWord_823566, baseEnd_823566] using wordTrace_append hprefix tailTrace_823566
  have hstable : (prefixWord ++ tailWord_823566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823566).length < 2 ^ (prefixWord ++ tailWord_823566).sum := by decide
  have hdescent : baseEnd_823566 < baseStart_823566 := by decide
  rcases family_descends (prefixWord ++ tailWord_823566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823583 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 1, 3, 2]
def baseStart_823583 : Nat := 118140960795 + 823583 * 2 ^ 59
def prefixEnd_823583 : Nat := 4983230072969 + 3 ^ 40 * 823583 * 2
def baseEnd_823583 : Nat := 422893937871956461424917

theorem tailTrace_823583 : CollatzResearch.WordTrace tailWord_823583 prefixEnd_823583 422893937871956461424917 := by
  unfold tailWord_823583
  simp only [CollatzResearch.WordTrace]
  refine ⟨30038539775306922623251403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20025693183537948415500935 30038539775306922623251403)
  ·
    refine ⟨45057809662960383934877105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30038539775306922623251403 45057809662960383934877105)
    ·
      refine ⟨33793357247220287951157829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45057809662960383934877105 33793357247220287951157829)
      ·
        refine ⟨6336254483853803990842093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33793357247220287951157829 6336254483853803990842093)
        ·
          refine ⟨2376095431445176496565785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6336254483853803990842093 2376095431445176496565785)
          ·
            refine ⟨1782071573583882372424339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376095431445176496565785 1782071573583882372424339)
            ·
              refine ⟨2673107360375823558636509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782071573583882372424339 2673107360375823558636509)
              ·
                refine ⟨1002415260140933834488691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2673107360375823558636509 1002415260140933834488691)
                ·
                  refine ⟨1503622890211400751733037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002415260140933834488691 1503622890211400751733037)
                  ·
                    refine ⟨563858583829275281899889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1503622890211400751733037 563858583829275281899889)
                    ·
                      refine ⟨422893937871956461424917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563858583829275281899889 422893937871956461424917)
                      ·
                        rfl

theorem cell23_823583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_823583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823583 prefixEnd_823583 := by exact prefixLift 823583
  have htrace : WordTrace (prefixWord ++ tailWord_823583) baseStart_823583 baseEnd_823583 := by
    simpa [prefixWord, tailWord_823583, baseEnd_823583] using wordTrace_append hprefix tailTrace_823583
  have hstable : (prefixWord ++ tailWord_823583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823583).length < 2 ^ (prefixWord ++ tailWord_823583).sum := by decide
  have hdescent : baseEnd_823583 < baseStart_823583 := by decide
  rcases family_descends (prefixWord ++ tailWord_823583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823653 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 5]
def baseStart_823653 : Nat := 118140960795 + 823653 * 2 ^ 59
def prefixEnd_823653 : Nat := 4983230072969 + 3 ^ 40 * 823653 * 2
def baseEnd_823653 : Nat := 46992209057530131949955

theorem tailTrace_823653 : CollatzResearch.WordTrace tailWord_823653 prefixEnd_823653 46992209057530131949955 := by
  unfold tailWord_823653
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041092885053324578299613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20027395256702216385533075 30041092885053324578299613)
  ·
    refine ⟨11265409831894996716862355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30041092885053324578299613 11265409831894996716862355)
    ·
      refine ⟨16898114747842495075293533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11265409831894996716862355 16898114747842495075293533)
      ·
        refine ⟨6336793030440935653235075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16898114747842495075293533 6336793030440935653235075)
        ·
          refine ⟨9505189545661403479852613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336793030440935653235075 9505189545661403479852613)
          ·
            refine ⟨1782223039811513152472365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9505189545661403479852613 1782223039811513152472365)
            ·
              refine ⟨668333639929317432177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1782223039811513152472365 668333639929317432177137)
              ·
                refine ⟨501250229946988074132853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668333639929317432177137 501250229946988074132853)
                ·
                  refine ⟨46992209057530131949955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501250229946988074132853 46992209057530131949955)
                  ·
                    rfl

theorem cell23_823653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_823653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823653 prefixEnd_823653 := by exact prefixLift 823653
  have htrace : WordTrace (prefixWord ++ tailWord_823653) baseStart_823653 baseEnd_823653 := by
    simpa [prefixWord, tailWord_823653, baseEnd_823653] using wordTrace_append hprefix tailTrace_823653
  have hstable : (prefixWord ++ tailWord_823653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823653).length < 2 ^ (prefixWord ++ tailWord_823653).sum := by decide
  have hdescent : baseEnd_823653 < baseStart_823653 := by decide
  rcases family_descends (prefixWord ++ tailWord_823653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823720 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_823720 : Nat := 118140960795 + 823720 * 2 ^ 59
def prefixEnd_823720 : Nat := 4983230072969 + 3 ^ 40 * 823720 * 2
def baseEnd_823720 : Nat := 422964284721622425411787

theorem tailTrace_823720 : CollatzResearch.WordTrace tailWord_823720 prefixEnd_823720 422964284721622425411787 := by
  unfold tailWord_823720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15021768287905297510494307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20029024383873730013992409 15021768287905297510494307)
  ·
    refine ⟨22532652431857946265741461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15021768287905297510494307 22532652431857946265741461)
    ·
      refine ⟨1056218082743341231206631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22532652431857946265741461 1056218082743341231206631)
      ·
        refine ⟨1584327124115011846809947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056218082743341231206631 1584327124115011846809947)
        ·
          refine ⟨2376490686172517770214921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584327124115011846809947 2376490686172517770214921)
          ·
            refine ⟨1782368014629388327661191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376490686172517770214921 1782368014629388327661191)
            ·
              refine ⟨2673552021944082491491787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782368014629388327661191 2673552021944082491491787)
              ·
                refine ⟨4010328032916123737237681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673552021944082491491787 4010328032916123737237681)
                ·
                  refine ⟨3007746024687092802928261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4010328032916123737237681 3007746024687092802928261)
                  ·
                    refine ⟨563952379628829900549049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3007746024687092802928261 563952379628829900549049)
                    ·
                      refine ⟨422964284721622425411787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 563952379628829900549049 422964284721622425411787)
                      ·
                        rfl

theorem cell23_823720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_823720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823720 prefixEnd_823720 := by exact prefixLift 823720
  have htrace : WordTrace (prefixWord ++ tailWord_823720) baseStart_823720 baseEnd_823720 := by
    simpa [prefixWord, tailWord_823720, baseEnd_823720] using wordTrace_append hprefix tailTrace_823720
  have hstable : (prefixWord ++ tailWord_823720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823720).length < 2 ^ (prefixWord ++ tailWord_823720).sum := by decide
  have hdescent : baseEnd_823720 < baseStart_823720 := by decide
  rcases family_descends (prefixWord ++ tailWord_823720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823740 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_823740 : Nat := 118140960795 + 823740 * 2 ^ 59
def prefixEnd_823740 : Nat := 4983230072969 + 3 ^ 40 * 823740 * 2
def baseEnd_823740 : Nat := 422974554334712347161695

theorem tailTrace_823740 : CollatzResearch.WordTrace tailWord_823740 prefixEnd_823740 422974554334712347161695 := by
  unfold tailWord_823740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15022133017869069218358337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20029510690492092291144449 15022133017869069218358337)
  ·
    refine ⟨11266599763401801913768753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15022133017869069218358337 11266599763401801913768753)
    ·
      refine ⟨8449949822551351435326565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11266599763401801913768753 8449949822551351435326565)
      ·
        refine ⟨1584365591728378394123731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8449949822551351435326565 1584365591728378394123731)
        ·
          refine ⟨2376548387592567591185597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584365591728378394123731 2376548387592567591185597)
          ·
            refine ⟨891205645347212846694599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2376548387592567591185597 891205645347212846694599)
            ·
              refine ⟨1336808468020819270041899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891205645347212846694599 1336808468020819270041899)
              ·
                refine ⟨2005212702031228905062849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336808468020819270041899 2005212702031228905062849)
                ·
                  refine ⟨1503909526523421678797137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005212702031228905062849 1503909526523421678797137)
                  ·
                    refine ⟨1127932144892566259097853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1503909526523421678797137 1127932144892566259097853)
                    ·
                      refine ⟨422974554334712347161695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1127932144892566259097853 422974554334712347161695)
                      ·
                        rfl

theorem cell23_823740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_823740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823740 prefixEnd_823740 := by exact prefixLift 823740
  have htrace : WordTrace (prefixWord ++ tailWord_823740) baseStart_823740 baseEnd_823740 := by
    simpa [prefixWord, tailWord_823740, baseEnd_823740] using wordTrace_append hprefix tailTrace_823740
  have hstable : (prefixWord ++ tailWord_823740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823740).length < 2 ^ (prefixWord ++ tailWord_823740).sum := by decide
  have hdescent : baseEnd_823740 < baseStart_823740 := by decide
  rcases family_descends (prefixWord ++ tailWord_823740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823770 : List Nat := [3, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3]
def baseStart_823770 : Nat := 118140960795 + 823770 * 2 ^ 59
def prefixEnd_823770 : Nat := 4983230072969 + 3 ^ 40 * 823770 * 2
def baseEnd_823770 : Nat := 422989958754347229786557

theorem tailTrace_823770 : CollatzResearch.WordTrace tailWord_823770 prefixEnd_823770 422989958754347229786557 := by
  unfold tailWord_823770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511340056407363390077191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20030240150419635706872509 7511340056407363390077191)
  ·
    refine ⟨11267010084611045085115787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7511340056407363390077191 11267010084611045085115787)
    ·
      refine ⟨16900515126916567627673681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11267010084611045085115787 16900515126916567627673681)
      ·
        refine ⟨12675386345187425720755261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16900515126916567627673681 12675386345187425720755261)
        ·
          refine ⟨4753269879445284645283223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12675386345187425720755261 4753269879445284645283223)
          ·
            refine ⟨7129904819167926967924835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753269879445284645283223 7129904819167926967924835)
            ·
              refine ⟨10694857228751890451887253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7129904819167926967924835 10694857228751890451887253)
              ·
                refine ⟨501321432597744864932215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10694857228751890451887253 501321432597744864932215)
                ·
                  refine ⟨751982148896617297398323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501321432597744864932215 751982148896617297398323)
                  ·
                    refine ⟨1127973223344925946097485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 751982148896617297398323 1127973223344925946097485)
                    ·
                      refine ⟨422989958754347229786557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1127973223344925946097485 422989958754347229786557)
                      ·
                        rfl

theorem cell23_823770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_823770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823770 prefixEnd_823770 := by exact prefixLift 823770
  have htrace : WordTrace (prefixWord ++ tailWord_823770) baseStart_823770 baseEnd_823770 := by
    simpa [prefixWord, tailWord_823770, baseEnd_823770] using wordTrace_append hprefix tailTrace_823770
  have hstable : (prefixWord ++ tailWord_823770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823770).length < 2 ^ (prefixWord ++ tailWord_823770).sum := by decide
  have hdescent : baseEnd_823770 < baseStart_823770 := by decide
  rcases family_descends (prefixWord ++ tailWord_823770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823793 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_823793 : Nat := 118140960795 + 823793 * 2 ^ 59
def prefixEnd_823793 : Nat := 4983230072969 + 3 ^ 40 * 823793 * 2
def baseEnd_823793 : Nat := 423001768809400639798951

theorem tailTrace_823793 : CollatzResearch.WordTrace tailWord_823793 prefixEnd_823793 423001768809400639798951 := by
  unfold tailWord_823793
  simp only [CollatzResearch.WordTrace]
  refine ⟨30046199104546128488396033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20030799403030752325597355 30046199104546128488396033)
  ·
    refine ⟨22534649328409596366297025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30046199104546128488396033 22534649328409596366297025)
    ·
      refine ⟨16900986996307197274722769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22534649328409596366297025 16900986996307197274722769)
      ·
        refine ⟨12675740247230397956042077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16900986996307197274722769 12675740247230397956042077)
        ·
          refine ⟨4753402592711399233515779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12675740247230397956042077 4753402592711399233515779)
          ·
            refine ⟨7130103889067098850273669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4753402592711399233515779 7130103889067098850273669)
            ·
              refine ⟨1336894479200081034426313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7130103889067098850273669 1336894479200081034426313)
              ·
                refine ⟨1002670859400060775819735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336894479200081034426313 1002670859400060775819735)
                ·
                  refine ⟨1504006289100091163729603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002670859400060775819735 1504006289100091163729603)
                  ·
                    refine ⟨2256009433650136745594405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1504006289100091163729603 2256009433650136745594405)
                    ·
                      refine ⟨423001768809400639798951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2256009433650136745594405 423001768809400639798951)
                      ·
                        rfl

theorem cell23_823793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_823793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823793 prefixEnd_823793 := by exact prefixLift 823793
  have htrace : WordTrace (prefixWord ++ tailWord_823793) baseStart_823793 baseEnd_823793 := by
    simpa [prefixWord, tailWord_823793, baseEnd_823793] using wordTrace_append hprefix tailTrace_823793
  have hstable : (prefixWord ++ tailWord_823793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823793).length < 2 ^ (prefixWord ++ tailWord_823793).sum := by decide
  have hdescent : baseEnd_823793 < baseStart_823793 := by decide
  rcases family_descends (prefixWord ++ tailWord_823793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823813 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_823813 : Nat := 118140960795 + 823813 * 2 ^ 59
def prefixEnd_823813 : Nat := 4983230072969 + 3 ^ 40 * 823813 * 2
def baseEnd_823813 : Nat := 423012038422490561548859

theorem tailTrace_823813 : CollatzResearch.WordTrace tailWord_823813 prefixEnd_823813 423012038422490561548859 := by
  unfold tailWord_823813
  simp only [CollatzResearch.WordTrace]
  refine ⟨30046928564473671904124093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20031285709649114602749395 30046928564473671904124093)
  ·
    refine ⟨11267598211677626964046535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30046928564473671904124093 11267598211677626964046535)
    ·
      refine ⟨16901397317516440446069803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11267598211677626964046535 16901397317516440446069803)
      ·
        refine ⟨25352095976274660669104705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16901397317516440446069803 25352095976274660669104705)
        ·
          refine ⟨19014071982205995501828529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25352095976274660669104705 19014071982205995501828529)
          ·
            refine ⟨14260553986654496626371397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19014071982205995501828529 14260553986654496626371397)
            ·
              refine ⟨2673853872497718117444637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14260553986654496626371397 2673853872497718117444637)
              ·
                refine ⟨1002695202186644294041739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2673853872497718117444637 1002695202186644294041739)
                ·
                  refine ⟨1504042803279966441062609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002695202186644294041739 1504042803279966441062609)
                  ·
                    refine ⟨1128032102459974830796957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1504042803279966441062609 1128032102459974830796957)
                    ·
                      refine ⟨423012038422490561548859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1128032102459974830796957 423012038422490561548859)
                      ·
                        rfl

theorem cell23_823813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_823813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823813 prefixEnd_823813 := by exact prefixLift 823813
  have htrace : WordTrace (prefixWord ++ tailWord_823813) baseStart_823813 baseEnd_823813 := by
    simpa [prefixWord, tailWord_823813, baseEnd_823813] using wordTrace_append hprefix tailTrace_823813
  have hstable : (prefixWord ++ tailWord_823813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823813).length < 2 ^ (prefixWord ++ tailWord_823813).sum := by decide
  have hdescent : baseEnd_823813 < baseStart_823813 := by decide
  rcases family_descends (prefixWord ++ tailWord_823813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823814 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_823814 : Nat := 118140960795 + 823814 * 2 ^ 59
def prefixEnd_823814 : Nat := 4983230072969 + 3 ^ 40 * 823814 * 2
def baseEnd_823814 : Nat := 423012551903145057636355

theorem tailTrace_823814 : CollatzResearch.WordTrace tailWord_823814 prefixEnd_823814 423012551903145057636355 := by
  unfold tailWord_823814
  simp only [CollatzResearch.WordTrace]
  refine ⟨938967657420939033590953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20031310024980032716606997 938967657420939033590953)
  ·
    refine ⟨704225743065704275193215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 938967657420939033590953 704225743065704275193215)
    ·
      refine ⟨1056338614598556412789823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704225743065704275193215 1056338614598556412789823)
      ·
        refine ⟨1584507921897834619184735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056338614598556412789823 1584507921897834619184735)
        ·
          refine ⟨2376761882846751928777103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1584507921897834619184735 2376761882846751928777103)
          ·
            refine ⟨3565142824270127893165655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376761882846751928777103 3565142824270127893165655)
            ·
              refine ⟨5347714236405191839748483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565142824270127893165655 5347714236405191839748483)
              ·
                refine ⟨8021571354607787759622725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347714236405191839748483 8021571354607787759622725)
                ·
                  refine ⟨1504044628988960204929261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8021571354607787759622725 1504044628988960204929261)
                  ·
                    refine ⟨564016735870860076848473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1504044628988960204929261 564016735870860076848473)
                    ·
                      refine ⟨423012551903145057636355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564016735870860076848473 423012551903145057636355)
                      ·
                        rfl

theorem cell23_823814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_823814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823814 prefixEnd_823814 := by exact prefixLift 823814
  have htrace : WordTrace (prefixWord ++ tailWord_823814) baseStart_823814 baseEnd_823814 := by
    simpa [prefixWord, tailWord_823814, baseEnd_823814] using wordTrace_append hprefix tailTrace_823814
  have hstable : (prefixWord ++ tailWord_823814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823814).length < 2 ^ (prefixWord ++ tailWord_823814).sum := by decide
  have hdescent : baseEnd_823814 < baseStart_823814 := by decide
  rcases family_descends (prefixWord ++ tailWord_823814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823837 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_823837 : Nat := 118140960795 + 823837 * 2 ^ 59
def prefixEnd_823837 : Nat := 4983230072969 + 3 ^ 40 * 823837 * 2
def baseEnd_823837 : Nat := 141008120652732822549583

theorem tailTrace_823837 : CollatzResearch.WordTrace tailWord_823837 prefixEnd_823837 141008120652732822549583 := by
  unfold tailWord_823837
  simp only [CollatzResearch.WordTrace]
  refine ⟨30047803916386724002997765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20031869277591149335331843 30047803916386724002997765)
  ·
    refine ⟨5633963234322510750562081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30047803916386724002997765 5633963234322510750562081)
    ·
      refine ⟨4225472425741883062921561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5633963234322510750562081 4225472425741883062921561)
      ·
        refine ⟨3169104319306412297191171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4225472425741883062921561 3169104319306412297191171)
        ·
          refine ⟨4753656478959618445786757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3169104319306412297191171 4753656478959618445786757)
          ·
            refine ⟨891310589804928458585017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4753656478959618445786757 891310589804928458585017)
            ·
              refine ⟨668482942353696343938763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891310589804928458585017 668482942353696343938763)
              ·
                refine ⟨1002724413530544515908145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668482942353696343938763 1002724413530544515908145)
                ·
                  refine ⟨752043310147908386931109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002724413530544515908145 752043310147908386931109)
                  ·
                    refine ⟨141008120652732822549583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752043310147908386931109 141008120652732822549583)
                    ·
                      rfl

theorem cell23_823837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_823837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823837 prefixEnd_823837 := by exact prefixLift 823837
  have htrace : WordTrace (prefixWord ++ tailWord_823837) baseStart_823837 baseEnd_823837 := by
    simpa [prefixWord, tailWord_823837, baseEnd_823837] using wordTrace_append hprefix tailTrace_823837
  have hstable : (prefixWord ++ tailWord_823837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823837).length < 2 ^ (prefixWord ++ tailWord_823837).sum := by decide
  have hdescent : baseEnd_823837 < baseStart_823837 := by decide
  rcases family_descends (prefixWord ++ tailWord_823837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823844 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_823844 : Nat := 118140960795 + 823844 * 2 ^ 59
def prefixEnd_823844 : Nat := 4983230072969 + 3 ^ 40 * 823844 * 2
def baseEnd_823844 : Nat := 423027956322779940261217

theorem tailTrace_823844 : CollatzResearch.WordTrace tailWord_823844 prefixEnd_823844 423027956322779940261217 := by
  unfold tailWord_823844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15024029613680682099251293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20032039484907576132335057 15024029613680682099251293)
  ·
    refine ⟨5634011105130255787219235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15024029613680682099251293 5634011105130255787219235)
    ·
      refine ⟨8451016657695383680828853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5634011105130255787219235 8451016657695383680828853)
      ·
        refine ⟨792282811658942220077705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8451016657695383680828853 792282811658942220077705)
        ·
          refine ⟨594212108744206665058279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792282811658942220077705 594212108744206665058279)
          ·
            refine ⟨891318163116309997587419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594212108744206665058279 891318163116309997587419)
            ·
              refine ⟨1336977244674464996381129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891318163116309997587419 1336977244674464996381129)
              ·
                refine ⟨1002732933505848747285847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336977244674464996381129 1002732933505848747285847)
                ·
                  refine ⟨1504099400258773120928771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1002732933505848747285847 1504099400258773120928771)
                  ·
                    refine ⟨2256149100388159681393157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1504099400258773120928771 2256149100388159681393157)
                    ·
                      refine ⟨423027956322779940261217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2256149100388159681393157 423027956322779940261217)
                      ·
                        rfl

theorem cell23_823844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_823844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823844 prefixEnd_823844 := by exact prefixLift 823844
  have htrace : WordTrace (prefixWord ++ tailWord_823844) baseStart_823844 baseEnd_823844 := by
    simpa [prefixWord, tailWord_823844, baseEnd_823844] using wordTrace_append hprefix tailTrace_823844
  have hstable : (prefixWord ++ tailWord_823844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823844).length < 2 ^ (prefixWord ++ tailWord_823844).sum := by decide
  have hdescent : baseEnd_823844 < baseStart_823844 := by decide
  rcases family_descends (prefixWord ++ tailWord_823844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823847 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_823847 : Nat := 118140960795 + 823847 * 2 ^ 59
def prefixEnd_823847 : Nat := 4983230072969 + 3 ^ 40 * 823847 * 2
def baseEnd_823847 : Nat := 423029496764743428523703

theorem tailTrace_823847 : CollatzResearch.WordTrace tailWord_823847 prefixEnd_823847 423029496764743428523703 := by
  unfold tailWord_823847
  simp only [CollatzResearch.WordTrace]
  refine ⟨30048168646350495710861795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20032112430900330473907863 30048168646350495710861795)
  ·
    refine ⟨45072252969525743566292693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30048168646350495710861795 45072252969525743566292693)
    ·
      refine ⟨1056380928973259614834985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45072252969525743566292693 1056380928973259614834985)
      ·
        refine ⟨792285696729944711126239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056380928973259614834985 792285696729944711126239)
        ·
          refine ⟨1188428545094917066689359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792285696729944711126239 1188428545094917066689359)
          ·
            refine ⟨1782642817642375600034039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188428545094917066689359 1782642817642375600034039)
            ·
              refine ⟨2673964226463563400051059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782642817642375600034039 2673964226463563400051059)
              ·
                refine ⟨4010946339695345100076589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673964226463563400051059 4010946339695345100076589)
                ·
                  refine ⟨1504104877385754412528721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4010946339695345100076589 1504104877385754412528721)
                  ·
                    refine ⟨1128078658039315809396541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1504104877385754412528721 1128078658039315809396541)
                    ·
                      refine ⟨423029496764743428523703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1128078658039315809396541 423029496764743428523703)
                      ·
                        rfl

theorem cell23_823847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_823847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823847 prefixEnd_823847 := by exact prefixLift 823847
  have htrace : WordTrace (prefixWord ++ tailWord_823847) baseStart_823847 baseEnd_823847 := by
    simpa [prefixWord, tailWord_823847, baseEnd_823847] using wordTrace_append hprefix tailTrace_823847
  have hstable : (prefixWord ++ tailWord_823847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823847).length < 2 ^ (prefixWord ++ tailWord_823847).sum := by decide
  have hdescent : baseEnd_823847 < baseStart_823847 := by decide
  rcases family_descends (prefixWord ++ tailWord_823847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823878 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_823878 : Nat := 118140960795 + 823878 * 2 ^ 59
def prefixEnd_823878 : Nat := 4983230072969 + 3 ^ 40 * 823878 * 2
def baseEnd_823878 : Nat := 423045414665032807236061

theorem tailTrace_823878 : CollatzResearch.WordTrace tailWord_823878 prefixEnd_823878 423045414665032807236061 := by
  unfold tailWord_823878
  simp only [CollatzResearch.WordTrace]
  refine ⟨939040603413693375163759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20032866206158792003493525 939040603413693375163759)
  ·
    refine ⟨1408560905120540062745639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 939040603413693375163759 1408560905120540062745639)
    ·
      refine ⟨2112841357680810094118459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408560905120540062745639 2112841357680810094118459)
      ·
        refine ⟨3169262036521215141177689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112841357680810094118459 3169262036521215141177689)
        ·
          refine ⟨2376946527390911355883267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3169262036521215141177689 2376946527390911355883267)
          ·
            refine ⟨3565419791086367033824901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376946527390911355883267 3565419791086367033824901)
            ·
              refine ⟨668516210828693818842169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3565419791086367033824901 668516210828693818842169)
              ·
                refine ⟨501387158121520364131627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668516210828693818842169 501387158121520364131627)
                ·
                  refine ⟨752080737182280546197441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501387158121520364131627 752080737182280546197441)
                  ·
                    refine ⟨564060552886710409648081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752080737182280546197441 564060552886710409648081)
                    ·
                      refine ⟨423045414665032807236061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564060552886710409648081 423045414665032807236061)
                      ·
                        rfl

theorem cell23_823878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_823878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823878 prefixEnd_823878 := by exact prefixLift 823878
  have htrace : WordTrace (prefixWord ++ tailWord_823878) baseStart_823878 baseEnd_823878 := by
    simpa [prefixWord, tailWord_823878, baseEnd_823878] using wordTrace_append hprefix tailTrace_823878
  have hstable : (prefixWord ++ tailWord_823878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823878).length < 2 ^ (prefixWord ++ tailWord_823878).sum := by decide
  have hdescent : baseEnd_823878 < baseStart_823878 := by decide
  rcases family_descends (prefixWord ++ tailWord_823878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823886 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_823886 : Nat := 118140960795 + 823886 * 2 ^ 59
def prefixEnd_823886 : Nat := 4983230072969 + 3 ^ 40 * 823886 * 2
def baseEnd_823886 : Nat := 423049522510268775936023

theorem tailTrace_823886 : CollatzResearch.WordTrace tailWord_823886 prefixEnd_823886 423049522510268775936023 := by
  unfold tailWord_823886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756198886651150671441439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20033060728806136914354341 3756198886651150671441439)
  ·
    refine ⟨5634298329976726007162159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3756198886651150671441439 5634298329976726007162159)
    ·
      refine ⟨8451447494965089010743239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5634298329976726007162159 8451447494965089010743239)
      ·
        refine ⟨12677171242447633516114859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8451447494965089010743239 12677171242447633516114859)
        ·
          refine ⟨19015756863671450274172289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12677171242447633516114859 19015756863671450274172289)
          ·
            refine ⟨14261817647753587705629217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19015756863671450274172289 14261817647753587705629217)
            ·
              refine ⟨10696363235815190779221913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14261817647753587705629217 10696363235815190779221913)
              ·
                refine ⟨8022272426861393084416435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10696363235815190779221913 8022272426861393084416435)
                ·
                  refine ⟨12033408640292089626624653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022272426861393084416435 12033408640292089626624653)
                  ·
                    refine ⟨4512528240109533609984245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12033408640292089626624653 4512528240109533609984245)
                    ·
                      refine ⟨423049522510268775936023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4512528240109533609984245 423049522510268775936023)
                      ·
                        rfl

theorem cell23_823886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_823886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823886 prefixEnd_823886 := by exact prefixLift 823886
  have htrace : WordTrace (prefixWord ++ tailWord_823886) baseStart_823886 baseEnd_823886 := by
    simpa [prefixWord, tailWord_823886, baseEnd_823886] using wordTrace_append hprefix tailTrace_823886
  have hstable : (prefixWord ++ tailWord_823886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823886).length < 2 ^ (prefixWord ++ tailWord_823886).sum := by decide
  have hdescent : baseEnd_823886 < baseStart_823886 := by decide
  rcases family_descends (prefixWord ++ tailWord_823886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823896 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_823896 : Nat := 118140960795 + 823896 * 2 ^ 59
def prefixEnd_823896 : Nat := 4983230072969 + 3 ^ 40 * 823896 * 2
def baseEnd_823896 : Nat := 423054657316813736810977

theorem tailTrace_823896 : CollatzResearch.WordTrace tailWord_823896 prefixEnd_823896 423054657316813736810977 := by
  unfold tailWord_823896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15024977911586488539697771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20033303882115318052930361 15024977911586488539697771)
  ·
    refine ⟨22537466867379732809546657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15024977911586488539697771 22537466867379732809546657)
    ·
      refine ⟨16903100150534799607159993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22537466867379732809546657 16903100150534799607159993)
      ·
        refine ⟨12677325112901099705369995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16903100150534799607159993 12677325112901099705369995)
        ·
          refine ⟨19015987669351649558054993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12677325112901099705369995 19015987669351649558054993)
          ·
            refine ⟨14261990752013737168541245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19015987669351649558054993 14261990752013737168541245)
            ·
              refine ⟨5348246532005151438202967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14261990752013737168541245 5348246532005151438202967)
              ·
                refine ⟨8022369798007727157304451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5348246532005151438202967 8022369798007727157304451)
                ·
                  refine ⟨12033554697011590735956677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8022369798007727157304451 12033554697011590735956677)
                  ·
                    refine ⟨2256291505689673262991877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12033554697011590735956677 2256291505689673262991877)
                    ·
                      refine ⟨423054657316813736810977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2256291505689673262991877 423054657316813736810977)
                      ·
                        rfl

theorem cell23_823896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_823896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823896 prefixEnd_823896 := by exact prefixLift 823896
  have htrace : WordTrace (prefixWord ++ tailWord_823896) baseStart_823896 baseEnd_823896 := by
    simpa [prefixWord, tailWord_823896, baseEnd_823896] using wordTrace_append hprefix tailTrace_823896
  have hstable : (prefixWord ++ tailWord_823896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823896).length < 2 ^ (prefixWord ++ tailWord_823896).sum := by decide
  have hdescent : baseEnd_823896 < baseStart_823896 := by decide
  rcases family_descends (prefixWord ++ tailWord_823896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823940 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 5]
def baseStart_823940 : Nat := 118140960795 + 823940 * 2 ^ 59
def prefixEnd_823940 : Nat := 4983230072969 + 3 ^ 40 * 823940 * 2
def baseEnd_823940 : Nat := 47008583385067951628975

theorem tailTrace_823940 : CollatzResearch.WordTrace tailWord_823940 prefixEnd_823940 47008583385067951628975 := by
  unfold tailWord_823940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025780317506786296998637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20034373756675715062664849 15025780317506786296998637)
  ·
    refine ⟨5634667619065044861374489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15025780317506786296998637 5634667619065044861374489)
    ·
      refine ⟨4226000714298783646030867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5634667619065044861374489 4226000714298783646030867)
      ·
        refine ⟨6339001071448175469046301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226000714298783646030867 6339001071448175469046301)
        ·
          refine ⟨2377125401793065800892363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6339001071448175469046301 2377125401793065800892363)
          ·
            refine ⟨3565688102689598701338545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377125401793065800892363 3565688102689598701338545)
            ·
              refine ⟨2674266077017199026003909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565688102689598701338545 2674266077017199026003909)
              ·
                refine ⟨501424889440724817375733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2674266077017199026003909 501424889440724817375733)
                ·
                  refine ⟨47008583385067951628975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 501424889440724817375733 47008583385067951628975)
                  ·
                    rfl

theorem cell23_823940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_823940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823940 prefixEnd_823940 := by exact prefixLift 823940
  have htrace : WordTrace (prefixWord ++ tailWord_823940) baseStart_823940 baseEnd_823940 := by
    simpa [prefixWord, tailWord_823940, baseEnd_823940] using wordTrace_append hprefix tailTrace_823940
  have hstable : (prefixWord ++ tailWord_823940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823940).length < 2 ^ (prefixWord ++ tailWord_823940).sum := by decide
  have hdescent : baseEnd_823940 < baseStart_823940 := by decide
  rcases family_descends (prefixWord ++ tailWord_823940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823973 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_823973 : Nat := 118140960795 + 823973 * 2 ^ 59
def prefixEnd_823973 : Nat := 4983230072969 + 3 ^ 40 * 823973 * 2
def baseEnd_823973 : Nat := 423094195327209935548123

theorem tailTrace_823973 : CollatzResearch.WordTrace tailWord_823973 prefixEnd_823973 423094195327209935548123 := by
  unfold tailWord_823973
  simp only [CollatzResearch.WordTrace]
  refine ⟨30052764243894019229948573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20035176162596012819965715 30052764243894019229948573)
  ·
    refine ⟨11269786591460257211230715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30052764243894019229948573 11269786591460257211230715)
    ·
      refine ⟨16904679887190385816846073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11269786591460257211230715 16904679887190385816846073)
      ·
        refine ⟨12678509915392789362634555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16904679887190385816846073 12678509915392789362634555)
        ·
          refine ⟨19017764873089184043951833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12678509915392789362634555 19017764873089184043951833)
          ·
            refine ⟨14263323654816888032963875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19017764873089184043951833 14263323654816888032963875)
            ·
              refine ⟨21394985482225332049445813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14263323654816888032963875 21394985482225332049445813)
              ·
                refine ⟨2005779888958624879635545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21394985482225332049445813 2005779888958624879635545)
                ·
                  refine ⟨1504334916718968659726659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2005779888958624879635545 1504334916718968659726659)
                  ·
                    refine ⟨2256502375078452989589989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1504334916718968659726659 2256502375078452989589989)
                    ·
                      refine ⟨423094195327209935548123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2256502375078452989589989 423094195327209935548123)
                      ·
                        rfl

theorem cell23_823973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_823973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_823973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_823973 prefixEnd_823973 := by exact prefixLift 823973
  have htrace : WordTrace (prefixWord ++ tailWord_823973) baseStart_823973 baseEnd_823973 := by
    simpa [prefixWord, tailWord_823973, baseEnd_823973] using wordTrace_append hprefix tailTrace_823973
  have hstable : (prefixWord ++ tailWord_823973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823973).length < 2 ^ (prefixWord ++ tailWord_823973).sum := by decide
  have hdescent : baseEnd_823973 < baseStart_823973 := by decide
  rcases family_descends (prefixWord ++ tailWord_823973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824000 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 3, 4]
def baseStart_824000 : Nat := 118140960795 + 824000 * 2 ^ 59
def prefixEnd_824000 : Nat := 4983230072969 + 3 ^ 40 * 824000 * 2
def baseEnd_824000 : Nat := 141036019768293776636833

theorem tailTrace_824000 : CollatzResearch.WordTrace tailWord_824000 prefixEnd_824000 141036019768293776636833 := by
  unfold tailWord_824000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15026874507398101420590727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20035832676530801894120969 15026874507398101420590727)
  ·
    refine ⟨22540311761097152130886091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15026874507398101420590727 22540311761097152130886091)
    ·
      refine ⟨33810467641645728196329137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22540311761097152130886091 33810467641645728196329137)
      ·
        refine ⟨25357850731234296147246853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33810467641645728196329137 25357850731234296147246853)
        ·
          refine ⟨4754597012106430527608785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25357850731234296147246853 4754597012106430527608785)
          ·
            refine ⟨3565947759079822895706589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4754597012106430527608785 3565947759079822895706589)
            ·
              refine ⟨1337230409654933585889971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3565947759079822895706589 1337230409654933585889971)
              ·
                refine ⟨2005845614482400378834957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337230409654933585889971 2005845614482400378834957)
                ·
                  refine ⟨752192105430900142063109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2005845614482400378834957 752192105430900142063109)
                  ·
                    refine ⟨141036019768293776636833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752192105430900142063109 141036019768293776636833)
                    ·
                      rfl

theorem cell23_824000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_824000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824000 prefixEnd_824000 := by exact prefixLift 824000
  have htrace : WordTrace (prefixWord ++ tailWord_824000) baseStart_824000 baseEnd_824000 := by
    simpa [prefixWord, tailWord_824000, baseEnd_824000] using wordTrace_append hprefix tailTrace_824000
  have hstable : (prefixWord ++ tailWord_824000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824000).length < 2 ^ (prefixWord ++ tailWord_824000).sum := by decide
  have hdescent : baseEnd_824000 < baseStart_824000 := by decide
  rcases family_descends (prefixWord ++ tailWord_824000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824016 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_824016 : Nat := 118140960795 + 824016 * 2 ^ 59
def prefixEnd_824016 : Nat := 4983230072969 + 3 ^ 40 * 824016 * 2
def baseEnd_824016 : Nat := 423116274995353267310425

theorem tailTrace_824016 : CollatzResearch.WordTrace tailWord_824016 prefixEnd_824016 423116274995353267310425 := by
  unfold tailWord_824016
  simp only [CollatzResearch.WordTrace]
  refine ⟨15027166291369118786881951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20036221721825491715842601 15027166291369118786881951)
  ·
    refine ⟨22540749437053678180322927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15027166291369118786881951 22540749437053678180322927)
    ·
      refine ⟨33811124155580517270484391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22540749437053678180322927 33811124155580517270484391)
      ·
        refine ⟨50716686233370775905726587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33811124155580517270484391 50716686233370775905726587)
        ·
          refine ⟨76075029350056163858589881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50716686233370775905726587 76075029350056163858589881)
          ·
            refine ⟨57056272012542122893942411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76075029350056163858589881 57056272012542122893942411)
            ·
              refine ⟨85584408018813184340913617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57056272012542122893942411 85584408018813184340913617)
              ·
                refine ⟨64188306014109888255685213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85584408018813184340913617 64188306014109888255685213)
                ·
                  refine ⟨24070614755291208095881955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64188306014109888255685213 24070614755291208095881955)
                  ·
                    refine ⟨36105922132936812143822933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24070614755291208095881955 36105922132936812143822933)
                    ·
                      refine ⟨423116274995353267310425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36105922132936812143822933 423116274995353267310425)
                      ·
                        rfl

theorem cell23_824016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_824016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824016 prefixEnd_824016 := by exact prefixLift 824016
  have htrace : WordTrace (prefixWord ++ tailWord_824016) baseStart_824016 baseEnd_824016 := by
    simpa [prefixWord, tailWord_824016, baseEnd_824016] using wordTrace_append hprefix tailTrace_824016
  have hstable : (prefixWord ++ tailWord_824016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824016).length < 2 ^ (prefixWord ++ tailWord_824016).sum := by decide
  have hdescent : baseEnd_824016 < baseStart_824016 := by decide
  rcases family_descends (prefixWord ++ tailWord_824016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824073 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_824073 : Nat := 118140960795 + 824073 * 2 ^ 59
def prefixEnd_824073 : Nat := 4983230072969 + 3 ^ 40 * 824073 * 2
def baseEnd_824073 : Nat := 141048514464219848099221

theorem tailTrace_824073 : CollatzResearch.WordTrace tailWord_824073 prefixEnd_824073 141048514464219848099221 := by
  unfold tailWord_824073
  simp only [CollatzResearch.WordTrace]
  refine ⟨30056411543531736308588873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20037607695687824205725915 30056411543531736308588873)
  ·
    refine ⟨22542308657648802231441655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30056411543531736308588873 22542308657648802231441655)
    ·
      refine ⟨33813462986473203347162483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22542308657648802231441655 33813462986473203347162483)
      ·
        refine ⟨50720194479709805020743725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33813462986473203347162483 50720194479709805020743725)
        ·
          refine ⟨19020072929891176882778897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50720194479709805020743725 19020072929891176882778897)
          ·
            refine ⟨14265054697418382662084173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19020072929891176882778897 14265054697418382662084173)
            ·
              refine ⟨5349395511531893498281565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14265054697418382662084173 5349395511531893498281565)
              ·
                refine ⟨2006023316824460061855587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5349395511531893498281565 2006023316824460061855587)
                ·
                  refine ⟨3009034975236690092783381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006023316824460061855587 3009034975236690092783381)
                  ·
                    refine ⟨141048514464219848099221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3009034975236690092783381 141048514464219848099221)
                    ·
                      rfl

theorem cell23_824073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_824073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824073 prefixEnd_824073 := by exact prefixLift 824073
  have htrace : WordTrace (prefixWord ++ tailWord_824073) baseStart_824073 baseEnd_824073 := by
    simpa [prefixWord, tailWord_824073, baseEnd_824073] using wordTrace_append hprefix tailTrace_824073
  have hstable : (prefixWord ++ tailWord_824073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824073).length < 2 ^ (prefixWord ++ tailWord_824073).sum := by decide
  have hdescent : baseEnd_824073 < baseStart_824073 := by decide
  rcases family_descends (prefixWord ++ tailWord_824073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824090 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_824090 : Nat := 118140960795 + 824090 * 2 ^ 59
def prefixEnd_824090 : Nat := 4983230072969 + 3 ^ 40 * 824090 * 2
def baseEnd_824090 : Nat := 141051424187928659261695

theorem tailTrace_824090 : CollatzResearch.WordTrace tailWord_824090 prefixEnd_824090 141051424187928659261695 := by
  unfold tailWord_824090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514257896117537052989431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20038021056313432141305149 7514257896117537052989431)
  ·
    refine ⟨11271386844176305579484147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7514257896117537052989431 11271386844176305579484147)
    ·
      refine ⟨16907080266264458369226221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11271386844176305579484147 16907080266264458369226221)
      ·
        refine ⟨6340155099849171888459833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16907080266264458369226221 6340155099849171888459833)
        ·
          refine ⟨4755116324886878916344875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6340155099849171888459833 4755116324886878916344875)
          ·
            refine ⟨7132674487330318374517313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755116324886878916344875 7132674487330318374517313)
            ·
              refine ⟨5349505865497738780887985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7132674487330318374517313 5349505865497738780887985)
              ·
                refine ⟨4012129399123304085665989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5349505865497738780887985 4012129399123304085665989)
                ·
                  refine ⟨752274262335619516062373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4012129399123304085665989 752274262335619516062373)
                  ·
                    refine ⟨141051424187928659261695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752274262335619516062373 141051424187928659261695)
                    ·
                      rfl

theorem cell23_824090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_824090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824090 prefixEnd_824090 := by exact prefixLift 824090
  have htrace : WordTrace (prefixWord ++ tailWord_824090) baseStart_824090 baseEnd_824090 := by
    simpa [prefixWord, tailWord_824090, baseEnd_824090] using wordTrace_append hprefix tailTrace_824090
  have hstable : (prefixWord ++ tailWord_824090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824090).length < 2 ^ (prefixWord ++ tailWord_824090).sum := by decide
  have hdescent : baseEnd_824090 < baseStart_824090 := by decide
  rcases family_descends (prefixWord ++ tailWord_824090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824097 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_824097 : Nat := 118140960795 + 824097 * 2 ^ 59
def prefixEnd_824097 : Nat := 4983230072969 + 3 ^ 40 * 824097 * 2
def baseEnd_824097 : Nat := 423157866928367450397553

theorem tailTrace_824097 : CollatzResearch.WordTrace tailWord_824097 prefixEnd_824097 423157866928367450397553 := by
  unfold tailWord_824097
  simp only [CollatzResearch.WordTrace]
  refine ⟨30057286895444788407462545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20038191263629858938308363 30057286895444788407462545)
  ·
    refine ⟨22542965171583591305596909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30057286895444788407462545 22542965171583591305596909)
    ·
      refine ⟨8453611939343846739598841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22542965171583591305596909 8453611939343846739598841)
      ·
        refine ⟨6340208954507885054699131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8453611939343846739598841 6340208954507885054699131)
        ·
          refine ⟨9510313431761827582048697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340208954507885054699131 9510313431761827582048697)
          ·
            refine ⟨7132735073821370686536523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9510313431761827582048697 7132735073821370686536523)
            ·
              refine ⟨10699102610732056029804785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132735073821370686536523 10699102610732056029804785)
              ·
                refine ⟨8024326958049042022353589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10699102610732056029804785 8024326958049042022353589)
                ·
                  refine ⟨752280652317097689595649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8024326958049042022353589 752280652317097689595649)
                  ·
                    refine ⟨564210489237823267196737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752280652317097689595649 564210489237823267196737)
                    ·
                      refine ⟨423157866928367450397553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564210489237823267196737 423157866928367450397553)
                      ·
                        rfl

theorem cell23_824097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_824097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824097 prefixEnd_824097 := by exact prefixLift 824097
  have htrace : WordTrace (prefixWord ++ tailWord_824097) baseStart_824097 baseEnd_824097 := by
    simpa [prefixWord, tailWord_824097, baseEnd_824097] using wordTrace_append hprefix tailTrace_824097
  have hstable : (prefixWord ++ tailWord_824097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824097).length < 2 ^ (prefixWord ++ tailWord_824097).sum := by decide
  have hdescent : baseEnd_824097 < baseStart_824097 := by decide
  rcases family_descends (prefixWord ++ tailWord_824097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824114 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_824114 : Nat := 118140960795 + 824114 * 2 ^ 59
def prefixEnd_824114 : Nat := 4983230072969 + 3 ^ 40 * 824114 * 2
def baseEnd_824114 : Nat := 423166596099493883884975

theorem tailTrace_824114 : CollatzResearch.WordTrace tailWord_824114 prefixEnd_824114 423166596099493883884975 := by
  unfold tailWord_824114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7514476734095800077707849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20038604624255466873887597 7514476734095800077707849)
  ·
    refine ⟨5635857550571850058280887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7514476734095800077707849 5635857550571850058280887)
    ·
      refine ⟨8453786325857775087421331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5635857550571850058280887 8453786325857775087421331)
      ·
        refine ⟨12680679488786662631131997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8453786325857775087421331 12680679488786662631131997)
        ·
          refine ⟨4755254808294998486674499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12680679488786662631131997 4755254808294998486674499)
          ·
            refine ⟨7132882212442497730011749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755254808294998486674499 7132882212442497730011749)
            ·
              refine ⟨1337415414832968324377203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7132882212442497730011749 1337415414832968324377203)
              ·
                refine ⟨2006123122249452486565805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337415414832968324377203 2006123122249452486565805)
                ·
                  refine ⟨752296170843544682462177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2006123122249452486565805 752296170843544682462177)
                  ·
                    refine ⟨564222128132658511846633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752296170843544682462177 564222128132658511846633)
                    ·
                      refine ⟨423166596099493883884975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564222128132658511846633 423166596099493883884975)
                      ·
                        rfl

theorem cell23_824114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_824114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824114 prefixEnd_824114 := by exact prefixLift 824114
  have htrace : WordTrace (prefixWord ++ tailWord_824114) baseStart_824114 baseEnd_824114 := by
    simpa [prefixWord, tailWord_824114, baseEnd_824114] using wordTrace_append hprefix tailTrace_824114
  have hstable : (prefixWord ++ tailWord_824114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824114).length < 2 ^ (prefixWord ++ tailWord_824114).sum := by decide
  have hdescent : baseEnd_824114 < baseStart_824114 := by decide
  rcases family_descends (prefixWord ++ tailWord_824114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824127 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 4]
def baseStart_824127 : Nat := 118140960795 + 824127 * 2 ^ 59
def prefixEnd_824127 : Nat := 4983230072969 + 3 ^ 40 * 824127 * 2
def baseEnd_824127 : Nat := 423173271348002333022415

theorem tailTrace_824127 : CollatzResearch.WordTrace tailWord_824127 prefixEnd_824127 423173271348002333022415 := by
  unfold tailWord_824127
  simp only [CollatzResearch.WordTrace]
  refine ⟨30058381085336103531054635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20038920723557402354036423 30058381085336103531054635)
  ·
    refine ⟨45087571628004155296581953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30058381085336103531054635 45087571628004155296581953)
    ·
      refine ⟨33815678721003116472436465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45087571628004155296581953 33815678721003116472436465)
      ·
        refine ⟨25361759040752337354327349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33815678721003116472436465 25361759040752337354327349)
        ·
          refine ⟨2377664910070531626968189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25361759040752337354327349 2377664910070531626968189)
          ·
            refine ⟨891624341276449360113071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2377664910070531626968189 891624341276449360113071)
            ·
              refine ⟨1337436511914674040169607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891624341276449360113071 1337436511914674040169607)
              ·
                refine ⟨2006154767872011060254411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337436511914674040169607 2006154767872011060254411)
                ·
                  refine ⟨3009232151808016590381617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006154767872011060254411 3009232151808016590381617)
                  ·
                    refine ⟨2256924113856012442786213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3009232151808016590381617 2256924113856012442786213)
                    ·
                      refine ⟨423173271348002333022415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2256924113856012442786213 423173271348002333022415)
                      ·
                        rfl

theorem cell23_824127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_824127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824127 prefixEnd_824127 := by exact prefixLift 824127
  have htrace : WordTrace (prefixWord ++ tailWord_824127) baseStart_824127 baseEnd_824127 := by
    simpa [prefixWord, tailWord_824127, baseEnd_824127] using wordTrace_append hprefix tailTrace_824127
  have hstable : (prefixWord ++ tailWord_824127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824127).length < 2 ^ (prefixWord ++ tailWord_824127).sum := by decide
  have hdescent : baseEnd_824127 < baseStart_824127 := by decide
  rcases family_descends (prefixWord ++ tailWord_824127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824181 : List Nat := [1, 3, 4, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_824181 : Nat := 118140960795 + 824181 * 2 ^ 59
def prefixEnd_824181 : Nat := 4983230072969 + 3 ^ 40 * 824181 * 2
def baseEnd_824181 : Nat := 423200999303345121747167

theorem tailTrace_824181 : CollatzResearch.WordTrace tailWord_824181 prefixEnd_824181 423200999303345121747167 := by
  unfold tailWord_824181
  simp only [CollatzResearch.WordTrace]
  refine ⟨30060350627140470753520397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20040233751426980502346931 30060350627140470753520397)
  ·
    refine ⟨11272631485177676532570149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30060350627140470753520397 11272631485177676532570149)
    ·
      refine ⟨2113618403470814349856903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11272631485177676532570149 2113618403470814349856903)
      ·
        refine ⟨3170427605206221524785355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2113618403470814349856903 3170427605206221524785355)
        ·
          refine ⟨4755641407809332287178033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3170427605206221524785355 4755641407809332287178033)
          ·
            refine ⟨3566731055856999215383525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4755641407809332287178033 3566731055856999215383525)
            ·
              refine ⟨668762072973187352884411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3566731055856999215383525 668762072973187352884411)
              ·
                refine ⟨1003143109459781029326617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668762072973187352884411 1003143109459781029326617)
                ·
                  refine ⟨752357332094835771994963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003143109459781029326617 752357332094835771994963)
                  ·
                    refine ⟨1128535998142253657992445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 752357332094835771994963 1128535998142253657992445)
                    ·
                      refine ⟨423200999303345121747167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1128535998142253657992445 423200999303345121747167)
                      ·
                        rfl

theorem cell23_824181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_824181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824181 prefixEnd_824181 := by exact prefixLift 824181
  have htrace : WordTrace (prefixWord ++ tailWord_824181) baseStart_824181 baseEnd_824181 := by
    simpa [prefixWord, tailWord_824181, baseEnd_824181] using wordTrace_append hprefix tailTrace_824181
  have hstable : (prefixWord ++ tailWord_824181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824181).length < 2 ^ (prefixWord ++ tailWord_824181).sum := by decide
  have hdescent : baseEnd_824181 < baseStart_824181 := by decide
  rcases family_descends (prefixWord ++ tailWord_824181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824183 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_824183 : Nat := 118140960795 + 824183 * 2 ^ 59
def prefixEnd_824183 : Nat := 4983230072969 + 3 ^ 40 * 824183 * 2
def baseEnd_824183 : Nat := 423202026264654113922157

theorem tailTrace_824183 : CollatzResearch.WordTrace tailWord_824183 prefixEnd_824183 423202026264654113922157 := by
  unfold tailWord_824183
  simp only [CollatzResearch.WordTrace]
  refine ⟨30060423573133225095093203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20040282382088816730062135 30060423573133225095093203)
  ·
    refine ⟨45090635359699837642639805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30060423573133225095093203 45090635359699837642639805)
    ·
      refine ⟨16908988259887439115989927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45090635359699837642639805 16908988259887439115989927)
      ·
        refine ⟨25363482389831158673984891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16908988259887439115989927 25363482389831158673984891)
        ·
          refine ⟨38045223584746738010977337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25363482389831158673984891 38045223584746738010977337)
          ·
            refine ⟨28533917688560053508233003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38045223584746738010977337 28533917688560053508233003)
            ·
              refine ⟨42800876532840080262349505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28533917688560053508233003 42800876532840080262349505)
              ·
                refine ⟨32100657399630060196762129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42800876532840080262349505 32100657399630060196762129)
                ·
                  refine ⟨24075493049722545147571597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32100657399630060196762129 24075493049722545147571597)
                  ·
                    refine ⟨9028309893645954430339349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24075493049722545147571597 9028309893645954430339349)
                    ·
                      refine ⟨423202026264654113922157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9028309893645954430339349 423202026264654113922157)
                      ·
                        rfl

theorem cell23_824183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_824183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824183 prefixEnd_824183 := by exact prefixLift 824183
  have htrace : WordTrace (prefixWord ++ tailWord_824183) baseStart_824183 baseEnd_824183 := by
    simpa [prefixWord, tailWord_824183, baseEnd_824183] using wordTrace_append hprefix tailTrace_824183
  have hstable : (prefixWord ++ tailWord_824183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824183).length < 2 ^ (prefixWord ++ tailWord_824183).sum := by decide
  have hdescent : baseEnd_824183 < baseStart_824183 := by decide
  rcases family_descends (prefixWord ++ tailWord_824183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824221 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_824221 : Nat := 118140960795 + 824221 * 2 ^ 59
def prefixEnd_824221 : Nat := 4983230072969 + 3 ^ 40 * 824221 * 2
def baseEnd_824221 : Nat := 423221538529524965246983

theorem tailTrace_824221 : CollatzResearch.WordTrace tailWord_824221 prefixEnd_824221 423221538529524965246983 := by
  unfold tailWord_824221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30061809546995557584976517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20041206364663705056651011 30061809546995557584976517)
  ·
    refine ⟨5636589290061667047183097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30061809546995557584976517 5636589290061667047183097)
    ·
      refine ⟨4227441967546250285387323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5636589290061667047183097 4227441967546250285387323)
      ·
        refine ⟨6341162951319375428080985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227441967546250285387323 6341162951319375428080985)
        ·
          refine ⟨4755872213489531571060739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6341162951319375428080985 4755872213489531571060739)
          ·
            refine ⟨7133808320234297356591109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755872213489531571060739 7133808320234297356591109)
            ·
              refine ⟨1337589060043930754360833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7133808320234297356591109 1337589060043930754360833)
              ·
                refine ⟨1003191795032948065770625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337589060043930754360833 1003191795032948065770625)
                ·
                  refine ⟨752393846274711049327969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003191795032948065770625 752393846274711049327969)
                  ·
                    refine ⟨564295384706033286995977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752393846274711049327969 564295384706033286995977)
                    ·
                      refine ⟨423221538529524965246983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564295384706033286995977 423221538529524965246983)
                      ·
                        rfl

theorem cell23_824221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_824221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824221 prefixEnd_824221 := by exact prefixLift 824221
  have htrace : WordTrace (prefixWord ++ tailWord_824221) baseStart_824221 baseEnd_824221 := by
    simpa [prefixWord, tailWord_824221, baseEnd_824221] using wordTrace_append hprefix tailTrace_824221
  have hstable : (prefixWord ++ tailWord_824221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824221).length < 2 ^ (prefixWord ++ tailWord_824221).sum := by decide
  have hdescent : baseEnd_824221 < baseStart_824221 := by decide
  rcases family_descends (prefixWord ++ tailWord_824221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824244 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 7]
def baseStart_824244 : Nat := 118140960795 + 824244 * 2 ^ 59
def prefixEnd_824244 : Nat := 4983230072969 + 3 ^ 40 * 824244 * 2
def baseEnd_824244 : Nat := 47025927620508708362153

theorem tailTrace_824244 : CollatzResearch.WordTrace tailWord_824244 prefixEnd_824244 47025927620508708362153 := by
  unfold tailWord_824244
  simp only [CollatzResearch.WordTrace]
  refine ⟨15031324212956116256531893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20041765617274821675375857 15031324212956116256531893)
  ·
    refine ⟨1409186644964635899049865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15031324212956116256531893 1409186644964635899049865)
    ·
      refine ⟨1056889983723476924287399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1409186644964635899049865 1056889983723476924287399)
      ·
        refine ⟨1585334975585215386431099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056889983723476924287399 1585334975585215386431099)
        ·
          refine ⟨2378002463377823079646649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585334975585215386431099 2378002463377823079646649)
          ·
            refine ⟨1783501847533367309734987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2378002463377823079646649 1783501847533367309734987)
            ·
              refine ⟨2675252771300050964602481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783501847533367309734987 2675252771300050964602481)
              ·
                refine ⟨2006439578475038223451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675252771300050964602481 2006439578475038223451861)
                ·
                  refine ⟨47025927620508708362153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2006439578475038223451861 47025927620508708362153)
                  ·
                    rfl

theorem cell23_824244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_824244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824244 prefixEnd_824244 := by exact prefixLift 824244
  have htrace : WordTrace (prefixWord ++ tailWord_824244) baseStart_824244 baseEnd_824244 := by
    simpa [prefixWord, tailWord_824244, baseEnd_824244] using wordTrace_append hprefix tailTrace_824244
  have hstable : (prefixWord ++ tailWord_824244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824244).length < 2 ^ (prefixWord ++ tailWord_824244).sum := by decide
  have hdescent : baseEnd_824244 < baseStart_824244 := by decide
  rcases family_descends (prefixWord ++ tailWord_824244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824321 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 1, 4]
def baseStart_824321 : Nat := 118140960795 + 824321 * 2 ^ 59
def prefixEnd_824321 : Nat := 4983230072969 + 3 ^ 40 * 824321 * 2
def baseEnd_824321 : Nat := 141090962198324857998841

theorem tailTrace_824321 : CollatzResearch.WordTrace tailWord_824321 prefixEnd_824321 141090962198324857998841 := by
  unfold tailWord_824321
  simp only [CollatzResearch.WordTrace]
  refine ⟨30065456846633274663616817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20043637897755516442411211 30065456846633274663616817)
  ·
    refine ⟨22549092634974955997712613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30065456846633274663616817 22549092634974955997712613)
    ·
      refine ⟨4227954869057804249571115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22549092634974955997712613 4227954869057804249571115)
      ·
        refine ⟨6341932303586706374356673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227954869057804249571115 6341932303586706374356673)
        ·
          refine ⟨4756449227690029780767505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6341932303586706374356673 4756449227690029780767505)
          ·
            refine ⟨3567336920767522335575629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4756449227690029780767505 3567336920767522335575629)
            ·
              refine ⟨1337751345287820875840861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3567336920767522335575629 1337751345287820875840861)
              ·
                refine ⟨501656754482932828440323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1337751345287820875840861 501656754482932828440323)
                ·
                  refine ⟨752485131724399242660485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501656754482932828440323 752485131724399242660485)
                  ·
                    refine ⟨141090962198324857998841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752485131724399242660485 141090962198324857998841)
                    ·
                      rfl

theorem cell23_824321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_824321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824321 prefixEnd_824321 := by exact prefixLift 824321
  have htrace : WordTrace (prefixWord ++ tailWord_824321) baseStart_824321 baseEnd_824321 := by
    simpa [prefixWord, tailWord_824321, baseEnd_824321] using wordTrace_append hprefix tailTrace_824321
  have hstable : (prefixWord ++ tailWord_824321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824321).length < 2 ^ (prefixWord ++ tailWord_824321).sum := by decide
  have hdescent : baseEnd_824321 < baseStart_824321 := by decide
  rcases family_descends (prefixWord ++ tailWord_824321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824377 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_824377 : Nat := 118140960795 + 824377 * 2 ^ 59
def prefixEnd_824377 : Nat := 4983230072969 + 3 ^ 40 * 824377 * 2
def baseEnd_824377 : Nat := 141100547170542118298755

theorem tailTrace_824377 : CollatzResearch.WordTrace tailWord_824377 prefixEnd_824377 141100547170542118298755 := by
  unfold tailWord_824377
  simp only [CollatzResearch.WordTrace]
  refine ⟨30067499334430396227655385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20044999556286930818436923 30067499334430396227655385)
  ·
    refine ⟨22550624500822797170741539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30067499334430396227655385 22550624500822797170741539)
    ·
      refine ⟨33825936751234195756112309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22550624500822797170741539 33825936751234195756112309)
      ·
        refine ⟨3171181570428205852135529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33825936751234195756112309 3171181570428205852135529)
        ·
          refine ⟨2378386177821154389101647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3171181570428205852135529 2378386177821154389101647)
          ·
            refine ⟨3567579266731731583652471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378386177821154389101647 3567579266731731583652471)
            ·
              refine ⟨5351368900097597375478707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567579266731731583652471 5351368900097597375478707)
              ·
                refine ⟨8027053350146396063218061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351368900097597375478707 8027053350146396063218061)
                ·
                  refine ⟨3010145006304898523706773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8027053350146396063218061 3010145006304898523706773)
                  ·
                    refine ⟨141100547170542118298755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3010145006304898523706773 141100547170542118298755)
                    ·
                      rfl

theorem cell23_824377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_824377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824377 prefixEnd_824377 := by exact prefixLift 824377
  have htrace : WordTrace (prefixWord ++ tailWord_824377) baseStart_824377 baseEnd_824377 := by
    simpa [prefixWord, tailWord_824377, baseEnd_824377] using wordTrace_append hprefix tailTrace_824377
  have hstable : (prefixWord ++ tailWord_824377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824377).length < 2 ^ (prefixWord ++ tailWord_824377).sum := by decide
  have hdescent : baseEnd_824377 < baseStart_824377 := by decide
  rcases family_descends (prefixWord ++ tailWord_824377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824381 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_824381 : Nat := 118140960795 + 824381 * 2 ^ 59
def prefixEnd_824381 : Nat := 4983230072969 + 3 ^ 40 * 824381 * 2
def baseEnd_824381 : Nat := 141101231811414779748749

theorem tailTrace_824381 : CollatzResearch.WordTrace tailWord_824381 prefixEnd_824381 141101231811414779748749 := by
  unfold tailWord_824381
  simp only [CollatzResearch.WordTrace]
  refine ⟨30067645226415904910800997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20045096817610603273867331 30067645226415904910800997)
  ·
    refine ⟨5637683479952982170775187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30067645226415904910800997 5637683479952982170775187)
    ·
      refine ⟨8456525219929473256162781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5637683479952982170775187 8456525219929473256162781)
      ·
        refine ⟨3171196957473552471061043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8456525219929473256162781 3171196957473552471061043)
        ·
          refine ⟨4756795436210328706591565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171196957473552471061043 4756795436210328706591565)
          ·
            refine ⟨1783798288578873264971837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4756795436210328706591565 1783798288578873264971837)
            ·
              refine ⟨668924358217077474364439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1783798288578873264971837 668924358217077474364439)
              ·
                refine ⟨1003386537325616211546659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668924358217077474364439 1003386537325616211546659)
                ·
                  refine ⟨1505079805988424317319989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003386537325616211546659 1505079805988424317319989)
                  ·
                    refine ⟨141101231811414779748749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1505079805988424317319989 141101231811414779748749)
                    ·
                      rfl

theorem cell23_824381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_824381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824381 prefixEnd_824381 := by exact prefixLift 824381
  have htrace : WordTrace (prefixWord ++ tailWord_824381) baseStart_824381 baseEnd_824381 := by
    simpa [prefixWord, tailWord_824381, baseEnd_824381] using wordTrace_append hprefix tailTrace_824381
  have hstable : (prefixWord ++ tailWord_824381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824381).length < 2 ^ (prefixWord ++ tailWord_824381).sum := by decide
  have hdescent : baseEnd_824381 < baseStart_824381 := by decide
  rcases family_descends (prefixWord ++ tailWord_824381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824394 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_824394 : Nat := 118140960795 + 824394 * 2 ^ 59
def prefixEnd_824394 : Nat := 4983230072969 + 3 ^ 40 * 824394 * 2
def baseEnd_824394 : Nat := 141103456894250929461229

theorem tailTrace_824394 : CollatzResearch.WordTrace tailWord_824394 prefixEnd_824394 141103456894250929461229 := by
  unfold tailWord_824394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517029843842202032756059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20045412916912538754016157 7517029843842202032756059)
  ·
    refine ⟨11275544765763303049134089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7517029843842202032756059 11275544765763303049134089)
    ·
      refine ⟨8456658574322477286850567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11275544765763303049134089 8456658574322477286850567)
      ·
        refine ⟨12684987861483715930275851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456658574322477286850567 12684987861483715930275851)
        ·
          refine ⟨19027481792225573895413777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12684987861483715930275851 19027481792225573895413777)
          ·
            refine ⟨14270611344169180421560333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19027481792225573895413777 14270611344169180421560333)
            ·
              refine ⟨5351479254063442658085125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14270611344169180421560333 5351479254063442658085125)
              ·
                refine ⟨1003402360136895498390961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5351479254063442658085125 1003402360136895498390961)
                ·
                  refine ⟨752551770102671623793221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003402360136895498390961 752551770102671623793221)
                  ·
                    refine ⟨141103456894250929461229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752551770102671623793221 141103456894250929461229)
                    ·
                      rfl

theorem cell23_824394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_824394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824394 prefixEnd_824394 := by exact prefixLift 824394
  have htrace : WordTrace (prefixWord ++ tailWord_824394) baseStart_824394 baseEnd_824394 := by
    simpa [prefixWord, tailWord_824394, baseEnd_824394] using wordTrace_append hprefix tailTrace_824394
  have hstable : (prefixWord ++ tailWord_824394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824394).length < 2 ^ (prefixWord ++ tailWord_824394).sum := by decide
  have hdescent : baseEnd_824394 < baseStart_824394 := by decide
  rcases family_descends (prefixWord ++ tailWord_824394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824404 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_824404 : Nat := 118140960795 + 824404 * 2 ^ 59
def prefixEnd_824404 : Nat := 4983230072969 + 3 ^ 40 * 824404 * 2
def baseEnd_824404 : Nat := 423315505489297749258641

theorem tailTrace_824404 : CollatzResearch.WordTrace tailWord_824404 prefixEnd_824404 423315505489297749258641 := by
  unfold tailWord_824404
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034242052666289919444133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20045656070221719892592177 15034242052666289919444133)
  ·
    refine ⟨2818920384874929359895775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15034242052666289919444133 2818920384874929359895775)
    ·
      refine ⟨4228380577312394039843663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818920384874929359895775 4228380577312394039843663)
      ·
        refine ⟨6342570865968591059765495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4228380577312394039843663 6342570865968591059765495)
        ·
          refine ⟨9513856298952886589648243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6342570865968591059765495 9513856298952886589648243)
          ·
            refine ⟨14270784448429329884472365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9513856298952886589648243 14270784448429329884472365)
            ·
              refine ⟨5351544168160998706677137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14270784448429329884472365 5351544168160998706677137)
              ·
                refine ⟨4013658126120749030007853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351544168160998706677137 4013658126120749030007853)
                ·
                  refine ⟨1505121797295280886252945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4013658126120749030007853 1505121797295280886252945)
                  ·
                    refine ⟨1128841347971460664689709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1505121797295280886252945 1128841347971460664689709)
                    ·
                      refine ⟨423315505489297749258641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1128841347971460664689709 423315505489297749258641)
                      ·
                        rfl

theorem cell23_824404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_824404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824404 prefixEnd_824404 := by exact prefixLift 824404
  have htrace : WordTrace (prefixWord ++ tailWord_824404) baseStart_824404 baseEnd_824404 := by
    simpa [prefixWord, tailWord_824404, baseEnd_824404] using wordTrace_append hprefix tailTrace_824404
  have hstable : (prefixWord ++ tailWord_824404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824404).length < 2 ^ (prefixWord ++ tailWord_824404).sum := by decide
  have hdescent : baseEnd_824404 < baseStart_824404 := by decide
  rcases family_descends (prefixWord ++ tailWord_824404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824418 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_824418 : Nat := 118140960795 + 824418 * 2 ^ 59
def prefixEnd_824418 : Nat := 4983230072969 + 3 ^ 40 * 824418 * 2
def baseEnd_824418 : Nat := 423322694218460694483577

theorem tailTrace_824418 : CollatzResearch.WordTrace tailWord_824418 prefixEnd_824418 423322694218460694483577 := by
  unfold tailWord_824418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517248681820465057474477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20045996484854573486598605 7517248681820465057474477)
  ·
    refine ⟨2818968255682674396552929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7517248681820465057474477 2818968255682674396552929)
    ·
      refine ⟨2114226191762005797414697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2818968255682674396552929 2114226191762005797414697)
      ·
        refine ⟨1585669643821504348061023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2114226191762005797414697 1585669643821504348061023)
        ·
          refine ⟨2378504465732256522091535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585669643821504348061023 2378504465732256522091535)
          ·
            refine ⟨3567756698598384783137303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378504465732256522091535 3567756698598384783137303)
            ·
              refine ⟨5351635047897577174705955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3567756698598384783137303 5351635047897577174705955)
              ·
                refine ⟨8027452571846365762058933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351635047897577174705955 8027452571846365762058933)
                ·
                  refine ⟨752573678610596790193025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8027452571846365762058933 752573678610596790193025)
                  ·
                    refine ⟨564430258957947592644769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752573678610596790193025 564430258957947592644769)
                    ·
                      refine ⟨423322694218460694483577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564430258957947592644769 423322694218460694483577)
                      ·
                        rfl

theorem cell23_824418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_824418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824418 prefixEnd_824418 := by exact prefixLift 824418
  have htrace : WordTrace (prefixWord ++ tailWord_824418) baseStart_824418 baseEnd_824418 := by
    simpa [prefixWord, tailWord_824418, baseEnd_824418] using wordTrace_append hprefix tailTrace_824418
  have hstable : (prefixWord ++ tailWord_824418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824418).length < 2 ^ (prefixWord ++ tailWord_824418).sum := by decide
  have hdescent : baseEnd_824418 < baseStart_824418 := by decide
  rcases family_descends (prefixWord ++ tailWord_824418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824434 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_824434 : Nat := 118140960795 + 824434 * 2 ^ 59
def prefixEnd_824434 : Nat := 4983230072969 + 3 ^ 40 * 824434 * 2
def baseEnd_824434 : Nat := 423330909908932631883503

theorem tailTrace_824434 : CollatzResearch.WordTrace tailWord_824434 prefixEnd_824434 423330909908932631883503 := by
  unfold tailWord_824434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517394573805973740620089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20046385530149263308320237 7517394573805973740620089)
  ·
    refine ⟨5638045930354480305465067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7517394573805973740620089 5638045930354480305465067)
    ·
      refine ⟨8457068895531720458197601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638045930354480305465067 8457068895531720458197601)
      ·
        refine ⟨6342801671648790343648201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8457068895531720458197601 6342801671648790343648201)
        ·
          refine ⟨4757101253736592757736151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6342801671648790343648201 4757101253736592757736151)
          ·
            refine ⟨7135651880604889136604227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757101253736592757736151 7135651880604889136604227)
            ·
              refine ⟨10703477820907333704906341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135651880604889136604227 10703477820907333704906341)
              ·
                refine ⟨2006902091420125069669939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10703477820907333704906341 2006902091420125069669939)
                ·
                  refine ⟨3010353137130187604504909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2006902091420125069669939 3010353137130187604504909)
                  ·
                    refine ⟨1128882426423820351689341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3010353137130187604504909 1128882426423820351689341)
                    ·
                      refine ⟨423330909908932631883503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1128882426423820351689341 423330909908932631883503)
                      ·
                        rfl

theorem cell23_824434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_824434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824434 prefixEnd_824434 := by exact prefixLift 824434
  have htrace : WordTrace (prefixWord ++ tailWord_824434) baseStart_824434 baseEnd_824434 := by
    simpa [prefixWord, tailWord_824434, baseEnd_824434] using wordTrace_append hprefix tailTrace_824434
  have hstable : (prefixWord ++ tailWord_824434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824434).length < 2 ^ (prefixWord ++ tailWord_824434).sum := by decide
  have hdescent : baseEnd_824434 < baseStart_824434 := by decide
  rcases family_descends (prefixWord ++ tailWord_824434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824467 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 2, 6]
def baseStart_824467 : Nat := 118140960795 + 824467 * 2 ^ 59
def prefixEnd_824467 : Nat := 4983230072969 + 3 ^ 40 * 824467 * 2
def baseEnd_824467 : Nat := 141115951590177000923617

theorem tailTrace_824467 : CollatzResearch.WordTrace tailWord_824467 prefixEnd_824467 141115951590177000923617 := by
  unfold tailWord_824467
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070781904104341598431655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20047187936069561065621103 30070781904104341598431655)
  ·
    refine ⟨45106172856156512397647483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30070781904104341598431655 45106172856156512397647483)
    ·
      refine ⟨67659259284234768596471225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45106172856156512397647483 67659259284234768596471225)
      ·
        refine ⟨50744444463176076447353419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67659259284234768596471225 50744444463176076447353419)
        ·
          refine ⟨76116666694764114671030129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50744444463176076447353419 76116666694764114671030129)
          ·
            refine ⟨57087500021073086003272597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76116666694764114671030129 57087500021073086003272597)
            ·
              refine ⟨2675976563487800906403403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57087500021073086003272597 2675976563487800906403403)
              ·
                refine ⟨4013964845231701359605105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2675976563487800906403403 4013964845231701359605105)
                ·
                  refine ⟨3010473633923776019703829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4013964845231701359605105 3010473633923776019703829)
                  ·
                    refine ⟨141115951590177000923617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3010473633923776019703829 141115951590177000923617)
                    ·
                      rfl

theorem cell23_824467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 6].length) (baseStart_824467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824467 prefixEnd_824467 := by exact prefixLift 824467
  have htrace : WordTrace (prefixWord ++ tailWord_824467) baseStart_824467 baseEnd_824467 := by
    simpa [prefixWord, tailWord_824467, baseEnd_824467] using wordTrace_append hprefix tailTrace_824467
  have hstable : (prefixWord ++ tailWord_824467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824467).length < 2 ^ (prefixWord ++ tailWord_824467).sum := by decide
  have hdescent : baseEnd_824467 < baseStart_824467 := by decide
  rcases family_descends (prefixWord ++ tailWord_824467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824508 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_824508 : Nat := 118140960795 + 824508 * 2 ^ 59
def prefixEnd_824508 : Nat := 4983230072969 + 3 ^ 40 * 824508 * 2
def baseEnd_824508 : Nat := 423368907477365342358163

theorem tailTrace_824508 : CollatzResearch.WordTrace tailWord_824508 prefixEnd_824508 423368907477365342358163 := by
  unfold tailWord_824508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15036138648477902800337089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20048184864637203733782785 15036138648477902800337089)
  ·
    refine ⟨11277103986358427100252817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15036138648477902800337089 11277103986358427100252817)
    ·
      refine ⟨8457827989768820325189613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11277103986358427100252817 8457827989768820325189613)
      ·
        refine ⟨3171685496163307621946105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8457827989768820325189613 3171685496163307621946105)
        ·
          refine ⟨2378764122122480716459579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3171685496163307621946105 2378764122122480716459579)
          ·
            refine ⟨3568146183183721074689369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378764122122480716459579 3568146183183721074689369)
            ·
              refine ⟨2676109637387790806017027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568146183183721074689369 2676109637387790806017027)
              ·
                refine ⟨4014164456081686209025541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676109637387790806017027 4014164456081686209025541)
                ·
                  refine ⟨752655835515316164192289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4014164456081686209025541 752655835515316164192289)
                  ·
                    refine ⟨564491876636487123144217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 752655835515316164192289 564491876636487123144217)
                    ·
                      refine ⟨423368907477365342358163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564491876636487123144217 423368907477365342358163)
                      ·
                        rfl

theorem cell23_824508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_824508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824508 prefixEnd_824508 := by exact prefixLift 824508
  have htrace : WordTrace (prefixWord ++ tailWord_824508) baseStart_824508 baseEnd_824508 := by
    simpa [prefixWord, tailWord_824508, baseEnd_824508] using wordTrace_append hprefix tailTrace_824508
  have hstable : (prefixWord ++ tailWord_824508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824508).length < 2 ^ (prefixWord ++ tailWord_824508).sum := by decide
  have hdescent : baseEnd_824508 < baseStart_824508 := by decide
  rcases family_descends (prefixWord ++ tailWord_824508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824527 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 1, 7]
def baseStart_824527 : Nat := 118140960795 + 824527 * 2 ^ 59
def prefixEnd_824527 : Nat := 4983230072969 + 3 ^ 40 * 824527 * 2
def baseEnd_824527 : Nat := 141126221203266922673525

theorem tailTrace_824527 : CollatzResearch.WordTrace tailWord_824527 prefixEnd_824527 141126221203266922673525 := by
  unfold tailWord_824527
  simp only [CollatzResearch.WordTrace]
  refine ⟨30072970283886971845615835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20048646855924647897077223 30072970283886971845615835)
  ·
    refine ⟨45109455425830457768423753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30072970283886971845615835 45109455425830457768423753)
    ·
      refine ⟨33832091569372843326317815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45109455425830457768423753 33832091569372843326317815)
      ·
        refine ⟨50748137354059264989476723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33832091569372843326317815 50748137354059264989476723)
        ·
          refine ⟨76122206031088897484215085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50748137354059264989476723 76122206031088897484215085)
          ·
            refine ⟨28545827261658336556580657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76122206031088897484215085 28545827261658336556580657)
            ·
              refine ⟨21409370446243752417435493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28545827261658336556580657 21409370446243752417435493)
              ·
                refine ⟨4014256958670703578269155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21409370446243752417435493 4014256958670703578269155)
                ·
                  refine ⟨6021385438006055367403733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014256958670703578269155 6021385438006055367403733)
                  ·
                    refine ⟨141126221203266922673525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6021385438006055367403733 141126221203266922673525)
                    ·
                      rfl

theorem cell23_824527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_824527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824527 prefixEnd_824527 := by exact prefixLift 824527
  have htrace : WordTrace (prefixWord ++ tailWord_824527) baseStart_824527 baseEnd_824527 := by
    simpa [prefixWord, tailWord_824527, baseEnd_824527] using wordTrace_append hprefix tailTrace_824527
  have hstable : (prefixWord ++ tailWord_824527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824527).length < 2 ^ (prefixWord ++ tailWord_824527).sum := by decide
  have hdescent : baseEnd_824527 < baseStart_824527 := by decide
  rcases family_descends (prefixWord ++ tailWord_824527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824537 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_824537 : Nat := 118140960795 + 824537 * 2 ^ 59
def prefixEnd_824537 : Nat := 4983230072969 + 3 ^ 40 * 824537 * 2
def baseEnd_824537 : Nat := 423383798416345728895529

theorem tailTrace_824537 : CollatzResearch.WordTrace tailWord_824537 prefixEnd_824537 423383798416345728895529 := by
  unfold tailWord_824537
  simp only [CollatzResearch.WordTrace]
  refine ⟨30073335013850743553479865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20048890009233829035653243 30073335013850743553479865)
  ·
    refine ⟨22555001260388057665109899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30073335013850743553479865 22555001260388057665109899)
    ·
      refine ⟨33832501890582086497664849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22555001260388057665109899 33832501890582086497664849)
      ·
        refine ⟨25374376417936564873248637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33832501890582086497664849 25374376417936564873248637)
        ·
          refine ⟨9515391156726211827468239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25374376417936564873248637 9515391156726211827468239)
          ·
            refine ⟨14273086735089317741202359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9515391156726211827468239 14273086735089317741202359)
            ·
              refine ⟨21409630102633976611803539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14273086735089317741202359 21409630102633976611803539)
              ·
                refine ⟨32114445153950964917705309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21409630102633976611803539 32114445153950964917705309)
                ·
                  refine ⟨12042916932731611844139491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32114445153950964917705309 12042916932731611844139491)
                  ·
                    refine ⟨18064375399097417766209237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12042916932731611844139491 18064375399097417766209237)
                    ·
                      refine ⟨423383798416345728895529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18064375399097417766209237 423383798416345728895529)
                      ·
                        rfl

theorem cell23_824537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_824537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824537 prefixEnd_824537 := by exact prefixLift 824537
  have htrace : WordTrace (prefixWord ++ tailWord_824537) baseStart_824537 baseEnd_824537 := by
    simpa [prefixWord, tailWord_824537, baseEnd_824537] using wordTrace_append hprefix tailTrace_824537
  have hstable : (prefixWord ++ tailWord_824537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824537).length < 2 ^ (prefixWord ++ tailWord_824537).sum := by decide
  have hdescent : baseEnd_824537 < baseStart_824537 := by decide
  rcases family_descends (prefixWord ++ tailWord_824537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824544 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_824544 : Nat := 118140960795 + 824544 * 2 ^ 59
def prefixEnd_824544 : Nat := 4983230072969 + 3 ^ 40 * 824544 * 2
def baseEnd_824544 : Nat := 141129130926975733835999

theorem tailTrace_824544 : CollatzResearch.WordTrace tailWord_824544 prefixEnd_824544 141129130926975733835999 := by
  unfold tailWord_824544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15036795162412691874492343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20049060216550255832656457 15036795162412691874492343)
  ·
    refine ⟨22555192743619037811738515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15036795162412691874492343 22555192743619037811738515)
    ·
      refine ⟨33832789115428556717607773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22555192743619037811738515 33832789115428556717607773)
      ·
        refine ⟨12687295918285708769102915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33832789115428556717607773 12687295918285708769102915)
        ·
          refine ⟨19030943877428563153654373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12687295918285708769102915 19030943877428563153654373)
          ·
            refine ⟨3568301977017855591310195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19030943877428563153654373 3568301977017855591310195)
            ·
              refine ⟨5352452965526783386965293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568301977017855591310195 5352452965526783386965293)
              ·
                refine ⟨2007169862072543770111985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5352452965526783386965293 2007169862072543770111985)
                ·
                  refine ⟨1505377396554407827583989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2007169862072543770111985 1505377396554407827583989)
                  ·
                    refine ⟨141129130926975733835999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1505377396554407827583989 141129130926975733835999)
                    ·
                      rfl

theorem cell23_824544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_824544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824544 prefixEnd_824544 := by exact prefixLift 824544
  have htrace : WordTrace (prefixWord ++ tailWord_824544) baseStart_824544 baseEnd_824544 := by
    simpa [prefixWord, tailWord_824544, baseEnd_824544] using wordTrace_append hprefix tailTrace_824544
  have hstable : (prefixWord ++ tailWord_824544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824544).length < 2 ^ (prefixWord ++ tailWord_824544).sum := by decide
  have hdescent : baseEnd_824544 < baseStart_824544 := by decide
  rcases family_descends (prefixWord ++ tailWord_824544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824554 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_824554 : Nat := 118140960795 + 824554 * 2 ^ 59
def prefixEnd_824554 : Nat := 4983230072969 + 3 ^ 40 * 824554 * 2
def baseEnd_824554 : Nat := 423392527587472162382951

theorem tailTrace_824554 : CollatzResearch.WordTrace tailWord_824554 prefixEnd_824554 423392527587472162382951 := by
  unfold tailWord_824554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7518488763697288864212179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20049303369859436971232477 7518488763697288864212179)
  ·
    refine ⟨11277733145545933296318269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7518488763697288864212179 11277733145545933296318269)
    ·
      refine ⟨4229149929579724986119351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11277733145545933296318269 4229149929579724986119351)
      ·
        refine ⟨6343724894369587479179027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229149929579724986119351 6343724894369587479179027)
        ·
          refine ⟨9515587341554381218768541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6343724894369587479179027 9515587341554381218768541)
          ·
            refine ⟨3568345253082892957038203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9515587341554381218768541 3568345253082892957038203)
            ·
              refine ⟨5352517879624339435557305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568345253082892957038203 5352517879624339435557305)
              ·
                refine ⟨4014388409718254576667979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5352517879624339435557305 4014388409718254576667979)
                ·
                  refine ⟨6021582614577381865001969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014388409718254576667979 6021582614577381865001969)
                  ·
                    refine ⟨4516186960933036398751477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6021582614577381865001969 4516186960933036398751477)
                    ·
                      refine ⟨423392527587472162382951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4516186960933036398751477 423392527587472162382951)
                      ·
                        rfl

theorem cell23_824554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_824554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824554 prefixEnd_824554 := by exact prefixLift 824554
  have htrace : WordTrace (prefixWord ++ tailWord_824554) baseStart_824554 baseEnd_824554 := by
    simpa [prefixWord, tailWord_824554, baseEnd_824554] using wordTrace_append hprefix tailTrace_824554
  have hstable : (prefixWord ++ tailWord_824554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824554).length < 2 ^ (prefixWord ++ tailWord_824554).sum := by decide
  have hdescent : baseEnd_824554 < baseStart_824554 := by decide
  rcases family_descends (prefixWord ++ tailWord_824554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824581 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 2, 4, 2]
def baseStart_824581 : Nat := 118140960795 + 824581 * 2 ^ 59
def prefixEnd_824581 : Nat := 4983230072969 + 3 ^ 40 * 824581 * 2
def baseEnd_824581 : Nat := 423406391565143556745327

theorem tailTrace_824581 : CollatzResearch.WordTrace tailWord_824581 prefixEnd_824581 423406391565143556745327 := by
  unfold tailWord_824581
  simp only [CollatzResearch.WordTrace]
  refine ⟨30074939825691339068081597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20049959883794226045387731 30074939825691339068081597)
  ·
    refine ⟨11278102434634252150530599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30074939825691339068081597 11278102434634252150530599)
    ·
      refine ⟨16917153651951378225795899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11278102434634252150530599 16917153651951378225795899)
      ·
        refine ⟨25375730477927067338693849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16917153651951378225795899 25375730477927067338693849)
        ·
          refine ⟨19031797858445300504020387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25375730477927067338693849 19031797858445300504020387)
          ·
            refine ⟨28547696787667950756030581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19031797858445300504020387 28547696787667950756030581)
            ·
              refine ⟨2676346573843870383377867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28547696787667950756030581 2676346573843870383377867)
              ·
                refine ⟨4014519860765805575066801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676346573843870383377867 4014519860765805575066801)
                ·
                  refine ⟨3010889895574354181300101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4014519860765805575066801 3010889895574354181300101)
                  ·
                    refine ⟨564541855420191408993769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3010889895574354181300101 564541855420191408993769)
                    ·
                      refine ⟨423406391565143556745327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564541855420191408993769 423406391565143556745327)
                      ·
                        rfl

theorem cell23_824581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_824581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824581 prefixEnd_824581 := by exact prefixLift 824581
  have htrace : WordTrace (prefixWord ++ tailWord_824581) baseStart_824581 baseEnd_824581 := by
    simpa [prefixWord, tailWord_824581, baseEnd_824581] using wordTrace_append hprefix tailTrace_824581
  have hstable : (prefixWord ++ tailWord_824581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824581).length < 2 ^ (prefixWord ++ tailWord_824581).sum := by decide
  have hdescent : baseEnd_824581 < baseStart_824581 := by decide
  rcases family_descends (prefixWord ++ tailWord_824581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824638 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_824638 : Nat := 118140960795 + 824638 * 2 ^ 59
def prefixEnd_824638 : Nat := 4983230072969 + 3 ^ 40 * 824638 * 2
def baseEnd_824638 : Nat := 47048406662494425970285

theorem tailTrace_824638 : CollatzResearch.WordTrace tailWord_824638 prefixEnd_824638 47048406662494425970285 := by
  unfold tailWord_824638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3759627348310604725363321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20051345857656558535271045 3759627348310604725363321)
  ·
    refine ⟨2819720511232953544022491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3759627348310604725363321 2819720511232953544022491)
    ·
      refine ⟨4229580766849430316033737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819720511232953544022491 4229580766849430316033737)
      ·
        refine ⟨3172185575137072737025303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4229580766849430316033737 3172185575137072737025303)
        ·
          refine ⟨4758278362705609105537955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172185575137072737025303 4758278362705609105537955)
          ·
            refine ⟨7137417544058413658306933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758278362705609105537955 7137417544058413658306933)
            ·
              refine ⟨669132894755476280466275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7137417544058413658306933 669132894755476280466275)
              ·
                refine ⟨1003699342133214420699413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669132894755476280466275 1003699342133214420699413)
                ·
                  refine ⟨47048406662494425970285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1003699342133214420699413 47048406662494425970285)
                  ·
                    rfl

theorem cell23_824638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_824638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824638 prefixEnd_824638 := by exact prefixLift 824638
  have htrace : WordTrace (prefixWord ++ tailWord_824638) baseStart_824638 baseEnd_824638 := by
    simpa [prefixWord, tailWord_824638, baseEnd_824638] using wordTrace_append hprefix tailTrace_824638
  have hstable : (prefixWord ++ tailWord_824638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824638).length < 2 ^ (prefixWord ++ tailWord_824638).sum := by decide
  have hdescent : baseEnd_824638 < baseStart_824638 := by decide
  rcases family_descends (prefixWord ++ tailWord_824638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824658 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_824658 : Nat := 118140960795 + 824658 * 2 ^ 59
def prefixEnd_824658 : Nat := 4983230072969 + 3 ^ 40 * 824658 * 2
def baseEnd_824658 : Nat := 423445929575539755482473

theorem tailTrace_824658 : CollatzResearch.WordTrace tailWord_824658 prefixEnd_824658 423445929575539755482473 := by
  unfold tailWord_824658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519437061603095304658657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20051832164274920812423085 7519437061603095304658657)
  ·
    refine ⟨5639577796202321478493993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7519437061603095304658657 5639577796202321478493993)
    ·
      refine ⟨4229683347151741108870495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5639577796202321478493993 4229683347151741108870495)
      ·
        refine ⟨6344525020727611663305743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229683347151741108870495 6344525020727611663305743)
        ·
          refine ⟨9516787531091417494958615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344525020727611663305743 9516787531091417494958615)
          ·
            refine ⟨14275181296637126242437923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9516787531091417494958615 14275181296637126242437923)
            ·
              refine ⟨21412771944955689363656885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14275181296637126242437923 21412771944955689363656885)
              ·
                refine ⟨2007447369839595877842833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21412771944955689363656885 2007447369839595877842833)
                ·
                  refine ⟨1505585527379696908382125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2007447369839595877842833 1505585527379696908382125)
                  ·
                    refine ⟨564594572767386340643297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505585527379696908382125 564594572767386340643297)
                    ·
                      refine ⟨423445929575539755482473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564594572767386340643297 423445929575539755482473)
                      ·
                        rfl

theorem cell23_824658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_824658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824658 prefixEnd_824658 := by exact prefixLift 824658
  have htrace : WordTrace (prefixWord ++ tailWord_824658) baseStart_824658 baseEnd_824658 := by
    simpa [prefixWord, tailWord_824658, baseEnd_824658] using wordTrace_append hprefix tailTrace_824658
  have hstable : (prefixWord ++ tailWord_824658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824658).length < 2 ^ (prefixWord ++ tailWord_824658).sum := by decide
  have hdescent : baseEnd_824658 < baseStart_824658 := by decide
  rcases family_descends (prefixWord ++ tailWord_824658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824664 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_824664 : Nat := 118140960795 + 824664 * 2 ^ 59
def prefixEnd_824664 : Nat := 4983230072969 + 3 ^ 40 * 824664 * 2
def baseEnd_824664 : Nat := 141149670153155577335815

theorem tailTrace_824664 : CollatzResearch.WordTrace tailWord_824664 prefixEnd_824664 141149670153155577335815 := by
  unfold tailWord_824664
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038983542195322121676523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20051978056260429495568697 15038983542195322121676523)
  ·
    refine ⟨22558475313292983182514785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15038983542195322121676523 22558475313292983182514785)
    ·
      refine ⟨16918856484969737386886089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22558475313292983182514785 16918856484969737386886089)
      ·
        refine ⟨12689142363727303040164567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16918856484969737386886089 12689142363727303040164567)
        ·
          refine ⟨19033713545590954560246851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689142363727303040164567 19033713545590954560246851)
          ·
            refine ⟨28550570318386431840370277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19033713545590954560246851 28550570318386431840370277)
            ·
              refine ⟨5353231934697455970069427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28550570318386431840370277 5353231934697455970069427)
              ·
                refine ⟨8029847902046183955104141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5353231934697455970069427 8029847902046183955104141)
                ·
                  refine ⟨3011192963267318983164053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8029847902046183955104141 3011192963267318983164053)
                  ·
                    refine ⟨141149670153155577335815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3011192963267318983164053 141149670153155577335815)
                    ·
                      rfl

theorem cell23_824664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_824664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824664 prefixEnd_824664 := by exact prefixLift 824664
  have htrace : WordTrace (prefixWord ++ tailWord_824664) baseStart_824664 baseEnd_824664 := by
    simpa [prefixWord, tailWord_824664, baseEnd_824664] using wordTrace_append hprefix tailTrace_824664
  have hstable : (prefixWord ++ tailWord_824664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824664).length < 2 ^ (prefixWord ++ tailWord_824664).sum := by decide
  have hdescent : baseEnd_824664 < baseStart_824664 := by decide
  rcases family_descends (prefixWord ++ tailWord_824664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824665 : List Nat := [1, 2, 1, 2, 2, 2, 5, 3, 1, 1, 3]
def baseStart_824665 : Nat := 118140960795 + 824665 * 2 ^ 59
def prefixEnd_824665 : Nat := 4983230072969 + 3 ^ 40 * 824665 * 2
def baseEnd_824665 : Nat := 423449523940121228094941

theorem tailTrace_824665 : CollatzResearch.WordTrace tailWord_824665 prefixEnd_824665 423449523940121228094941 := by
  unfold tailWord_824665
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078003557387021414139449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20052002371591347609426299 30078003557387021414139449)
  ·
    refine ⟨22558502668040266060604587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30078003557387021414139449 22558502668040266060604587)
    ·
      refine ⟨33837754002060399090906881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22558502668040266060604587 33837754002060399090906881)
      ·
        refine ⟨25378315501545299318180161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33837754002060399090906881 25378315501545299318180161)
        ·
          refine ⟨19033736626158974488635121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25378315501545299318180161 19033736626158974488635121)
          ·
            refine ⟨14275302469619230866476341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19033736626158974488635121 14275302469619230866476341)
            ·
              refine ⟨1338309606526802893732157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14275302469619230866476341 1338309606526802893732157)
              ·
                refine ⟨501866102447551085149559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338309606526802893732157 501866102447551085149559)
                ·
                  refine ⟨752799153671326627724339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 501866102447551085149559 752799153671326627724339)
                  ·
                    refine ⟨1129198730506989941586509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 752799153671326627724339 1129198730506989941586509)
                    ·
                      refine ⟨423449523940121228094941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129198730506989941586509 423449523940121228094941)
                      ·
                        rfl

theorem cell23_824665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_824665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824665 prefixEnd_824665 := by exact prefixLift 824665
  have htrace : WordTrace (prefixWord ++ tailWord_824665) baseStart_824665 baseEnd_824665 := by
    simpa [prefixWord, tailWord_824665, baseEnd_824665] using wordTrace_append hprefix tailTrace_824665
  have hstable : (prefixWord ++ tailWord_824665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824665).length < 2 ^ (prefixWord ++ tailWord_824665).sum := by decide
  have hdescent : baseEnd_824665 < baseStart_824665 := by decide
  rcases family_descends (prefixWord ++ tailWord_824665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824682 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_824682 : Nat := 118140960795 + 824682 * 2 ^ 59
def prefixEnd_824682 : Nat := 4983230072969 + 3 ^ 40 * 824682 * 2
def baseEnd_824682 : Nat := 423458253111247661582363

theorem tailTrace_824682 : CollatzResearch.WordTrace tailWord_824682 prefixEnd_824682 423458253111247661582363 := by
  unfold tailWord_824682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519655899581358329377075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20052415732216955545005533 7519655899581358329377075)
  ·
    refine ⟨11279483849372037494065613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7519655899581358329377075 11279483849372037494065613)
    ·
      refine ⟨4229806443514514060274605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11279483849372037494065613 4229806443514514060274605)
      ·
        refine ⟨1586177416317942772602977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4229806443514514060274605 1586177416317942772602977)
        ·
          refine ⟨1189633062238457079452233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586177416317942772602977 1189633062238457079452233)
          ·
            refine ⟨892224796678842809589175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189633062238457079452233 892224796678842809589175)
            ·
              refine ⟨1338337195018264214383763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892224796678842809589175 1338337195018264214383763)
              ·
                refine ⟨2007505792527396321575645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338337195018264214383763 2007505792527396321575645)
                ·
                  refine ⟨752814672197773620590867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2007505792527396321575645 752814672197773620590867)
                  ·
                    refine ⟨1129222008296660430886301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 752814672197773620590867 1129222008296660430886301)
                    ·
                      refine ⟨423458253111247661582363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129222008296660430886301 423458253111247661582363)
                      ·
                        rfl

theorem cell23_824682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_824682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824682 prefixEnd_824682 := by exact prefixLift 824682
  have htrace : WordTrace (prefixWord ++ tailWord_824682) baseStart_824682 baseEnd_824682 := by
    simpa [prefixWord, tailWord_824682, baseEnd_824682] using wordTrace_append hprefix tailTrace_824682
  have hstable : (prefixWord ++ tailWord_824682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824682).length < 2 ^ (prefixWord ++ tailWord_824682).sum := by decide
  have hdescent : baseEnd_824682 < baseStart_824682 := by decide
  rcases family_descends (prefixWord ++ tailWord_824682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824701 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_824701 : Nat := 118140960795 + 824701 * 2 ^ 59
def prefixEnd_824701 : Nat := 4983230072969 + 3 ^ 40 * 824701 * 2
def baseEnd_824701 : Nat := 423468009243683087244775

theorem tailTrace_824701 : CollatzResearch.WordTrace tailWord_824701 prefixEnd_824701 423468009243683087244775 := by
  unfold tailWord_824701
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079316585256599562449957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20052877723504399708299971 30079316585256599562449957)
  ·
    refine ⟨5639871859735612417959367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30079316585256599562449957 5639871859735612417959367)
    ·
      refine ⟨8459807789603418626939051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639871859735612417959367 8459807789603418626939051)
      ·
        refine ⟨12689711684405127940408577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8459807789603418626939051 12689711684405127940408577)
        ·
          refine ⟨9517283763303845955306433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12689711684405127940408577 9517283763303845955306433)
          ·
            refine ⟨7137962822477884466479825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9517283763303845955306433 7137962822477884466479825)
            ·
              refine ⟨5353472116858413349859869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137962822477884466479825 5353472116858413349859869)
              ·
                refine ⟨2007552043821905006197451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5353472116858413349859869 2007552043821905006197451)
                ·
                  refine ⟨3011328065732857509296177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007552043821905006197451 3011328065732857509296177)
                  ·
                    refine ⟨2258496049299643131972133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3011328065732857509296177 2258496049299643131972133)
                    ·
                      refine ⟨423468009243683087244775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2258496049299643131972133 423468009243683087244775)
                      ·
                        rfl

theorem cell23_824701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_824701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824701 prefixEnd_824701 := by exact prefixLift 824701
  have htrace : WordTrace (prefixWord ++ tailWord_824701) baseStart_824701 baseEnd_824701 := by
    simpa [prefixWord, tailWord_824701, baseEnd_824701] using wordTrace_append hprefix tailTrace_824701
  have hstable : (prefixWord ++ tailWord_824701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824701).length < 2 ^ (prefixWord ++ tailWord_824701).sum := by decide
  have hdescent : baseEnd_824701 < baseStart_824701 := by decide
  rcases family_descends (prefixWord ++ tailWord_824701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824708 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_824708 : Nat := 118140960795 + 824708 * 2 ^ 59
def prefixEnd_824708 : Nat := 4983230072969 + 3 ^ 40 * 824708 * 2
def baseEnd_824708 : Nat := 423471603608264559857243

theorem tailTrace_824708 : CollatzResearch.WordTrace tailWord_824708 prefixEnd_824708 423471603608264559857243 := by
  unfold tailWord_824708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15039785948115619878977389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20053047930820826505303185 15039785948115619878977389)
  ·
    refine ⟨5639919730543357454616521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15039785948115619878977389 5639919730543357454616521)
    ·
      refine ⟨4229939797907518090962391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5639919730543357454616521 4229939797907518090962391)
      ·
        refine ⟨6344909696861277136443587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229939797907518090962391 6344909696861277136443587)
        ·
          refine ⟨9517364545291915704665381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344909696861277136443587 9517364545291915704665381)
          ·
            refine ⟨1784505852242234194624759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9517364545291915704665381 1784505852242234194624759)
            ·
              refine ⟨2676758778363351291937139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784505852242234194624759 2676758778363351291937139)
              ·
                refine ⟨4015138167545026937905709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676758778363351291937139 4015138167545026937905709)
                ·
                  refine ⟨1505676812829385101714641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4015138167545026937905709 1505676812829385101714641)
                  ·
                    refine ⟨1129257609622038826285981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1505676812829385101714641 1129257609622038826285981)
                    ·
                      refine ⟨423471603608264559857243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129257609622038826285981 423471603608264559857243)
                      ·
                        rfl

theorem cell23_824708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_824708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824708 prefixEnd_824708 := by exact prefixLift 824708
  have htrace : WordTrace (prefixWord ++ tailWord_824708) baseStart_824708 baseEnd_824708 := by
    simpa [prefixWord, tailWord_824708, baseEnd_824708] using wordTrace_append hprefix tailTrace_824708
  have hstable : (prefixWord ++ tailWord_824708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824708).length < 2 ^ (prefixWord ++ tailWord_824708).sum := by decide
  have hdescent : baseEnd_824708 < baseStart_824708 := by decide
  rcases family_descends (prefixWord ++ tailWord_824708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824721 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_824721 : Nat := 118140960795 + 824721 * 2 ^ 59
def prefixEnd_824721 : Nat := 4983230072969 + 3 ^ 40 * 824721 * 2
def baseEnd_824721 : Nat := 423478278856773008994683

theorem tailTrace_824721 : CollatzResearch.WordTrace tailWord_824721 prefixEnd_824721 423478278856773008994683 := by
  unfold tailWord_824721
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080046045184142978178017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20053364030122761985452011 30080046045184142978178017)
  ·
    refine ⟨22560034533888107233633513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30080046045184142978178017 22560034533888107233633513)
    ·
      refine ⟨16920025900416080425225135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22560034533888107233633513 16920025900416080425225135)
      ·
        refine ⟨25380038850624120637837703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16920025900416080425225135 25380038850624120637837703)
        ·
          refine ⟨38070058275936180956756555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25380038850624120637837703 38070058275936180956756555)
          ·
            refine ⟨57105087413904271435134833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38070058275936180956756555 57105087413904271435134833)
            ·
              refine ⟨42828815560428203576351125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57105087413904271435134833 42828815560428203576351125)
              ·
                refine ⟨2007600729395072042641459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42828815560428203576351125 2007600729395072042641459)
                ·
                  refine ⟨3011401094092608063962189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2007600729395072042641459 3011401094092608063962189)
                  ·
                    refine ⟨1129275410284728023985821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3011401094092608063962189 1129275410284728023985821)
                    ·
                      refine ⟨423478278856773008994683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129275410284728023985821 423478278856773008994683)
                      ·
                        rfl

theorem cell23_824721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_824721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824721 prefixEnd_824721 := by exact prefixLift 824721
  have htrace : WordTrace (prefixWord ++ tailWord_824721) baseStart_824721 baseEnd_824721 := by
    simpa [prefixWord, tailWord_824721, baseEnd_824721] using wordTrace_append hprefix tailTrace_824721
  have hstable : (prefixWord ++ tailWord_824721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824721).length < 2 ^ (prefixWord ++ tailWord_824721).sum := by decide
  have hdescent : baseEnd_824721 < baseStart_824721 := by decide
  rcases family_descends (prefixWord ++ tailWord_824721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824731 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 9, 2]
def baseStart_824731 : Nat := 118140960795 + 824731 * 2 ^ 59
def prefixEnd_824731 : Nat := 4983230072969 + 3 ^ 40 * 824731 * 2
def baseEnd_824731 : Nat := 423483413663317969869637

theorem tailTrace_824731 : CollatzResearch.WordTrace tailWord_824731 prefixEnd_824731 423483413663317969869637 := by
  unfold tailWord_824731
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080410775147914686042047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20053607183431943124028031 30080410775147914686042047)
  ·
    refine ⟨45120616162721872029063071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30080410775147914686042047 45120616162721872029063071)
    ·
      refine ⟨67680924244082808043594607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45120616162721872029063071 67680924244082808043594607)
      ·
        refine ⟨101521386366124212065391911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67680924244082808043594607 101521386366124212065391911)
        ·
          refine ⟨152282079549186318098087867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101521386366124212065391911 152282079549186318098087867)
          ·
            refine ⟨228423119323779477147131801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152282079549186318098087867 228423119323779477147131801)
            ·
              refine ⟨171317339492834607860348851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228423119323779477147131801 171317339492834607860348851)
              ·
                refine ⟨256976009239251911790523277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171317339492834607860348851 256976009239251911790523277)
                ·
                  refine ⟨96366003464719466921446229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256976009239251911790523277 96366003464719466921446229)
                  ·
                    refine ⟨564644551551090626492849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 96366003464719466921446229 564644551551090626492849)
                    ·
                      refine ⟨423483413663317969869637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564644551551090626492849 423483413663317969869637)
                      ·
                        rfl

theorem cell23_824731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9, 2].length) (baseStart_824731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824731 prefixEnd_824731 := by exact prefixLift 824731
  have htrace : WordTrace (prefixWord ++ tailWord_824731) baseStart_824731 baseEnd_824731 := by
    simpa [prefixWord, tailWord_824731, baseEnd_824731] using wordTrace_append hprefix tailTrace_824731
  have hstable : (prefixWord ++ tailWord_824731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824731).length < 2 ^ (prefixWord ++ tailWord_824731).sum := by decide
  have hdescent : baseEnd_824731 < baseStart_824731 := by decide
  rcases family_descends (prefixWord ++ tailWord_824731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824732 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_824732 : Nat := 118140960795 + 824732 * 2 ^ 59
def prefixEnd_824732 : Nat := 4983230072969 + 3 ^ 40 * 824732 * 2
def baseEnd_824732 : Nat := 141161309047990821985711

theorem tailTrace_824732 : CollatzResearch.WordTrace tailWord_824732 prefixEnd_824732 141161309047990821985711 := by
  unfold tailWord_824732
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040223624072145928414225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20053631498762861237885633 15040223624072145928414225)
  ·
    refine ⟨11280167718054109446310669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15040223624072145928414225 11280167718054109446310669)
    ·
      refine ⟨4230062894270291042366501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11280167718054109446310669 4230062894270291042366501)
      ·
        refine ⟨793136792675679570443719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4230062894270291042366501 793136792675679570443719)
        ·
          refine ⟨1189705189013519355665579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793136792675679570443719 1189705189013519355665579)
          ·
            refine ⟨1784557783520279033498369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189705189013519355665579 1784557783520279033498369)
            ·
              refine ⟨1338418337640209275123777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784557783520279033498369 1338418337640209275123777)
              ·
                refine ⟨1003813753230156956342833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338418337640209275123777 1003813753230156956342833)
                ·
                  refine ⟨752860314922617717257125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1003813753230156956342833 752860314922617717257125)
                  ·
                    refine ⟨141161309047990821985711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 752860314922617717257125 141161309047990821985711)
                    ·
                      rfl

theorem cell23_824732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_824732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824732 prefixEnd_824732 := by exact prefixLift 824732
  have htrace : WordTrace (prefixWord ++ tailWord_824732) baseStart_824732 baseEnd_824732 := by
    simpa [prefixWord, tailWord_824732, baseEnd_824732] using wordTrace_append hprefix tailTrace_824732
  have hstable : (prefixWord ++ tailWord_824732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824732).length < 2 ^ (prefixWord ++ tailWord_824732).sum := by decide
  have hdescent : baseEnd_824732 < baseStart_824732 := by decide
  rcases family_descends (prefixWord ++ tailWord_824732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824748 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 3, 3, 2]
def baseStart_824748 : Nat := 118140960795 + 824748 * 2 ^ 59
def prefixEnd_824748 : Nat := 4983230072969 + 3 ^ 40 * 824748 * 2
def baseEnd_824748 : Nat := 423492142834444403357059

theorem tailTrace_824748 : CollatzResearch.WordTrace tailWord_824748 prefixEnd_824748 423492142834444403357059 := by
  unfold tailWord_824748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15040515408043163294705449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20054020544057551059607265 15040515408043163294705449)
  ·
    refine ⟨11280386556032372471029087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15040515408043163294705449 11280386556032372471029087)
    ·
      refine ⟨16920579834048558706543631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11280386556032372471029087 16920579834048558706543631)
      ·
        refine ⟨25380869751072838059815447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16920579834048558706543631 25380869751072838059815447)
        ·
          refine ⟨38071304626609257089723171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25380869751072838059815447 38071304626609257089723171)
          ·
            refine ⟨57106956939913885634584757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38071304626609257089723171 57106956939913885634584757)
            ·
              refine ⟨5353777213116926778242321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57106956939913885634584757 5353777213116926778242321)
              ·
                refine ⟨4015332909837695083681741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353777213116926778242321 4015332909837695083681741)
                ·
                  refine ⟨1505749841189135656380653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4015332909837695083681741 1505749841189135656380653)
                  ·
                    refine ⟨564656190445925871142745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505749841189135656380653 564656190445925871142745)
                    ·
                      refine ⟨423492142834444403357059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564656190445925871142745 423492142834444403357059)
                      ·
                        rfl

theorem cell23_824748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_824748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824748 prefixEnd_824748 := by exact prefixLift 824748
  have htrace : WordTrace (prefixWord ++ tailWord_824748) baseStart_824748 baseEnd_824748 := by
    simpa [prefixWord, tailWord_824748, baseEnd_824748] using wordTrace_append hprefix tailTrace_824748
  have hstable : (prefixWord ++ tailWord_824748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824748).length < 2 ^ (prefixWord ++ tailWord_824748).sum := by decide
  have hdescent : baseEnd_824748 < baseStart_824748 := by decide
  rcases family_descends (prefixWord ++ tailWord_824748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824765 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_824765 : Nat := 118140960795 + 824765 * 2 ^ 59
def prefixEnd_824765 : Nat := 4983230072969 + 3 ^ 40 * 824765 * 2
def baseEnd_824765 : Nat := 423500872005570836844481

theorem tailTrace_824765 : CollatzResearch.WordTrace tailWord_824765 prefixEnd_824765 423500872005570836844481 := by
  unfold tailWord_824765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30081650857024738492779749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20054433904683158995186499 30081650857024738492779749)
  ·
    refine ⟨5640309535692138467396203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30081650857024738492779749 5640309535692138467396203)
    ·
      refine ⟨8460464303538207701094305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640309535692138467396203 8460464303538207701094305)
      ·
        refine ⟨6345348227653655775820729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8460464303538207701094305 6345348227653655775820729)
        ·
          refine ⟨4759011170740241831865547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6345348227653655775820729 4759011170740241831865547)
          ·
            refine ⟨7138516756110362747798321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759011170740241831865547 7138516756110362747798321)
            ·
              refine ⟨5353887567082772060848741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7138516756110362747798321 5353887567082772060848741)
              ·
                refine ⟨1003853918828019761409139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5353887567082772060848741 1003853918828019761409139)
                ·
                  refine ⟨1505780878242029642113709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003853918828019761409139 1505780878242029642113709)
                  ·
                    refine ⟨564667829340761115792641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505780878242029642113709 564667829340761115792641)
                    ·
                      refine ⟨423500872005570836844481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564667829340761115792641 423500872005570836844481)
                      ·
                        rfl

theorem cell23_824765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_824765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824765 prefixEnd_824765 := by exact prefixLift 824765
  have htrace : WordTrace (prefixWord ++ tailWord_824765) baseStart_824765 baseEnd_824765 := by
    simpa [prefixWord, tailWord_824765, baseEnd_824765] using wordTrace_append hprefix tailTrace_824765
  have hstable : (prefixWord ++ tailWord_824765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824765).length < 2 ^ (prefixWord ++ tailWord_824765).sum := by decide
  have hdescent : baseEnd_824765 < baseStart_824765 := by decide
  rcases family_descends (prefixWord ++ tailWord_824765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824782 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_824782 : Nat := 118140960795 + 824782 * 2 ^ 59
def prefixEnd_824782 : Nat := 4983230072969 + 3 ^ 40 * 824782 * 2
def baseEnd_824782 : Nat := 423509601176697270331903

theorem tailTrace_824782 : CollatzResearch.WordTrace tailWord_824782 prefixEnd_824782 423509601176697270331903 := by
  unfold tailWord_824782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760283862245393799518575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20054847265308766930765733 3760283862245393799518575)
  ·
    refine ⟨5640425793368090699277863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760283862245393799518575 5640425793368090699277863)
    ·
      refine ⟨8460638690052136048916795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640425793368090699277863 8460638690052136048916795)
      ·
        refine ⟨12690958035078204073375193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460638690052136048916795 12690958035078204073375193)
        ·
          refine ⟨9518218526308653055031395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690958035078204073375193 9518218526308653055031395)
          ·
            refine ⟨14277327789462979582547093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9518218526308653055031395 14277327789462979582547093)
            ·
              refine ⟨669249740131077167931895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14277327789462979582547093 669249740131077167931895)
              ·
                refine ⟨1003874610196615751897843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669249740131077167931895 1003874610196615751897843)
                ·
                  refine ⟨1505811915294923627846765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1003874610196615751897843 1505811915294923627846765)
                  ·
                    refine ⟨564679468235596360442537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1505811915294923627846765 564679468235596360442537)
                    ·
                      refine ⟨423509601176697270331903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564679468235596360442537 423509601176697270331903)
                      ·
                        rfl

theorem cell23_824782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_824782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824782 prefixEnd_824782 := by exact prefixLift 824782
  have htrace : WordTrace (prefixWord ++ tailWord_824782) baseStart_824782 baseEnd_824782 := by
    simpa [prefixWord, tailWord_824782, baseEnd_824782] using wordTrace_append hprefix tailTrace_824782
  have hstable : (prefixWord ++ tailWord_824782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824782).length < 2 ^ (prefixWord ++ tailWord_824782).sum := by decide
  have hdescent : baseEnd_824782 < baseStart_824782 := by decide
  rcases family_descends (prefixWord ++ tailWord_824782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824801 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 7]
def baseStart_824801 : Nat := 118140960795 + 824801 * 2 ^ 59
def prefixEnd_824801 : Nat := 4983230072969 + 3 ^ 40 * 824801 * 2
def baseEnd_824801 : Nat := 47057706367681410666035

theorem tailTrace_824801 : CollatzResearch.WordTrace tailWord_824801 prefixEnd_824801 47057706367681410666035 := by
  unfold tailWord_824801
  simp only [CollatzResearch.WordTrace]
  refine ⟨30082963884894316641090257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20055309256596211094060171 30082963884894316641090257)
  ·
    refine ⟨22562222913670737480817693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30082963884894316641090257 22562222913670737480817693)
    ·
      refine ⟨8460833592626526555306635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22562222913670737480817693 8460833592626526555306635)
      ·
        refine ⟨12691250388939789832959953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460833592626526555306635 12691250388939789832959953)
        ·
          refine ⟨9518437791704842374719965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12691250388939789832959953 9518437791704842374719965)
          ·
            refine ⟨3569414171889315890519987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9518437791704842374719965 3569414171889315890519987)
            ·
              refine ⟨5354121257833973835779981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569414171889315890519987 5354121257833973835779981)
              ·
                refine ⟨2007795471687740188417493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5354121257833973835779981 2007795471687740188417493)
                ·
                  refine ⟨47057706367681410666035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2007795471687740188417493 47057706367681410666035)
                  ·
                    rfl

theorem cell23_824801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_824801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824801 prefixEnd_824801 := by exact prefixLift 824801
  have htrace : WordTrace (prefixWord ++ tailWord_824801) baseStart_824801 baseEnd_824801 := by
    simpa [prefixWord, tailWord_824801, baseEnd_824801] using wordTrace_append hprefix tailTrace_824801
  have hstable : (prefixWord ++ tailWord_824801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824801).length < 2 ^ (prefixWord ++ tailWord_824801).sum := by decide
  have hdescent : baseEnd_824801 < baseStart_824801 := by decide
  rcases family_descends (prefixWord ++ tailWord_824801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824811 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 3]
def baseStart_824811 : Nat := 118140960795 + 824811 * 2 ^ 59
def prefixEnd_824811 : Nat := 4983230072969 + 3 ^ 40 * 824811 * 2
def baseEnd_824811 : Nat := 423524492115677656869269

theorem tailTrace_824811 : CollatzResearch.WordTrace tailWord_824811 prefixEnd_824811 423524492115677656869269 := by
  unfold tailWord_824811
  simp only [CollatzResearch.WordTrace]
  refine ⟨30083328614858088348954287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20055552409905392232636191 30083328614858088348954287)
  ·
    refine ⟨45124992922287132523431431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30083328614858088348954287 45124992922287132523431431)
    ·
      refine ⟨67687489383430698785147147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45124992922287132523431431 67687489383430698785147147)
      ·
        refine ⟨101531234075146048177720721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67687489383430698785147147 101531234075146048177720721)
        ·
          refine ⟨76148425556359536133290541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101531234075146048177720721 76148425556359536133290541)
          ·
            refine ⟨28555659583634826049983953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76148425556359536133290541 28555659583634826049983953)
            ·
              refine ⟨21416744687726119537487965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28555659583634826049983953 21416744687726119537487965)
              ·
                refine ⟨8031279257897294826557987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21416744687726119537487965 8031279257897294826557987)
                ·
                  refine ⟨12046918886845942239836981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8031279257897294826557987 12046918886845942239836981)
                  ·
                    refine ⟨1129398645641807084984717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12046918886845942239836981 1129398645641807084984717)
                    ·
                      refine ⟨423524492115677656869269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129398645641807084984717 423524492115677656869269)
                      ·
                        rfl

theorem cell23_824811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 3].length) (baseStart_824811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824811 prefixEnd_824811 := by exact prefixLift 824811
  have htrace : WordTrace (prefixWord ++ tailWord_824811) baseStart_824811 baseEnd_824811 := by
    simpa [prefixWord, tailWord_824811, baseEnd_824811] using wordTrace_append hprefix tailTrace_824811
  have hstable : (prefixWord ++ tailWord_824811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824811).length < 2 ^ (prefixWord ++ tailWord_824811).sum := by decide
  have hdescent : baseEnd_824811 < baseStart_824811 := by decide
  rcases family_descends (prefixWord ++ tailWord_824811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824818 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_824818 : Nat := 118140960795 + 824818 * 2 ^ 59
def prefixEnd_824818 : Nat := 4983230072969 + 3 ^ 40 * 824818 * 2
def baseEnd_824818 : Nat := 47058676275584347720193

theorem tailTrace_824818 : CollatzResearch.WordTrace tailWord_824818 prefixEnd_824818 47058676275584347720193 := by
  unfold tailWord_824818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520895981458182136114777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20055722617221819029639405 7520895981458182136114777)
  ·
    refine ⟨5640671986093636602086083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7520895981458182136114777 5640671986093636602086083)
    ·
      refine ⟨8461007979140454903129125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640671986093636602086083 8461007979140454903129125)
      ·
        refine ⟨1586438996088835294336711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8461007979140454903129125 1586438996088835294336711)
        ·
          refine ⟨2379658494133252941505067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586438996088835294336711 2379658494133252941505067)
          ·
            refine ⟨3569487741199879412257601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379658494133252941505067 3569487741199879412257601)
            ·
              refine ⟨2677115805899909559193201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569487741199879412257601 2677115805899909559193201)
              ·
                refine ⟨2007836854424932169394901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677115805899909559193201 2007836854424932169394901)
                ·
                  refine ⟨47058676275584347720193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2007836854424932169394901 47058676275584347720193)
                  ·
                    rfl

theorem cell23_824818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_824818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824818 prefixEnd_824818 := by exact prefixLift 824818
  have htrace : WordTrace (prefixWord ++ tailWord_824818) baseStart_824818 baseEnd_824818 := by
    simpa [prefixWord, tailWord_824818, baseEnd_824818] using wordTrace_append hprefix tailTrace_824818
  have hstable : (prefixWord ++ tailWord_824818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824818).length < 2 ^ (prefixWord ++ tailWord_824818).sum := by decide
  have hdescent : baseEnd_824818 < baseStart_824818 := by decide
  rcases family_descends (prefixWord ++ tailWord_824818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824841 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_824841 : Nat := 118140960795 + 824841 * 2 ^ 59
def prefixEnd_824841 : Nat := 4983230072969 + 3 ^ 40 * 824841 * 2
def baseEnd_824841 : Nat := 423539896535312539494131

theorem tailTrace_824841 : CollatzResearch.WordTrace tailWord_824841 prefixEnd_824841 423539896535312539494131 := by
  unfold tailWord_824841
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084422804749403472546377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20056281869832935648364251 30084422804749403472546377)
  ·
    refine ⟨22563317103562052604409783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30084422804749403472546377 22563317103562052604409783)
    ·
      refine ⟨33844975655343078906614675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22563317103562052604409783 33844975655343078906614675)
      ·
        refine ⟨50767463483014618359922013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33844975655343078906614675 50767463483014618359922013)
        ·
          refine ⟨19037798806130481884970755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50767463483014618359922013 19037798806130481884970755)
          ·
            refine ⟨28556698209195722827456133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19037798806130481884970755 28556698209195722827456133)
            ·
              refine ⟨5354380914224198030148025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28556698209195722827456133 5354380914224198030148025)
              ·
                refine ⟨4015785685668148522611019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5354380914224198030148025 4015785685668148522611019)
                ·
                  refine ⟨6023678528502222783916529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015785685668148522611019 6023678528502222783916529)
                  ·
                    refine ⟨4517758896376667087937397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6023678528502222783916529 4517758896376667087937397)
                    ·
                      refine ⟨423539896535312539494131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4517758896376667087937397 423539896535312539494131)
                      ·
                        rfl

theorem cell23_824841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_824841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824841 prefixEnd_824841 := by exact prefixLift 824841
  have htrace : WordTrace (prefixWord ++ tailWord_824841) baseStart_824841 baseEnd_824841 := by
    simpa [prefixWord, tailWord_824841, baseEnd_824841] using wordTrace_append hprefix tailTrace_824841
  have hstable : (prefixWord ++ tailWord_824841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824841).length < 2 ^ (prefixWord ++ tailWord_824841).sum := by decide
  have hdescent : baseEnd_824841 < baseStart_824841 := by decide
  rcases family_descends (prefixWord ++ tailWord_824841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824852 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 7]
def baseStart_824852 : Nat := 118140960795 + 824852 * 2 ^ 59
def prefixEnd_824852 : Nat := 4983230072969 + 3 ^ 40 * 824852 * 2
def baseEnd_824852 : Nat := 47060616091390221828509

theorem tailTrace_824852 : CollatzResearch.WordTrace tailWord_824852 prefixEnd_824852 47060616091390221828509 := by
  unfold tailWord_824852
  simp only [CollatzResearch.WordTrace]
  refine ⟨15042412003854776175598405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20056549338473034900797873 15042412003854776175598405)
  ·
    refine ⟨2820452250722770532924701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15042412003854776175598405 2820452250722770532924701)
    ·
      refine ⟨1057669594021038949846763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2820452250722770532924701 1057669594021038949846763)
      ·
        refine ⟨1586504391031558424770145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057669594021038949846763 1586504391031558424770145)
        ·
          refine ⟨1189878293273668818577609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586504391031558424770145 1189878293273668818577609)
          ·
            refine ⟨892408719955251613933207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189878293273668818577609 892408719955251613933207)
            ·
              refine ⟨1338613079932877420899811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892408719955251613933207 1338613079932877420899811)
              ·
                refine ⟨2007919619899316131349717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338613079932877420899811 2007919619899316131349717)
                ·
                  refine ⟨47060616091390221828509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2007919619899316131349717 47060616091390221828509)
                  ·
                    rfl

theorem cell23_824852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_824852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824852 prefixEnd_824852 := by exact prefixLift 824852
  have htrace : WordTrace (prefixWord ++ tailWord_824852) baseStart_824852 baseEnd_824852 := by
    simpa [prefixWord, tailWord_824852, baseEnd_824852] using wordTrace_append hprefix tailTrace_824852
  have hstable : (prefixWord ++ tailWord_824852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824852).length < 2 ^ (prefixWord ++ tailWord_824852).sum := by decide
  have hdescent : baseEnd_824852 < baseStart_824852 := by decide
  rcases family_descends (prefixWord ++ tailWord_824852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824881 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_824881 : Nat := 118140960795 + 824881 * 2 ^ 59
def prefixEnd_824881 : Nat := 4983230072969 + 3 ^ 40 * 824881 * 2
def baseEnd_824881 : Nat := 423560435761492382993947

theorem tailTrace_824881 : CollatzResearch.WordTrace tailWord_824881 prefixEnd_824881 423560435761492382993947 := by
  unfold tailWord_824881
  simp only [CollatzResearch.WordTrace]
  refine ⟨30085881724604490304002497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20057254483069660202668331 30085881724604490304002497)
  ·
    refine ⟨22564411293453367728001873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30085881724604490304002497 22564411293453367728001873)
    ·
      refine ⟨16923308470090025796001405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22564411293453367728001873 16923308470090025796001405)
      ·
        refine ⟨6346240676283759673500527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16923308470090025796001405 6346240676283759673500527)
        ·
          refine ⟨9519361014425639510250791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346240676283759673500527 9519361014425639510250791)
          ·
            refine ⟨14279041521638459265376187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9519361014425639510250791 14279041521638459265376187)
            ·
              refine ⟨21418562282457688898064281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14279041521638459265376187 21418562282457688898064281)
              ·
                refine ⟨16063921711843266673548211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21418562282457688898064281 16063921711843266673548211)
                ·
                  refine ⟨24095882567764900010322317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16063921711843266673548211 24095882567764900010322317)
                  ·
                    refine ⟨9035955962911837503870869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24095882567764900010322317 9035955962911837503870869)
                    ·
                      refine ⟨423560435761492382993947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9035955962911837503870869 423560435761492382993947)
                      ·
                        rfl

theorem cell23_824881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_824881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824881 prefixEnd_824881 := by exact prefixLift 824881
  have htrace : WordTrace (prefixWord ++ tailWord_824881) baseStart_824881 baseEnd_824881 := by
    simpa [prefixWord, tailWord_824881, baseEnd_824881] using wordTrace_append hprefix tailTrace_824881
  have hstable : (prefixWord ++ tailWord_824881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824881).length < 2 ^ (prefixWord ++ tailWord_824881).sum := by decide
  have hdescent : baseEnd_824881 < baseStart_824881 := by decide
  rcases family_descends (prefixWord ++ tailWord_824881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824885 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_824885 : Nat := 118140960795 + 824885 * 2 ^ 59
def prefixEnd_824885 : Nat := 4983230072969 + 3 ^ 40 * 824885 * 2
def baseEnd_824885 : Nat := 423562489684110367343929

theorem tailTrace_824885 : CollatzResearch.WordTrace tailWord_824885 prefixEnd_824885 423562489684110367343929 := by
  unfold tailWord_824885
  simp only [CollatzResearch.WordTrace]
  refine ⟨30086027616589998987148109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20057351744393332658098739 30086027616589998987148109)
  ·
    refine ⟨11282260356221249620180541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30086027616589998987148109 11282260356221249620180541)
    ·
      refine ⟨4230847633582968607567703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11282260356221249620180541 4230847633582968607567703)
      ·
        refine ⟨6346271450374452911351555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230847633582968607567703 6346271450374452911351555)
        ·
          refine ⟨9519407175561679367027333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346271450374452911351555 9519407175561679367027333)
          ·
            refine ⟨1784888845417814881317625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9519407175561679367027333 1784888845417814881317625)
            ·
              refine ⟨1338666634063361160988219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784888845417814881317625 1338666634063361160988219)
              ·
                refine ⟨2007999951095041741482329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338666634063361160988219 2007999951095041741482329)
                ·
                  refine ⟨1505999963321281306111747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2007999951095041741482329 1505999963321281306111747)
                  ·
                    refine ⟨2258999944981921959167621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1505999963321281306111747 2258999944981921959167621)
                    ·
                      refine ⟨423562489684110367343929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2258999944981921959167621 423562489684110367343929)
                      ·
                        rfl

theorem cell23_824885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_824885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824885 prefixEnd_824885 := by exact prefixLift 824885
  have htrace : WordTrace (prefixWord ++ tailWord_824885) baseStart_824885 baseEnd_824885 := by
    simpa [prefixWord, tailWord_824885, baseEnd_824885] using wordTrace_append hprefix tailTrace_824885
  have hstable : (prefixWord ++ tailWord_824885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824885).length < 2 ^ (prefixWord ++ tailWord_824885).sum := by decide
  have hdescent : baseEnd_824885 < baseStart_824885 := by decide
  rcases family_descends (prefixWord ++ tailWord_824885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824908 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 6]
def baseStart_824908 : Nat := 118140960795 + 824908 * 2 ^ 59
def prefixEnd_824908 : Nat := 4983230072969 + 3 ^ 40 * 824908 * 2
def baseEnd_824908 : Nat := 47063811082129308595147

theorem tailTrace_824908 : CollatzResearch.WordTrace tailWord_824908 prefixEnd_824908 47063811082129308595147 := by
  unfold tailWord_824908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15043433247753336957617689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20057910997004449276823585 15043433247753336957617689)
  ·
    refine ⟨11282574935815002718213267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15043433247753336957617689 11282574935815002718213267)
    ·
      refine ⟨16923862403722504077319901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11282574935815002718213267 16923862403722504077319901)
      ·
        refine ⟨6346448401395939028994963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16923862403722504077319901 6346448401395939028994963)
        ·
          refine ⟨9519672602093908543492445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346448401395939028994963 9519672602093908543492445)
          ·
            refine ⟨3569877225785215703809667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9519672602093908543492445 3569877225785215703809667)
            ·
              refine ⟨5354815838677823555714501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569877225785215703809667 5354815838677823555714501)
              ·
                refine ⟨1004027969752091916696469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5354815838677823555714501 1004027969752091916696469)
                ·
                  refine ⟨47063811082129308595147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1004027969752091916696469 47063811082129308595147)
                  ·
                    rfl

theorem cell23_824908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_824908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824908 prefixEnd_824908 := by exact prefixLift 824908
  have htrace : WordTrace (prefixWord ++ tailWord_824908) baseStart_824908 baseEnd_824908 := by
    simpa [prefixWord, tailWord_824908, baseEnd_824908] using wordTrace_append hprefix tailTrace_824908
  have hstable : (prefixWord ++ tailWord_824908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824908).length < 2 ^ (prefixWord ++ tailWord_824908).sum := by decide
  have hdescent : baseEnd_824908 < baseStart_824908 := by decide
  rcases family_descends (prefixWord ++ tailWord_824908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824911 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_824911 : Nat := 118140960795 + 824911 * 2 ^ 59
def prefixEnd_824911 : Nat := 4983230072969 + 3 ^ 40 * 824911 * 2
def baseEnd_824911 : Nat := 423575840181127265618809

theorem tailTrace_824911 : CollatzResearch.WordTrace tailWord_824911 prefixEnd_824911 423575840181127265618809 := by
  unfold tailWord_824911
  simp only [CollatzResearch.WordTrace]
  refine ⟨30086975914495805427594587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20057983942997203618396391 30086975914495805427594587)
  ·
    refine ⟨45130463871743708141391881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30086975914495805427594587 45130463871743708141391881)
    ·
      refine ⟨33847847903807781106043911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45130463871743708141391881 33847847903807781106043911)
      ·
        refine ⟨50771771855711671659065867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33847847903807781106043911 50771771855711671659065867)
        ·
          refine ⟨76157657783567507488598801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50771771855711671659065867 76157657783567507488598801)
          ·
            refine ⟨57118243337675630616449101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76157657783567507488598801 57118243337675630616449101)
            ·
              refine ⟨21419341251628361481168413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57118243337675630616449101 21419341251628361481168413)
              ·
                refine ⟨8032252969360635555438155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21419341251628361481168413 8032252969360635555438155)
                ·
                  refine ⟨12048379454040953333157233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032252969360635555438155 12048379454040953333157233)
                  ·
                    refine ⟨9036284590530714999867925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12048379454040953333157233 9036284590530714999867925)
                    ·
                      refine ⟨423575840181127265618809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9036284590530714999867925 423575840181127265618809)
                      ·
                        rfl

theorem cell23_824911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_824911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824911 prefixEnd_824911 := by exact prefixLift 824911
  have htrace : WordTrace (prefixWord ++ tailWord_824911) baseStart_824911 baseEnd_824911 := by
    simpa [prefixWord, tailWord_824911, baseEnd_824911] using wordTrace_append hprefix tailTrace_824911
  have hstable : (prefixWord ++ tailWord_824911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824911).length < 2 ^ (prefixWord ++ tailWord_824911).sum := by decide
  have hdescent : baseEnd_824911 < baseStart_824911 := by decide
  rcases family_descends (prefixWord ++ tailWord_824911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824935 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_824935 : Nat := 118140960795 + 824935 * 2 ^ 59
def prefixEnd_824935 : Nat := 4983230072969 + 3 ^ 40 * 824935 * 2
def baseEnd_824935 : Nat := 423588163716835171718699

theorem tailTrace_824935 : CollatzResearch.WordTrace tailWord_824935 prefixEnd_824935 423588163716835171718699 := by
  unfold tailWord_824935
  simp only [CollatzResearch.WordTrace]
  refine ⟨30087851266408857526468259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20058567510939238350978839 30087851266408857526468259)
  ·
    refine ⟨45131776899613286289702389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30087851266408857526468259 45131776899613286289702389)
    ·
      refine ⟨4231104084338745589659599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45131776899613286289702389 4231104084338745589659599)
      ·
        refine ⟨6346656126508118384489399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231104084338745589659599 6346656126508118384489399)
        ·
          refine ⟨9519984189762177576734099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346656126508118384489399 9519984189762177576734099)
          ·
            refine ⟨14279976284643266365101149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9519984189762177576734099 14279976284643266365101149)
            ·
              refine ⟨5354991106741224886912931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14279976284643266365101149 5354991106741224886912931)
              ·
                refine ⟨8032486660111837330369397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5354991106741224886912931 8032486660111837330369397)
                ·
                  refine ⟨753045624385484749722131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8032486660111837330369397 753045624385484749722131)
                  ·
                    refine ⟨1129568436578227124583197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 753045624385484749722131 1129568436578227124583197)
                    ·
                      refine ⟨423588163716835171718699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129568436578227124583197 423588163716835171718699)
                      ·
                        rfl

theorem cell23_824935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_824935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824935 prefixEnd_824935 := by exact prefixLift 824935
  have htrace : WordTrace (prefixWord ++ tailWord_824935) baseStart_824935 baseEnd_824935 := by
    simpa [prefixWord, tailWord_824935, baseEnd_824935] using wordTrace_append hprefix tailTrace_824935
  have hstable : (prefixWord ++ tailWord_824935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824935).length < 2 ^ (prefixWord ++ tailWord_824935).sum := by decide
  have hdescent : baseEnd_824935 < baseStart_824935 := by decide
  rcases family_descends (prefixWord ++ tailWord_824935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824992 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4]
def baseStart_824992 : Nat := 118140960795 + 824992 * 2 ^ 59
def prefixEnd_824992 : Nat := 4983230072969 + 3 ^ 40 * 824992 * 2
def baseEnd_824992 : Nat := 423617432114141448705937

theorem tailTrace_824992 : CollatzResearch.WordTrace tailWord_824992 prefixEnd_824992 423617432114141448705937 := by
  unfold tailWord_824992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15044965113601178130646615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20059953484801570840862153 15044965113601178130646615)
  ·
    refine ⟨22567447670401767195969923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15044965113601178130646615 22567447670401767195969923)
    ·
      refine ⟨33851171505602650793954885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22567447670401767195969923 33851171505602650793954885)
      ·
        refine ⟨6347094657300497023866541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33851171505602650793954885 6347094657300497023866541)
        ·
          refine ⟨2380160496487686383949953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6347094657300497023866541 2380160496487686383949953)
          ·
            refine ⟨1785120372365764787962465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380160496487686383949953 1785120372365764787962465)
            ·
              refine ⟨1338840279274323590971849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785120372365764787962465 1338840279274323590971849)
              ·
                refine ⟨1004130209455742693228887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338840279274323590971849 1004130209455742693228887)
                ·
                  refine ⟨1506195314183614039843331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004130209455742693228887 1506195314183614039843331)
                  ·
                    refine ⟨2259292971275421059764997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1506195314183614039843331 2259292971275421059764997)
                    ·
                      refine ⟨423617432114141448705937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2259292971275421059764997 423617432114141448705937)
                      ·
                        rfl

theorem cell23_824992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_824992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_824992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_824992 prefixEnd_824992 := by exact prefixLift 824992
  have htrace : WordTrace (prefixWord ++ tailWord_824992) baseStart_824992 baseEnd_824992 := by
    simpa [prefixWord, tailWord_824992, baseEnd_824992] using wordTrace_append hprefix tailTrace_824992
  have hstable : (prefixWord ++ tailWord_824992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824992).length < 2 ^ (prefixWord ++ tailWord_824992).sum := by decide
  have hdescent : baseEnd_824992 < baseStart_824992 := by decide
  rcases family_descends (prefixWord ++ tailWord_824992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825005 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_825005 : Nat := 118140960795 + 825005 * 2 ^ 59
def prefixEnd_825005 : Nat := 4983230072969 + 3 ^ 40 * 825005 * 2
def baseEnd_825005 : Nat := 423624107362649897843377

theorem tailTrace_825005 : CollatzResearch.WordTrace tailWord_825005 prefixEnd_825005 423624107362649897843377 := by
  unfold tailWord_825005
  simp only [CollatzResearch.WordTrace]
  refine ⟨30090404376155259481516469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20060269584103506321010979 30090404376155259481516469)
  ·
    refine ⟨2820975410264555576392169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30090404376155259481516469 2820975410264555576392169)
    ·
      refine ⟨2115731557698416682294127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2820975410264555576392169 2115731557698416682294127)
      ·
        refine ⟨3173597336547625023441191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115731557698416682294127 3173597336547625023441191)
        ·
          refine ⟨4760396004821437535161787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173597336547625023441191 4760396004821437535161787)
          ·
            refine ⟨7140594007232156302742681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760396004821437535161787 7140594007232156302742681)
            ·
              refine ⟨5355445505424117227057011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7140594007232156302742681 5355445505424117227057011)
              ·
                refine ⟨8033168258136175840585517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355445505424117227057011 8033168258136175840585517)
                ·
                  refine ⟨3012438096801065940219569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8033168258136175840585517 3012438096801065940219569)
                  ·
                    refine ⟨2259328572600799455164677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3012438096801065940219569 2259328572600799455164677)
                    ·
                      refine ⟨423624107362649897843377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2259328572600799455164677 423624107362649897843377)
                      ·
                        rfl

theorem cell23_825005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_825005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825005 prefixEnd_825005 := by exact prefixLift 825005
  have htrace : WordTrace (prefixWord ++ tailWord_825005) baseStart_825005 baseEnd_825005 := by
    simpa [prefixWord, tailWord_825005, baseEnd_825005] using wordTrace_append hprefix tailTrace_825005
  have hstable : (prefixWord ++ tailWord_825005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825005).length < 2 ^ (prefixWord ++ tailWord_825005).sum := by decide
  have hdescent : baseEnd_825005 < baseStart_825005 := by decide
  rcases family_descends (prefixWord ++ tailWord_825005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825036 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_825036 : Nat := 118140960795 + 825036 * 2 ^ 59
def prefixEnd_825036 : Nat := 4983230072969 + 3 ^ 40 * 825036 * 2
def baseEnd_825036 : Nat := 141213341754313092185245

theorem tailTrace_825036 : CollatzResearch.WordTrace tailWord_825036 prefixEnd_825036 141213341754313092185245 := by
  unfold tailWord_825036
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045767519521475887947481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20061023359361967850596641 15045767519521475887947481)
  ·
    refine ⟨11284325639641106915960611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15045767519521475887947481 11284325639641106915960611)
    ·
      refine ⟨16926488459461660373940917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11284325639641106915960611 16926488459461660373940917)
      ·
        refine ⟨1586858293074530660056961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16926488459461660373940917 1586858293074530660056961)
        ·
          refine ⟨1190143719805897995042721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586858293074530660056961 1190143719805897995042721)
          ·
            refine ⟨892607789854423496282041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190143719805897995042721 892607789854423496282041)
            ·
              refine ⟨669455842390817622211531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892607789854423496282041 669455842390817622211531)
              ·
                refine ⟨1004183763586226433317297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669455842390817622211531 1004183763586226433317297)
                ·
                  refine ⟨753137822689669824987973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1004183763586226433317297 753137822689669824987973)
                  ·
                    refine ⟨141213341754313092185245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753137822689669824987973 141213341754313092185245)
                    ·
                      rfl

theorem cell23_825036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_825036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825036 prefixEnd_825036 := by exact prefixLift 825036
  have htrace : WordTrace (prefixWord ++ tailWord_825036) baseStart_825036 baseEnd_825036 := by
    simpa [prefixWord, tailWord_825036, baseEnd_825036] using wordTrace_append hprefix tailTrace_825036
  have hstable : (prefixWord ++ tailWord_825036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825036).length < 2 ^ (prefixWord ++ tailWord_825036).sum := by decide
  have hdescent : baseEnd_825036 < baseStart_825036 := by decide
  rcases family_descends (prefixWord ++ tailWord_825036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825046 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_825046 : Nat := 118140960795 + 825046 * 2 ^ 59
def prefixEnd_825046 : Nat := 4983230072969 + 3 ^ 40 * 825046 * 2
def baseEnd_825046 : Nat := 423645160069484237430689

theorem tailTrace_825046 : CollatzResearch.WordTrace tailWord_825046 prefixEnd_825046 423645160069484237430689 := by
  unfold tailWord_825046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880743735562920217734937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20061266512671148989172661 1880743735562920217734937)
  ·
    refine ⟨1410557801672190163301203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1880743735562920217734937 1410557801672190163301203)
    ·
      refine ⟨2115836702508285244951805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410557801672190163301203 2115836702508285244951805)
      ·
        refine ⟨793438763440606966856927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2115836702508285244951805 793438763440606966856927)
        ·
          refine ⟨1190158145160910450285391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793438763440606966856927 1190158145160910450285391)
          ·
            refine ⟨1785237217741365675428087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190158145160910450285391 1785237217741365675428087)
            ·
              refine ⟨2677855826612048513142131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785237217741365675428087 2677855826612048513142131)
              ·
                refine ⟨4016783739918072769713197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677855826612048513142131 4016783739918072769713197)
                ·
                  refine ⟨1506293902469277288642449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4016783739918072769713197 1506293902469277288642449)
                  ·
                    refine ⟨1129720426851957966481837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1506293902469277288642449 1129720426851957966481837)
                    ·
                      refine ⟨423645160069484237430689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129720426851957966481837 423645160069484237430689)
                      ·
                        rfl

theorem cell23_825046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_825046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825046 prefixEnd_825046 := by exact prefixLift 825046
  have htrace : WordTrace (prefixWord ++ tailWord_825046) baseStart_825046 baseEnd_825046 := by
    simpa [prefixWord, tailWord_825046, baseEnd_825046] using wordTrace_append hprefix tailTrace_825046
  have hstable : (prefixWord ++ tailWord_825046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825046).length < 2 ^ (prefixWord ++ tailWord_825046).sum := by decide
  have hdescent : baseEnd_825046 < baseStart_825046 := by decide
  rcases family_descends (prefixWord ++ tailWord_825046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825099 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 2, 2, 2]
def baseStart_825099 : Nat := 118140960795 + 825099 * 2 ^ 59
def prefixEnd_825099 : Nat := 4983230072969 + 3 ^ 40 * 825099 * 2
def baseEnd_825099 : Nat := 423672374544172530067945

theorem tailTrace_825099 : CollatzResearch.WordTrace tailWord_825099 prefixEnd_825099 423672374544172530067945 := by
  unfold tailWord_825099
  simp only [CollatzResearch.WordTrace]
  refine ⟨30093832837814713535438351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20062555225209809023625567 30093832837814713535438351)
  ·
    refine ⟨45140749256722070303157527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30093832837814713535438351 45140749256722070303157527)
    ·
      refine ⟨67711123885083105454736291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45140749256722070303157527 67711123885083105454736291)
      ·
        refine ⟨101566685827624658182104437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67711123885083105454736291 101566685827624658182104437)
        ·
          refine ⟨9521876796339811704572291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101566685827624658182104437 9521876796339811704572291)
          ·
            refine ⟨14282815194509717556858437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9521876796339811704572291 14282815194509717556858437)
            ·
              refine ⟨2678027848970572041910957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14282815194509717556858437 2678027848970572041910957)
              ·
                refine ⟨1004260443363964515716609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2678027848970572041910957 1004260443363964515716609)
                ·
                  refine ⟨753195332522973386787457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1004260443363964515716609 753195332522973386787457)
                  ·
                    refine ⟨564896499392230040090593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 753195332522973386787457 564896499392230040090593)
                    ·
                      refine ⟨423672374544172530067945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 564896499392230040090593 423672374544172530067945)
                      ·
                        rfl

theorem cell23_825099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 2, 2].length) (baseStart_825099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825099 prefixEnd_825099 := by exact prefixLift 825099
  have htrace : WordTrace (prefixWord ++ tailWord_825099) baseStart_825099 baseEnd_825099 := by
    simpa [prefixWord, tailWord_825099, baseEnd_825099] using wordTrace_append hprefix tailTrace_825099
  have hstable : (prefixWord ++ tailWord_825099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825099).length < 2 ^ (prefixWord ++ tailWord_825099).sum := by decide
  have hdescent : baseEnd_825099 < baseStart_825099 := by decide
  rcases family_descends (prefixWord ++ tailWord_825099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825155 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4]
def baseStart_825155 : Nat := 118140960795 + 825155 * 2 ^ 59
def prefixEnd_825155 : Nat := 4983230072969 + 3 ^ 40 * 825155 * 2
def baseEnd_825155 : Nat := 423701129460824310967687

theorem tailTrace_825155 : CollatzResearch.WordTrace tailWord_825155 prefixEnd_825155 423701129460824310967687 := by
  unfold tailWord_825155
  simp only [CollatzResearch.WordTrace]
  refine ⟨30095875325611835099476919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20063916883741223399651279 30095875325611835099476919)
  ·
    refine ⟨45143812988417752649215379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30095875325611835099476919 45143812988417752649215379)
    ·
      refine ⟨67715719482626628973823069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45143812988417752649215379 67715719482626628973823069)
      ·
        refine ⟨25393394805984985865183651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67715719482626628973823069 25393394805984985865183651)
        ·
          refine ⟨38090092208977478797775477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25393394805984985865183651 38090092208977478797775477)
          ·
            refine ⟨3570946144591638637291451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38090092208977478797775477 3570946144591638637291451)
            ·
              refine ⟨5356419216887457955937177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570946144591638637291451 5356419216887457955937177)
              ·
                refine ⟨4017314412665593466952883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5356419216887457955937177 4017314412665593466952883)
                ·
                  refine ⟨6025971618998390200429325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017314412665593466952883 6025971618998390200429325)
                  ·
                    refine ⟨2259739357124396325160997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6025971618998390200429325 2259739357124396325160997)
                    ·
                      refine ⟨423701129460824310967687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2259739357124396325160997 423701129460824310967687)
                      ·
                        rfl

theorem cell23_825155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_825155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825155 prefixEnd_825155 := by exact prefixLift 825155
  have htrace : WordTrace (prefixWord ++ tailWord_825155) baseStart_825155 baseEnd_825155 := by
    simpa [prefixWord, tailWord_825155, baseEnd_825155] using wordTrace_append hprefix tailTrace_825155
  have hstable : (prefixWord ++ tailWord_825155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825155).length < 2 ^ (prefixWord ++ tailWord_825155).sum := by decide
  have hdescent : baseEnd_825155 < baseStart_825155 := by decide
  rcases family_descends (prefixWord ++ tailWord_825155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825172 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_825172 : Nat := 118140960795 + 825172 * 2 ^ 59
def prefixEnd_825172 : Nat := 4983230072969 + 3 ^ 40 * 825172 * 2
def baseEnd_825172 : Nat := 423709858631950744455109

theorem tailTrace_825172 : CollatzResearch.WordTrace tailWord_825172 prefixEnd_825172 423709858631950744455109 := by
  unfold tailWord_825172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15048247683275123501422885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20064330244366831335230513 15048247683275123501422885)
  ·
    refine ⟨2821546440614085656516791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15048247683275123501422885 2821546440614085656516791)
    ·
      refine ⟨4232319660921128484775187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821546440614085656516791 4232319660921128484775187)
      ·
        refine ⟨6348479491381692727162781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4232319660921128484775187 6348479491381692727162781)
        ·
          refine ⟨2380679809268134772686043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6348479491381692727162781 2380679809268134772686043)
          ·
            refine ⟨3571019713902202159029065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380679809268134772686043 3571019713902202159029065)
            ·
              refine ⟨2678264785426651619271799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3571019713902202159029065 2678264785426651619271799)
              ·
                refine ⟨4017397178139977428907699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678264785426651619271799 4017397178139977428907699)
                ·
                  refine ⟨6026095767209966143361549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4017397178139977428907699 6026095767209966143361549)
                  ·
                    refine ⟨2259785912703737303760581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6026095767209966143361549 2259785912703737303760581)
                    ·
                      refine ⟨423709858631950744455109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2259785912703737303760581 423709858631950744455109)
                      ·
                        rfl

theorem cell23_825172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_825172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825172 prefixEnd_825172 := by exact prefixLift 825172
  have htrace : WordTrace (prefixWord ++ tailWord_825172) baseStart_825172 baseEnd_825172 := by
    simpa [prefixWord, tailWord_825172, baseEnd_825172] using wordTrace_append hprefix tailTrace_825172
  have hstable : (prefixWord ++ tailWord_825172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825172).length < 2 ^ (prefixWord ++ tailWord_825172).sum := by decide
  have hdescent : baseEnd_825172 < baseStart_825172 := by decide
  rcases family_descends (prefixWord ++ tailWord_825172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825195 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 6]
def baseStart_825195 : Nat := 118140960795 + 825195 * 2 ^ 59
def prefixEnd_825195 : Nat := 4983230072969 + 3 ^ 40 * 825195 * 2
def baseEnd_825195 : Nat := 47080185409667128274167

theorem tailTrace_825195 : CollatzResearch.WordTrace tailWord_825195 prefixEnd_825195 47080185409667128274167 := by
  unfold tailWord_825195
  simp only [CollatzResearch.WordTrace]
  refine ⟨30097334245466921930933039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20064889496977947953955359 30097334245466921930933039)
  ·
    refine ⟨45146001368200382896399559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30097334245466921930933039 45146001368200382896399559)
    ·
      refine ⟨67719002052300574344599339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45146001368200382896399559 67719002052300574344599339)
      ·
        refine ⟨101578503078450861516899009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67719002052300574344599339 101578503078450861516899009)
        ·
          refine ⟨76183877308838146137674257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101578503078450861516899009 76183877308838146137674257)
          ·
            refine ⟨57137907981628609603255693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76183877308838146137674257 57137907981628609603255693)
            ·
              refine ⟨21426715493110728601220885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57137907981628609603255693 21426715493110728601220885)
              ·
                refine ⟨1004377288739565403182229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21426715493110728601220885 1004377288739565403182229)
                ·
                  refine ⟨47080185409667128274167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1004377288739565403182229 47080185409667128274167)
                  ·
                    rfl

theorem cell23_825195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 6].length) (baseStart_825195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825195 prefixEnd_825195 := by exact prefixLift 825195
  have htrace : WordTrace (prefixWord ++ tailWord_825195) baseStart_825195 baseEnd_825195 := by
    simpa [prefixWord, tailWord_825195, baseEnd_825195] using wordTrace_append hprefix tailTrace_825195
  have hstable : (prefixWord ++ tailWord_825195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825195).length < 2 ^ (prefixWord ++ tailWord_825195).sum := by decide
  have hdescent : baseEnd_825195 < baseStart_825195 := by decide
  rcases family_descends (prefixWord ++ tailWord_825195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825226 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_825226 : Nat := 118140960795 + 825226 * 2 ^ 59
def prefixEnd_825226 : Nat := 4983230072969 + 3 ^ 40 * 825226 * 2
def baseEnd_825226 : Nat := 423737586587293533179861

theorem tailTrace_825226 : CollatzResearch.WordTrace tailWord_825226 prefixEnd_825226 423737586587293533179861 := by
  unfold tailWord_825226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524616227088653556327883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20065643272236409483541021 7524616227088653556327883)
  ·
    refine ⟨11286924340632980334491825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7524616227088653556327883 11286924340632980334491825)
    ·
      refine ⟨8465193255474735250868869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11286924340632980334491825 8465193255474735250868869)
      ·
        refine ⟨1587223735401512859537913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8465193255474735250868869 1587223735401512859537913)
        ·
          refine ⟨1190417801551134644653435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587223735401512859537913 1190417801551134644653435)
          ·
            refine ⟨1785626702326701966980153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190417801551134644653435 1785626702326701966980153)
            ·
              refine ⟨1339220026745026475235115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785626702326701966980153 1339220026745026475235115)
              ·
                refine ⟨2008830040117539712852673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339220026745026475235115 2008830040117539712852673)
                ·
                  refine ⟨1506622530088154784639505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2008830040117539712852673 1506622530088154784639505)
                  ·
                    refine ⟨1129966897566116088479629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1506622530088154784639505 1129966897566116088479629)
                    ·
                      refine ⟨423737586587293533179861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1129966897566116088479629 423737586587293533179861)
                      ·
                        rfl

theorem cell23_825226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_825226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825226 prefixEnd_825226 := by exact prefixLift 825226
  have htrace : WordTrace (prefixWord ++ tailWord_825226) baseStart_825226 baseEnd_825226 := by
    simpa [prefixWord, tailWord_825226, baseEnd_825226] using wordTrace_append hprefix tailTrace_825226
  have hstable : (prefixWord ++ tailWord_825226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825226).length < 2 ^ (prefixWord ++ tailWord_825226).sum := by decide
  have hdescent : baseEnd_825226 < baseStart_825226 := by decide
  rcases family_descends (prefixWord ++ tailWord_825226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825250 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_825250 : Nat := 118140960795 + 825250 * 2 ^ 59
def prefixEnd_825250 : Nat := 4983230072969 + 3 ^ 40 * 825250 * 2
def baseEnd_825250 : Nat := 141249970041000479759917

theorem tailTrace_825250 : CollatzResearch.WordTrace tailWord_825250 prefixEnd_825250 141249970041000479759917 := by
  unfold tailWord_825250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524835065066916581046301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20066226840178444216123469 7524835065066916581046301)
  ·
    refine ⟨2821813149400093717892363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7524835065066916581046301 2821813149400093717892363)
    ·
      refine ⟨4232719724100140576838545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821813149400093717892363 4232719724100140576838545)
      ·
        refine ⟨3174539793075105432628909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4232719724100140576838545 3174539793075105432628909)
        ·
          refine ⟨1190452422403164537235841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3174539793075105432628909 1190452422403164537235841)
          ·
            refine ⟨892839316802373402926881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190452422403164537235841 892839316802373402926881)
            ·
              refine ⟨669629487601780052195161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892839316802373402926881 669629487601780052195161)
              ·
                refine ⟨502222115701335039146371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669629487601780052195161 502222115701335039146371)
                ·
                  refine ⟨753333173552002558719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502222115701335039146371 753333173552002558719557)
                  ·
                    refine ⟨141249970041000479759917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753333173552002558719557 141249970041000479759917)
                    ·
                      rfl

theorem cell23_825250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_825250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825250 prefixEnd_825250 := by exact prefixLift 825250
  have htrace : WordTrace (prefixWord ++ tailWord_825250) baseStart_825250 baseEnd_825250 := by
    simpa [prefixWord, tailWord_825250, baseEnd_825250] using wordTrace_append hprefix tailTrace_825250
  have hstable : (prefixWord ++ tailWord_825250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825250).length < 2 ^ (prefixWord ++ tailWord_825250).sum := by decide
  have hdescent : baseEnd_825250 < baseStart_825250 := by decide
  rcases family_descends (prefixWord ++ tailWord_825250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825272 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 1, 6]
def baseStart_825272 : Nat := 118140960795 + 825272 * 2 ^ 59
def prefixEnd_825272 : Nat := 4983230072969 + 3 ^ 40 * 825272 * 2
def baseEnd_825272 : Nat := 141253735565800117734883

theorem tailTrace_825272 : CollatzResearch.WordTrace tailWord_825272 prefixEnd_825272 141253735565800117734883 := by
  unfold tailWord_825272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050071333093982040743035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20066761777458642720990713 15050071333093982040743035)
  ·
    refine ⟨22575106999640973061114553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15050071333093982040743035 22575106999640973061114553)
    ·
      refine ⟨16931330249730729795835915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22575106999640973061114553 16931330249730729795835915)
      ·
        refine ⟨25396995374596094693753873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16931330249730729795835915 25396995374596094693753873)
        ·
          refine ⟨19047746530947071020315405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25396995374596094693753873 19047746530947071020315405)
          ·
            refine ⟨7142904949105151632618277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19047746530947071020315405 7142904949105151632618277)
            ·
              refine ⟨1339294677957215931115927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7142904949105151632618277 1339294677957215931115927)
              ·
                refine ⟨2008942016935823896673891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339294677957215931115927 2008942016935823896673891)
                ·
                  refine ⟨3013413025403735845010837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008942016935823896673891 3013413025403735845010837)
                  ·
                    refine ⟨141253735565800117734883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3013413025403735845010837 141253735565800117734883)
                    ·
                      rfl

theorem cell23_825272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_825272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825272 prefixEnd_825272 := by exact prefixLift 825272
  have htrace : WordTrace (prefixWord ++ tailWord_825272) baseStart_825272 baseEnd_825272 := by
    simpa [prefixWord, tailWord_825272, baseEnd_825272] using wordTrace_append hprefix tailTrace_825272
  have hstable : (prefixWord ++ tailWord_825272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825272).length < 2 ^ (prefixWord ++ tailWord_825272).sum := by decide
  have hdescent : baseEnd_825272 < baseStart_825272 := by decide
  rcases family_descends (prefixWord ++ tailWord_825272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825312 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_825312 : Nat := 118140960795 + 825312 * 2 ^ 59
def prefixEnd_825312 : Nat := 4983230072969 + 3 ^ 40 * 825312 * 2
def baseEnd_825312 : Nat := 423781745923580196704465

theorem tailTrace_825312 : CollatzResearch.WordTrace tailWord_825312 prefixEnd_825312 423781745923580196704465 := by
  unfold tailWord_825312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050800793021525456471095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20067734390695367275294793 15050800793021525456471095)
  ·
    refine ⟨22576201189532288184706643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15050800793021525456471095 22576201189532288184706643)
    ·
      refine ⟨33864301784298432277059965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22576201189532288184706643 33864301784298432277059965)
      ·
        refine ⟨12699113169111912103897487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33864301784298432277059965 12699113169111912103897487)
        ·
          refine ⟨19048669753667868155846231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12699113169111912103897487 19048669753667868155846231)
          ·
            refine ⟨28573004630501802233769347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19048669753667868155846231 28573004630501802233769347)
            ·
              refine ⟨42859506945752703350654021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28573004630501802233769347 42859506945752703350654021)
              ·
                refine ⟨8036157552328631878247629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42859506945752703350654021 8036157552328631878247629)
                ·
                  refine ⟨3013559082123236954342861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8036157552328631878247629 3013559082123236954342861)
                  ·
                    refine ⟨1130084655796213857878573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3013559082123236954342861 1130084655796213857878573)
                    ·
                      refine ⟨423781745923580196704465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130084655796213857878573 423781745923580196704465)
                      ·
                        rfl

theorem cell23_825312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_825312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825312 prefixEnd_825312 := by exact prefixLift 825312
  have htrace : WordTrace (prefixWord ++ tailWord_825312) baseStart_825312 baseEnd_825312 := by
    simpa [prefixWord, tailWord_825312, baseEnd_825312] using wordTrace_append hprefix tailTrace_825312
  have hstable : (prefixWord ++ tailWord_825312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825312).length < 2 ^ (prefixWord ++ tailWord_825312).sum := by decide
  have hdescent : baseEnd_825312 < baseStart_825312 := by decide
  rcases family_descends (prefixWord ++ tailWord_825312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825313 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 1, 2, 2]
def baseStart_825313 : Nat := 118140960795 + 825313 * 2 ^ 59
def prefixEnd_825313 : Nat := 4983230072969 + 3 ^ 40 * 825313 * 2
def baseEnd_825313 : Nat := 423782259404234692791961

theorem tailTrace_825313 : CollatzResearch.WordTrace tailWord_825313 prefixEnd_825313 423782259404234692791961 := by
  unfold tailWord_825313
  simp only [CollatzResearch.WordTrace]
  refine ⟨30101638059039428083728593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20067758706026285389152395 30101638059039428083728593)
  ·
    refine ⟨22576228544279571062796445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30101638059039428083728593 22576228544279571062796445)
    ·
      refine ⟨8466085704104839148548667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22576228544279571062796445 8466085704104839148548667)
      ·
        refine ⟨12699128556157258722823001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8466085704104839148548667 12699128556157258722823001)
        ·
          refine ⟨9524346417117944042117251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12699128556157258722823001 9524346417117944042117251)
          ·
            refine ⟨14286519625676916063175877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9524346417117944042117251 14286519625676916063175877)
            ·
              refine ⟨2678722429814421761845477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14286519625676916063175877 2678722429814421761845477)
              ·
                refine ⟨502260455590204080346027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2678722429814421761845477 502260455590204080346027)
                ·
                  refine ⟨753390683385306120519041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502260455590204080346027 753390683385306120519041)
                  ·
                    refine ⟨565043012538979590389281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 753390683385306120519041 565043012538979590389281)
                    ·
                      refine ⟨423782259404234692791961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565043012538979590389281 423782259404234692791961)
                      ·
                        rfl

theorem cell23_825313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_825313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825313 prefixEnd_825313 := by exact prefixLift 825313
  have htrace : WordTrace (prefixWord ++ tailWord_825313) baseStart_825313 baseEnd_825313 := by
    simpa [prefixWord, tailWord_825313, baseEnd_825313] using wordTrace_append hprefix tailTrace_825313
  have hstable : (prefixWord ++ tailWord_825313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825313).length < 2 ^ (prefixWord ++ tailWord_825313).sum := by decide
  have hdescent : baseEnd_825313 < baseStart_825313 := by decide
  rcases family_descends (prefixWord ++ tailWord_825313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825326 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_825326 : Nat := 118140960795 + 825326 * 2 ^ 59
def prefixEnd_825326 : Nat := 4983230072969 + 3 ^ 40 * 825326 * 2
def baseEnd_825326 : Nat := 423788934652743141929401

theorem tailTrace_825326 : CollatzResearch.WordTrace tailWord_825326 prefixEnd_825326 423788934652743141929401 := by
  unfold tailWord_825326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3762764025999041412993979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20068074805328220869301221 3762764025999041412993979)
  ·
    refine ⟨5644146038998562119490969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3762764025999041412993979 5644146038998562119490969)
    ·
      refine ⟨4233109529248921589618227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5644146038998562119490969 4233109529248921589618227)
      ·
        refine ⟨6349664293873382384427341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233109529248921589618227 6349664293873382384427341)
        ·
          refine ⟨2381124110202518394160253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6349664293873382384427341 2381124110202518394160253)
          ·
            refine ⟨892921541325944397810095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2381124110202518394160253 892921541325944397810095)
            ·
              refine ⟨1339382311988916596715143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892921541325944397810095 1339382311988916596715143)
              ·
                refine ⟨2009073467983374895072715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339382311988916596715143 2009073467983374895072715)
                ·
                  refine ⟨3013610201975062342609073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009073467983374895072715 3013610201975062342609073)
                  ·
                    refine ⟨2260207651481296756956805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3013610201975062342609073 2260207651481296756956805)
                    ·
                      refine ⟨423788934652743141929401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2260207651481296756956805 423788934652743141929401)
                      ·
                        rfl

theorem cell23_825326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_825326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825326 prefixEnd_825326 := by exact prefixLift 825326
  have htrace : WordTrace (prefixWord ++ tailWord_825326) baseStart_825326 baseEnd_825326 := by
    simpa [prefixWord, tailWord_825326, baseEnd_825326] using wordTrace_append hprefix tailTrace_825326
  have hstable : (prefixWord ++ tailWord_825326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825326).length < 2 ^ (prefixWord ++ tailWord_825326).sum := by decide
  have hdescent : baseEnd_825326 < baseStart_825326 := by decide
  rcases family_descends (prefixWord ++ tailWord_825326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825339 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 3, 3, 2]
def baseStart_825339 : Nat := 118140960795 + 825339 * 2 ^ 59
def prefixEnd_825339 : Nat := 4983230072969 + 3 ^ 40 * 825339 * 2
def baseEnd_825339 : Nat := 423795609901251591066841

theorem tailTrace_825339 : CollatzResearch.WordTrace tailWord_825339 prefixEnd_825339 423795609901251591066841 := by
  unfold tailWord_825339
  simp only [CollatzResearch.WordTrace]
  refine ⟨30102586356945234524175071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20068390904630156349450047 30102586356945234524175071)
  ·
    refine ⟨45153879535417851786262607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30102586356945234524175071 45153879535417851786262607)
    ·
      refine ⟨67730819303126777679393911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45153879535417851786262607 67730819303126777679393911)
      ·
        refine ⟨101596228954690166519090867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67730819303126777679393911 101596228954690166519090867)
        ·
          refine ⟨152394343432035249778636301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101596228954690166519090867 152394343432035249778636301)
          ·
            refine ⟨57147878787013218666988613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152394343432035249778636301 57147878787013218666988613)
            ·
              refine ⟨10715227272564978500060365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57147878787013218666988613 10715227272564978500060365)
              ·
                refine ⟨4018210227211866937522637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10715227272564978500060365 4018210227211866937522637)
                ·
                  refine ⟨1506828835204450101570989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4018210227211866937522637 1506828835204450101570989)
                  ·
                    refine ⟨565060813201668788089121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506828835204450101570989 565060813201668788089121)
                    ·
                      refine ⟨423795609901251591066841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565060813201668788089121 423795609901251591066841)
                      ·
                        rfl

theorem cell23_825339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3, 2].length) (baseStart_825339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825339 prefixEnd_825339 := by exact prefixLift 825339
  have htrace : WordTrace (prefixWord ++ tailWord_825339) baseStart_825339 baseEnd_825339 := by
    simpa [prefixWord, tailWord_825339, baseEnd_825339] using wordTrace_append hprefix tailTrace_825339
  have hstable : (prefixWord ++ tailWord_825339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825339).length < 2 ^ (prefixWord ++ tailWord_825339).sum := by decide
  have hdescent : baseEnd_825339 < baseStart_825339 := by decide
  rcases family_descends (prefixWord ++ tailWord_825339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825356 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 1, 3, 2]
def baseStart_825356 : Nat := 118140960795 + 825356 * 2 ^ 59
def prefixEnd_825356 : Nat := 4983230072969 + 3 ^ 40 * 825356 * 2
def baseEnd_825356 : Nat := 423804339072378024554263

theorem tailTrace_825356 : CollatzResearch.WordTrace tailWord_825356 prefixEnd_825356 423804339072378024554263 := by
  unfold tailWord_825356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15051603198941823213771961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20068804265255764285029281 15051603198941823213771961)
  ·
    refine ⟨11288702399206367410328971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15051603198941823213771961 11288702399206367410328971)
    ·
      refine ⟨16933053598809551115493457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11288702399206367410328971 16933053598809551115493457)
      ·
        refine ⟨12699790199107163336620093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16933053598809551115493457 12699790199107163336620093)
        ·
          refine ⟨4762421324665186251232535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12699790199107163336620093 4762421324665186251232535)
          ·
            refine ⟨7143631986997779376848803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4762421324665186251232535 7143631986997779376848803)
            ·
              refine ⟨10715447980496669065273205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143631986997779376848803 10715447980496669065273205)
              ·
                refine ⟨1004573248171562724869363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10715447980496669065273205 1004573248171562724869363)
                ·
                  refine ⟨1506859872257344087304045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004573248171562724869363 1506859872257344087304045)
                  ·
                    refine ⟨565072452096504032739017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506859872257344087304045 565072452096504032739017)
                    ·
                      refine ⟨423804339072378024554263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565072452096504032739017 423804339072378024554263)
                      ·
                        rfl

theorem cell23_825356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_825356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825356 prefixEnd_825356 := by exact prefixLift 825356
  have htrace : WordTrace (prefixWord ++ tailWord_825356) baseStart_825356 baseEnd_825356 := by
    simpa [prefixWord, tailWord_825356, baseEnd_825356] using wordTrace_append hprefix tailTrace_825356
  have hstable : (prefixWord ++ tailWord_825356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825356).length < 2 ^ (prefixWord ++ tailWord_825356).sum := by decide
  have hdescent : baseEnd_825356 < baseStart_825356 := by decide
  rcases family_descends (prefixWord ++ tailWord_825356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825364 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_825364 : Nat := 118140960795 + 825364 * 2 ^ 59
def prefixEnd_825364 : Nat := 4983230072969 + 3 ^ 40 * 825364 * 2
def baseEnd_825364 : Nat := 423808446917613993254227

theorem tailTrace_825364 : CollatzResearch.WordTrace tailWord_825364 prefixEnd_825364 423808446917613993254227 := by
  unfold tailWord_825364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15051749090927331896917573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20068998787903109195890097 15051749090927331896917573)
  ·
    refine ⟨2822202954548874730672045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15051749090927331896917573 2822202954548874730672045)
    ·
      refine ⟨1058326107955828024002017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2822202954548874730672045 1058326107955828024002017)
      ·
        refine ⟨793744580966871018001513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058326107955828024002017 793744580966871018001513)
        ·
          refine ⟨595308435725153263501135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793744580966871018001513 595308435725153263501135)
          ·
            refine ⟨892962653587729895251703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595308435725153263501135 892962653587729895251703)
            ·
              refine ⟨1339443980381594842877555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892962653587729895251703 1339443980381594842877555)
              ·
                refine ⟨2009165970572392264316333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339443980381594842877555 2009165970572392264316333)
                ·
                  refine ⟨753437238964647099118625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2009165970572392264316333 753437238964647099118625)
                  ·
                    refine ⟨565077929223485324338969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 753437238964647099118625 565077929223485324338969)
                    ·
                      refine ⟨423808446917613993254227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565077929223485324338969 423808446917613993254227)
                      ·
                        rfl

theorem cell23_825364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_825364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825364 prefixEnd_825364 := by exact prefixLift 825364
  have htrace : WordTrace (prefixWord ++ tailWord_825364) baseStart_825364 baseEnd_825364 := by
    simpa [prefixWord, tailWord_825364, baseEnd_825364] using wordTrace_append hprefix tailTrace_825364
  have hstable : (prefixWord ++ tailWord_825364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825364).length < 2 ^ (prefixWord ++ tailWord_825364).sum := by decide
  have hdescent : baseEnd_825364 < baseStart_825364 := by decide
  rcases family_descends (prefixWord ++ tailWord_825364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825390 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_825390 : Nat := 118140960795 + 825390 * 2 ^ 59
def prefixEnd_825390 : Nat := 4983230072969 + 3 ^ 40 * 825390 * 2
def baseEnd_825390 : Nat := 423821797414630891529107

theorem tailTrace_825390 : CollatzResearch.WordTrace tailWord_825390 prefixEnd_825390 423821797414630891529107 := by
  unfold tailWord_825390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763055809970058779285203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20069630986506980156187749 3763055809970058779285203)
  ·
    refine ⟨5644583714955088168927805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3763055809970058779285203 5644583714955088168927805)
    ·
      refine ⟨2116718893108158063347927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5644583714955088168927805 2116718893108158063347927)
      ·
        refine ⟨3175078339662237095021891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116718893108158063347927 3175078339662237095021891)
        ·
          refine ⟨4762617509493355642532837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175078339662237095021891 4762617509493355642532837)
          ·
            refine ⟨892990783030004182974907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4762617509493355642532837 892990783030004182974907)
            ·
              refine ⟨1339486174545006274462361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892990783030004182974907 1339486174545006274462361)
              ·
                refine ⟨1004614630908754705846771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339486174545006274462361 1004614630908754705846771)
                ·
                  refine ⟨1506921946363132058770157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004614630908754705846771 1506921946363132058770157)
                  ·
                    refine ⟨565095729886174522038809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1506921946363132058770157 565095729886174522038809)
                    ·
                      refine ⟨423821797414630891529107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565095729886174522038809 423821797414630891529107)
                      ·
                        rfl

theorem cell23_825390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_825390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825390 prefixEnd_825390 := by exact prefixLift 825390
  have htrace : WordTrace (prefixWord ++ tailWord_825390) baseStart_825390 baseEnd_825390 := by
    simpa [prefixWord, tailWord_825390, baseEnd_825390] using wordTrace_append hprefix tailTrace_825390
  have hstable : (prefixWord ++ tailWord_825390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825390).length < 2 ^ (prefixWord ++ tailWord_825390).sum := by decide
  have hdescent : baseEnd_825390 < baseStart_825390 := by decide
  rcases family_descends (prefixWord ++ tailWord_825390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825436 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_825436 : Nat := 118140960795 + 825436 * 2 ^ 59
def prefixEnd_825436 : Nat := 4983230072969 + 3 ^ 40 * 825436 * 2
def baseEnd_825436 : Nat := 423845417524737711553895

theorem tailTrace_825436 : CollatzResearch.WordTrace tailWord_825436 prefixEnd_825436 423845417524737711553895 := by
  unfold tailWord_825436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053062118796910045228081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20070749491729213393637441 15053062118796910045228081)
  ·
    refine ⟨11289796589097682533921061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15053062118796910045228081 11289796589097682533921061)
    ·
      refine ⟨2116836860455815475110199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11289796589097682533921061 2116836860455815475110199)
      ·
        refine ⟨3175255290683723212665299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116836860455815475110199 3175255290683723212665299)
        ·
          refine ⟨4762882936025584818997949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175255290683723212665299 4762882936025584818997949)
          ·
            refine ⟨1786081101009594307124231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4762882936025584818997949 1786081101009594307124231)
            ·
              refine ⟨2679121651514391460686347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786081101009594307124231 2679121651514391460686347)
              ·
                refine ⟨4018682477271587191029521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679121651514391460686347 4018682477271587191029521)
                ·
                  refine ⟨3014011857953690393272141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018682477271587191029521 3014011857953690393272141)
                  ·
                    refine ⟨1130254446732633897477053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014011857953690393272141 1130254446732633897477053)
                    ·
                      refine ⟨423845417524737711553895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130254446732633897477053 423845417524737711553895)
                      ·
                        rfl

theorem cell23_825436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_825436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825436 prefixEnd_825436 := by exact prefixLift 825436
  have htrace : WordTrace (prefixWord ++ tailWord_825436) baseStart_825436 baseEnd_825436 := by
    simpa [prefixWord, tailWord_825436, baseEnd_825436] using wordTrace_append hprefix tailTrace_825436
  have hstable : (prefixWord ++ tailWord_825436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825436).length < 2 ^ (prefixWord ++ tailWord_825436).sum := by decide
  have hdescent : baseEnd_825436 < baseStart_825436 := by decide
  rcases family_descends (prefixWord ++ tailWord_825436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825456 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 2, 5]
def baseStart_825456 : Nat := 118140960795 + 825456 * 2 ^ 59
def prefixEnd_825456 : Nat := 4983230072969 + 3 ^ 40 * 825456 * 2
def baseEnd_825456 : Nat := 141285229045942544434601

theorem tailTrace_825456 : CollatzResearch.WordTrace tailWord_825456 prefixEnd_825456 141285229045942544434601 := by
  unfold tailWord_825456
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053426848760681753092111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20071235798347575670789481 15053426848760681753092111)
  ·
    refine ⟨22580140273141022629638167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15053426848760681753092111 22580140273141022629638167)
    ·
      refine ⟨33870210409711533944457251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22580140273141022629638167 33870210409711533944457251)
      ·
        refine ⟨50805315614567300916685877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33870210409711533944457251 50805315614567300916685877)
        ·
          refine ⟨4762998338865684460939301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50805315614567300916685877 4762998338865684460939301)
          ·
            refine ⟨893062188537315836426119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4762998338865684460939301 893062188537315836426119)
            ·
              refine ⟨1339593282805973754639179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893062188537315836426119 1339593282805973754639179)
              ·
                refine ⟨2009389924208960631958769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339593282805973754639179 2009389924208960631958769)
                ·
                  refine ⟨1507042443156720473969077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2009389924208960631958769 1507042443156720473969077)
                  ·
                    refine ⟨141285229045942544434601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1507042443156720473969077 141285229045942544434601)
                    ·
                      rfl

theorem cell23_825456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_825456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825456 prefixEnd_825456 := by exact prefixLift 825456
  have htrace : WordTrace (prefixWord ++ tailWord_825456) baseStart_825456 baseEnd_825456 := by
    simpa [prefixWord, tailWord_825456, baseEnd_825456] using wordTrace_append hprefix tailTrace_825456
  have hstable : (prefixWord ++ tailWord_825456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825456).length < 2 ^ (prefixWord ++ tailWord_825456).sum := by decide
  have hdescent : baseEnd_825456 < baseStart_825456 := by decide
  rcases family_descends (prefixWord ++ tailWord_825456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825476 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_825476 : Nat := 118140960795 + 825476 * 2 ^ 59
def prefixEnd_825476 : Nat := 4983230072969 + 3 ^ 40 * 825476 * 2
def baseEnd_825476 : Nat := 423865956750917555053711

theorem tailTrace_825476 : CollatzResearch.WordTrace tailWord_825476 prefixEnd_825476 423865956750917555053711 := by
  unfold tailWord_825476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15053791578724453460956141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20071722104965937947941521 15053791578724453460956141)
  ·
    refine ⟨5645171842021670047858553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15053791578724453460956141 5645171842021670047858553)
    ·
      refine ⟨4233878881516252535893915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5645171842021670047858553 4233878881516252535893915)
      ·
        refine ⟨6350818322274378803840873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233878881516252535893915 6350818322274378803840873)
        ·
          refine ⟨4763113741705784102880655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6350818322274378803840873 4763113741705784102880655)
          ·
            refine ⟨7144670612558676154320983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763113741705784102880655 7144670612558676154320983)
            ·
              refine ⟨10717005918838014231481475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144670612558676154320983 10717005918838014231481475)
              ·
                refine ⟨16075508878257021347222213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10717005918838014231481475 16075508878257021347222213)
                ·
                  refine ⟨3014157914673191502604165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16075508878257021347222213 3014157914673191502604165)
                  ·
                    refine ⟨565154609001223406738281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3014157914673191502604165 565154609001223406738281)
                    ·
                      refine ⟨423865956750917555053711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565154609001223406738281 423865956750917555053711)
                      ·
                        rfl

theorem cell23_825476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_825476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825476 prefixEnd_825476 := by exact prefixLift 825476
  have htrace : WordTrace (prefixWord ++ tailWord_825476) baseStart_825476 baseEnd_825476 := by
    simpa [prefixWord, tailWord_825476, baseEnd_825476] using wordTrace_append hprefix tailTrace_825476
  have hstable : (prefixWord ++ tailWord_825476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825476).length < 2 ^ (prefixWord ++ tailWord_825476).sum := by decide
  have hdescent : baseEnd_825476 < baseStart_825476 := by decide
  rcases family_descends (prefixWord ++ tailWord_825476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825509 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_825509 : Nat := 118140960795 + 825509 * 2 ^ 59
def prefixEnd_825509 : Nat := 4983230072969 + 3 ^ 40 * 825509 * 2
def baseEnd_825509 : Nat := 423882901612515925941059

theorem tailTrace_825509 : CollatzResearch.WordTrace tailWord_825509 prefixEnd_825509 423882901612515925941059 := by
  unfold tailWord_825509
  simp only [CollatzResearch.WordTrace]
  refine ⟨30108786766329353557863581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20072524510886235705242387 30108786766329353557863581)
  ·
    refine ⟨11290795037373507584198843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30108786766329353557863581 11290795037373507584198843)
    ·
      refine ⟨16936192556060261376298265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11290795037373507584198843 16936192556060261376298265)
      ·
        refine ⟨12702144417045196032223699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16936192556060261376298265 12702144417045196032223699)
        ·
          refine ⟨19053216625567794048335549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12702144417045196032223699 19053216625567794048335549)
          ·
            refine ⟨7144956234587922768125831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19053216625567794048335549 7144956234587922768125831)
            ·
              refine ⟨10717434351881884152188747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144956234587922768125831 10717434351881884152188747)
              ·
                refine ⟨16076151527822826228283121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10717434351881884152188747 16076151527822826228283121)
                ·
                  refine ⟨12057113645867119671212341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16076151527822826228283121 12057113645867119671212341)
                  ·
                    refine ⟨1130354404300042469176157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12057113645867119671212341 1130354404300042469176157)
                    ·
                      refine ⟨423882901612515925941059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130354404300042469176157 423882901612515925941059)
                      ·
                        rfl

theorem cell23_825509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_825509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825509 prefixEnd_825509 := by exact prefixLift 825509
  have htrace : WordTrace (prefixWord ++ tailWord_825509) baseStart_825509 baseEnd_825509 := by
    simpa [prefixWord, tailWord_825509, baseEnd_825509] using wordTrace_append hprefix tailTrace_825509
  have hstable : (prefixWord ++ tailWord_825509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825509).length < 2 ^ (prefixWord ++ tailWord_825509).sum := by decide
  have hdescent : baseEnd_825509 < baseStart_825509 := by decide
  rcases family_descends (prefixWord ++ tailWord_825509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825537 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 3, 4]
def baseStart_825537 : Nat := 118140960795 + 825537 * 2 ^ 59
def prefixEnd_825537 : Nat := 4983230072969 + 3 ^ 40 * 825537 * 2
def baseEnd_825537 : Nat := 141299093023613938796977

theorem tailTrace_825537 : CollatzResearch.WordTrace tailWord_825537 prefixEnd_825537 141299093023613938796977 := by
  unfold tailWord_825537
  simp only [CollatzResearch.WordTrace]
  refine ⟨30109808010227914339882865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20073205340151942893255243 30109808010227914339882865)
  ·
    refine ⟨22582356007670935754912149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30109808010227914339882865 22582356007670935754912149)
    ·
      refine ⟨1058547937859575113511507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22582356007670935754912149 1058547937859575113511507)
      ·
        refine ⟨1587821906789362670267261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058547937859575113511507 1587821906789362670267261)
        ·
          refine ⟨595433215046011001350223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1587821906789362670267261 595433215046011001350223)
          ·
            refine ⟨893149822569016502025335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595433215046011001350223 893149822569016502025335)
            ·
              refine ⟨1339724733853524753038003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893149822569016502025335 1339724733853524753038003)
              ·
                refine ⟨2009587100780287129557005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339724733853524753038003 2009587100780287129557005)
                ·
                  refine ⟨753595162792607673583877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2009587100780287129557005 753595162792607673583877)
                  ·
                    refine ⟨141299093023613938796977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753595162792607673583877 141299093023613938796977)
                    ·
                      rfl

theorem cell23_825537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_825537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825537 prefixEnd_825537 := by exact prefixLift 825537
  have htrace : WordTrace (prefixWord ++ tailWord_825537) baseStart_825537 baseEnd_825537 := by
    simpa [prefixWord, tailWord_825537, baseEnd_825537] using wordTrace_append hprefix tailTrace_825537
  have hstable : (prefixWord ++ tailWord_825537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825537).length < 2 ^ (prefixWord ++ tailWord_825537).sum := by decide
  have hdescent : baseEnd_825537 < baseStart_825537 := by decide
  rcases family_descends (prefixWord ++ tailWord_825537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825559 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 1, 6]
def baseStart_825559 : Nat := 118140960795 + 825559 * 2 ^ 59
def prefixEnd_825559 : Nat := 4983230072969 + 3 ^ 40 * 825559 * 2
def baseEnd_825559 : Nat := 141302858548413576771943

theorem tailTrace_825559 : CollatzResearch.WordTrace tailWord_825559 prefixEnd_825559 141302858548413576771943 := by
  unfold tailWord_825559
  simp only [CollatzResearch.WordTrace]
  refine ⟨30110610416148212097183731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20073740277432141398122487 30110610416148212097183731)
  ·
    refine ⟨45165915624222318145775597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30110610416148212097183731 45165915624222318145775597)
    ·
      refine ⟨16937218359083369304665849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45165915624222318145775597 16937218359083369304665849)
      ·
        refine ⟨12702913769312526978499387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16937218359083369304665849 12702913769312526978499387)
        ·
          refine ⟨19054370653968790467749081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12702913769312526978499387 19054370653968790467749081)
          ·
            refine ⟨14290777990476592850811811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19054370653968790467749081 14290777990476592850811811)
            ·
              refine ⟨21436166985714889276217717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14290777990476592850811811 21436166985714889276217717)
              ·
                refine ⟨2009640654910770869645411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21436166985714889276217717 2009640654910770869645411)
                ·
                  refine ⟨3014460982366156304468117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009640654910770869645411 3014460982366156304468117)
                  ·
                    refine ⟨141302858548413576771943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3014460982366156304468117 141302858548413576771943)
                    ·
                      rfl

theorem cell23_825559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_825559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825559 prefixEnd_825559 := by exact prefixLift 825559
  have htrace : WordTrace (prefixWord ++ tailWord_825559) baseStart_825559 baseEnd_825559 := by
    simpa [prefixWord, tailWord_825559, baseEnd_825559] using wordTrace_append hprefix tailTrace_825559
  have hstable : (prefixWord ++ tailWord_825559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825559).length < 2 ^ (prefixWord ++ tailWord_825559).sum := by decide
  have hdescent : baseEnd_825559 < baseStart_825559 := by decide
  rcases family_descends (prefixWord ++ tailWord_825559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825576 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_825576 : Nat := 118140960795 + 825576 * 2 ^ 59
def prefixEnd_825576 : Nat := 4983230072969 + 3 ^ 40 * 825576 * 2
def baseEnd_825576 : Nat := 141305768272122387934417

theorem tailTrace_825576 : CollatzResearch.WordTrace tailWord_825576 prefixEnd_825576 141305768272122387934417 := by
  unfold tailWord_825576
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055615228543312000276291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20074153638057749333701721 15055615228543312000276291)
  ·
    refine ⟨22583422842814968000414437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055615228543312000276291 22583422842814968000414437)
    ·
      refine ⟨4234391783027806500077707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22583422842814968000414437 4234391783027806500077707)
      ·
        refine ⟨6351587674541709750116561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234391783027806500077707 6351587674541709750116561)
        ·
          refine ⟨4763690755906282312587421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6351587674541709750116561 4763690755906282312587421)
          ·
            refine ⟨1786384033464855867220283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4763690755906282312587421 1786384033464855867220283)
            ·
              refine ⟨2679576050197283800830425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786384033464855867220283 2679576050197283800830425)
              ·
                refine ⟨2009682037647962850622819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679576050197283800830425 2009682037647962850622819)
                ·
                  refine ⟨3014523056471944275934229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009682037647962850622819 3014523056471944275934229)
                  ·
                    refine ⟨141305768272122387934417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3014523056471944275934229 141305768272122387934417)
                    ·
                      rfl

theorem cell23_825576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_825576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825576 prefixEnd_825576 := by exact prefixLift 825576
  have htrace : WordTrace (prefixWord ++ tailWord_825576) baseStart_825576 baseEnd_825576 := by
    simpa [prefixWord, tailWord_825576, baseEnd_825576] using wordTrace_append hprefix tailTrace_825576
  have hstable : (prefixWord ++ tailWord_825576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825576).length < 2 ^ (prefixWord ++ tailWord_825576).sum := by decide
  have hdescent : baseEnd_825576 < baseStart_825576 := by decide
  rcases family_descends (prefixWord ++ tailWord_825576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825630 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_825630 : Nat := 118140960795 + 825630 * 2 ^ 59
def prefixEnd_825630 : Nat := 4983230072969 + 3 ^ 40 * 825630 * 2
def baseEnd_825630 : Nat := 423945032771709952528003

theorem tailTrace_825630 : CollatzResearch.WordTrace tailWord_825630 prefixEnd_825630 423945032771709952528003 := by
  unfold tailWord_825630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764149999861373902877293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20075466665927327482012229 3764149999861373902877293)
  ·
    refine ⟨1411556249948015213578985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3764149999861373902877293 1411556249948015213578985)
    ·
      refine ⟨1058667187461011410184239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1411556249948015213578985 1058667187461011410184239)
      ·
        refine ⟨1588000781191517115276359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058667187461011410184239 1588000781191517115276359)
        ·
          refine ⟨2382001171787275672914539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588000781191517115276359 2382001171787275672914539)
          ·
            refine ⟨3573001757680913509371809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382001171787275672914539 3573001757680913509371809)
            ·
              refine ⟨2679751318260685132028857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3573001757680913509371809 2679751318260685132028857)
              ·
                refine ⟨2009813488695513849021643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679751318260685132028857 2009813488695513849021643)
                ·
                  refine ⟨3014720233043270773532465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009813488695513849021643 3014720233043270773532465)
                  ·
                    refine ⟨2261040174782453080149349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3014720233043270773532465 2261040174782453080149349)
                    ·
                      refine ⟨423945032771709952528003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2261040174782453080149349 423945032771709952528003)
                      ·
                        rfl

theorem cell23_825630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_825630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825630 prefixEnd_825630 := by exact prefixLift 825630
  have htrace : WordTrace (prefixWord ++ tailWord_825630) baseStart_825630 baseEnd_825630 := by
    simpa [prefixWord, tailWord_825630, baseEnd_825630] using wordTrace_append hprefix tailTrace_825630
  have hstable : (prefixWord ++ tailWord_825630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825630).length < 2 ^ (prefixWord ++ tailWord_825630).sum := by decide
  have hdescent : baseEnd_825630 < baseStart_825630 := by decide
  rcases family_descends (prefixWord ++ tailWord_825630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825634 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_825634 : Nat := 118140960795 + 825634 * 2 ^ 59
def prefixEnd_825634 : Nat := 4983230072969 + 3 ^ 40 * 825634 * 2
def baseEnd_825634 : Nat := 423947086694327936877985

theorem tailTrace_825634 : CollatzResearch.WordTrace tailWord_825634 prefixEnd_825634 423947086694327936877985 := by
  unfold tailWord_825634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528336472719124976540989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20075563927250999937442637 7528336472719124976540989)
  ·
    refine ⟨2823126177269671866202871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7528336472719124976540989 2823126177269671866202871)
    ·
      refine ⟨4234689265904507799304307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823126177269671866202871 4234689265904507799304307)
      ·
        refine ⟨6352033898856761698956461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234689265904507799304307 6352033898856761698956461)
        ·
          refine ⟨2382012712071285637108673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6352033898856761698956461 2382012712071285637108673)
          ·
            refine ⟨1786509534053464227831505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2382012712071285637108673 1786509534053464227831505)
            ·
              refine ⟨1339882150540098170873629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786509534053464227831505 1339882150540098170873629)
              ·
                refine ⟨502455806452536814077611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1339882150540098170873629 502455806452536814077611)
                ·
                  refine ⟨753683709678805221116417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502455806452536814077611 753683709678805221116417)
                  ·
                    refine ⟨565262782259103915837313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 753683709678805221116417 565262782259103915837313)
                    ·
                      refine ⟨423947086694327936877985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565262782259103915837313 423947086694327936877985)
                      ·
                        rfl

theorem cell23_825634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_825634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825634 prefixEnd_825634 := by exact prefixLift 825634
  have htrace : WordTrace (prefixWord ++ tailWord_825634) baseStart_825634 baseEnd_825634 := by
    simpa [prefixWord, tailWord_825634, baseEnd_825634] using wordTrace_append hprefix tailTrace_825634
  have hstable : (prefixWord ++ tailWord_825634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825634).length < 2 ^ (prefixWord ++ tailWord_825634).sum := by decide
  have hdescent : baseEnd_825634 < baseStart_825634 := by decide
  rcases family_descends (prefixWord ++ tailWord_825634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825637 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 1, 2, 3]
def baseStart_825637 : Nat := 118140960795 + 825637 * 2 ^ 59
def prefixEnd_825637 : Nat := 4983230072969 + 3 ^ 40 * 825637 * 2
def baseEnd_825637 : Nat := 423948627136291425140471

theorem tailTrace_825637 : CollatzResearch.WordTrace tailWord_825637 prefixEnd_825637 423948627136291425140471 := by
  unfold tailWord_825637
  simp only [CollatzResearch.WordTrace]
  refine ⟨30113455309865631418523165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20075636873243754279015443 30113455309865631418523165)
  ·
    refine ⟨11292545741199611781946187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30113455309865631418523165 11292545741199611781946187)
    ·
      refine ⟨16938818611799417672919281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11292545741199611781946187 16938818611799417672919281)
      ·
        refine ⟨12704113958849563254689461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16938818611799417672919281 12704113958849563254689461)
        ·
          refine ⟨1191010683642146555127137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12704113958849563254689461 1191010683642146555127137)
          ·
            refine ⟨893258012731609916345353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191010683642146555127137 893258012731609916345353)
            ·
              refine ⟨669943509548707437259015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893258012731609916345353 669943509548707437259015)
              ·
                refine ⟨1004915264323061155888523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669943509548707437259015 1004915264323061155888523)
                ·
                  refine ⟨1507372896484591733832785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004915264323061155888523 1507372896484591733832785)
                  ·
                    refine ⟨1130529672363443800374589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507372896484591733832785 1130529672363443800374589)
                    ·
                      refine ⟨423948627136291425140471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130529672363443800374589 423948627136291425140471)
                      ·
                        rfl

theorem cell23_825637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_825637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825637 prefixEnd_825637 := by exact prefixLift 825637
  have htrace : WordTrace (prefixWord ++ tailWord_825637) baseStart_825637 baseEnd_825637 := by
    simpa [prefixWord, tailWord_825637, baseEnd_825637] using wordTrace_append hprefix tailTrace_825637
  have hstable : (prefixWord ++ tailWord_825637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825637).length < 2 ^ (prefixWord ++ tailWord_825637).sum := by decide
  have hdescent : baseEnd_825637 < baseStart_825637 := by decide
  rcases family_descends (prefixWord ++ tailWord_825637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825650 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_825650 : Nat := 118140960795 + 825650 * 2 ^ 59
def prefixEnd_825650 : Nat := 4983230072969 + 3 ^ 40 * 825650 * 2
def baseEnd_825650 : Nat := 423955302384799874277911

theorem tailTrace_825650 : CollatzResearch.WordTrace tailWord_825650 prefixEnd_825650 423955302384799874277911 := by
  unfold tailWord_825650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528482364704633659686601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20075952972545689759164269 7528482364704633659686601)
  ·
    refine ⟨5646361773528475244764951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7528482364704633659686601 5646361773528475244764951)
    ·
      refine ⟨8469542660292712867147427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5646361773528475244764951 8469542660292712867147427)
      ·
        refine ⟨12704313990439069300721141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8469542660292712867147427 12704313990439069300721141)
        ·
          refine ⟨1191029436603662746942607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12704313990439069300721141 1191029436603662746942607)
          ·
            refine ⟨1786544154905494120413911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191029436603662746942607 1786544154905494120413911)
            ·
              refine ⟨2679816232358241180620867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786544154905494120413911 2679816232358241180620867)
              ·
                refine ⟨4019724348537361770931301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679816232358241180620867 4019724348537361770931301)
                ·
                  refine ⟨753698315350755332049619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4019724348537361770931301 753698315350755332049619)
                  ·
                    refine ⟨1130547473026132998074429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 753698315350755332049619 1130547473026132998074429)
                    ·
                      refine ⟨423955302384799874277911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130547473026132998074429 423955302384799874277911)
                      ·
                        rfl

theorem cell23_825650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_825650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825650 prefixEnd_825650 := by exact prefixLift 825650
  have htrace : WordTrace (prefixWord ++ tailWord_825650) baseStart_825650 baseEnd_825650 := by
    simpa [prefixWord, tailWord_825650, baseEnd_825650] using wordTrace_append hprefix tailTrace_825650
  have hstable : (prefixWord ++ tailWord_825650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825650).length < 2 ^ (prefixWord ++ tailWord_825650).sum := by decide
  have hdescent : baseEnd_825650 < baseStart_825650 := by decide
  rcases family_descends (prefixWord ++ tailWord_825650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825676 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_825676 : Nat := 118140960795 + 825676 * 2 ^ 59
def prefixEnd_825676 : Nat := 4983230072969 + 3 ^ 40 * 825676 * 2
def baseEnd_825676 : Nat := 423968652881816772552791

theorem tailTrace_825676 : CollatzResearch.WordTrace tailWord_825676 prefixEnd_825676 423968652881816772552791 := by
  unfold tailWord_825676
  simp only [CollatzResearch.WordTrace]
  refine ⟨15057438878362170539596441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20076585171149560719461921 15057438878362170539596441)
  ·
    refine ⟨11293079158771627904697331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15057438878362170539596441 11293079158771627904697331)
    ·
      refine ⟨16939618738157441857045997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11293079158771627904697331 16939618738157441857045997)
      ·
        refine ⟨6352357026809040696392249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16939618738157441857045997 6352357026809040696392249)
        ·
          refine ⟨4764267770106780522294187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6352357026809040696392249 4764267770106780522294187)
          ·
            refine ⟨7146401655160170783441281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764267770106780522294187 7146401655160170783441281)
            ·
              refine ⟨5359801241370128087580961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7146401655160170783441281 5359801241370128087580961)
              ·
                refine ⟨4019850931027596065685721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359801241370128087580961 4019850931027596065685721)
                ·
                  refine ⟨3014888198270697049264291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019850931027596065685721 3014888198270697049264291)
                  ·
                    refine ⟨4522332297406045573896437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014888198270697049264291 4522332297406045573896437)
                    ·
                      refine ⟨423968652881816772552791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4522332297406045573896437 423968652881816772552791)
                      ·
                        rfl

theorem cell23_825676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_825676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825676 prefixEnd_825676 := by exact prefixLift 825676
  have htrace : WordTrace (prefixWord ++ tailWord_825676) baseStart_825676 baseEnd_825676 := by
    simpa [prefixWord, tailWord_825676, baseEnd_825676] using wordTrace_append hprefix tailTrace_825676
  have hstable : (prefixWord ++ tailWord_825676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825676).length < 2 ^ (prefixWord ++ tailWord_825676).sum := by decide
  have hdescent : baseEnd_825676 < baseStart_825676 := by decide
  rcases family_descends (prefixWord ++ tailWord_825676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825679 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 9]
def baseStart_825679 : Nat := 118140960795 + 825679 * 2 ^ 59
def prefixEnd_825679 : Nat := 4983230072969 + 3 ^ 40 * 825679 * 2
def baseEnd_825679 : Nat := 47107799258197806757253

theorem tailTrace_825679 : CollatzResearch.WordTrace tailWord_825679 prefixEnd_825679 47107799258197806757253 := by
  unfold tailWord_825679
  simp only [CollatzResearch.WordTrace]
  refine ⟨30114987175713472591552091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20076658117142315061034727 30114987175713472591552091)
  ·
    refine ⟨45172480763570208887328137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30114987175713472591552091 45172480763570208887328137)
    ·
      refine ⟨33879360572677656665496103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45172480763570208887328137 33879360572677656665496103)
      ·
        refine ⟨50819040859016484998244155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33879360572677656665496103 50819040859016484998244155)
        ·
          refine ⟨76228561288524727497366233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50819040859016484998244155 76228561288524727497366233)
          ·
            refine ⟨57171420966393545623024675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76228561288524727497366233 57171420966393545623024675)
            ·
              refine ⟨85757131449590318434537013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57171420966393545623024675 85757131449590318434537013)
              ·
                refine ⟨8039731073399092353237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85757131449590318434537013 8039731073399092353237845)
                ·
                  refine ⟨47107799258197806757253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8039731073399092353237845 47107799258197806757253)
                  ·
                    rfl

theorem cell23_825679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 9].length) (baseStart_825679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825679 prefixEnd_825679 := by exact prefixLift 825679
  have htrace : WordTrace (prefixWord ++ tailWord_825679) baseStart_825679 baseEnd_825679 := by
    simpa [prefixWord, tailWord_825679, baseEnd_825679] using wordTrace_append hprefix tailTrace_825679
  have hstable : (prefixWord ++ tailWord_825679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825679).length < 2 ^ (prefixWord ++ tailWord_825679).sum := by decide
  have hdescent : baseEnd_825679 < baseStart_825679 := by decide
  rcases family_descends (prefixWord ++ tailWord_825679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825718 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_825718 : Nat := 118140960795 + 825718 * 2 ^ 59
def prefixEnd_825718 : Nat := 4983230072969 + 3 ^ 40 * 825718 * 2
def baseEnd_825718 : Nat := 423990219069305608227599

theorem tailTrace_825718 : CollatzResearch.WordTrace tailWord_825718 prefixEnd_825718 423990219069305608227599 := by
  unfold tailWord_825718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882275601410761390763863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20077606415048121501481205 1882275601410761390763863)
  ·
    refine ⟨2823413402116142086145795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882275601410761390763863 2823413402116142086145795)
    ·
      refine ⟨4235120103174213129218693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823413402116142086145795 4235120103174213129218693)
      ·
        refine ⟨794085019345164961728505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4235120103174213129218693 794085019345164961728505)
        ·
          refine ⟨595563764508873721296379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794085019345164961728505 595563764508873721296379)
          ·
            refine ⟨893345646763310581944569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595563764508873721296379 893345646763310581944569)
            ·
              refine ⟨670009235072482936458427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893345646763310581944569 670009235072482936458427)
              ·
                refine ⟨1005013852608724404687641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670009235072482936458427 1005013852608724404687641)
                ·
                  refine ⟨753760389456543303515731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005013852608724404687641 753760389456543303515731)
                  ·
                    refine ⟨1130640584184814955273597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 753760389456543303515731 1130640584184814955273597)
                    ·
                      refine ⟨423990219069305608227599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130640584184814955273597 423990219069305608227599)
                      ·
                        rfl

theorem cell23_825718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_825718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825718 prefixEnd_825718 := by exact prefixLift 825718
  have htrace : WordTrace (prefixWord ++ tailWord_825718) baseStart_825718 baseEnd_825718 := by
    simpa [prefixWord, tailWord_825718, baseEnd_825718] using wordTrace_append hprefix tailTrace_825718
  have hstable : (prefixWord ++ tailWord_825718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825718).length < 2 ^ (prefixWord ++ tailWord_825718).sum := by decide
  have hdescent : baseEnd_825718 < baseStart_825718 := by decide
  rcases family_descends (prefixWord ++ tailWord_825718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825736 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_825736 : Nat := 118140960795 + 825736 * 2 ^ 59
def prefixEnd_825736 : Nat := 4983230072969 + 3 ^ 40 * 825736 * 2
def baseEnd_825736 : Nat := 423999461721086537802515

theorem tailTrace_825736 : CollatzResearch.WordTrace tailWord_825736 prefixEnd_825736 423999461721086537802515 := by
  unfold tailWord_825736
  simp only [CollatzResearch.WordTrace]
  refine ⟨15058533068253485663188531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20078044091004647550918041 15058533068253485663188531)
  ·
    refine ⟨22587799602380228494782797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15058533068253485663188531 22587799602380228494782797)
    ·
      refine ⟨8470424850892585685543549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22587799602380228494782797 8470424850892585685543549)
      ·
        refine ⟨3176409319084719632078831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8470424850892585685543549 3176409319084719632078831)
        ·
          refine ⟨4764613978627079448118247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176409319084719632078831 4764613978627079448118247)
          ·
            refine ⟨7146920967940619172177371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764613978627079448118247 7146920967940619172177371)
            ·
              refine ⟨10720381451910928758266057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7146920967940619172177371 10720381451910928758266057)
              ·
                refine ⟨8040286088933196568699543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10720381451910928758266057 8040286088933196568699543)
                ·
                  refine ⟨12060429133399794853049315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8040286088933196568699543 12060429133399794853049315)
                  ·
                    refine ⟨18090643700099692279573973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12060429133399794853049315 18090643700099692279573973)
                    ·
                      refine ⟨423999461721086537802515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18090643700099692279573973 423999461721086537802515)
                      ·
                        rfl

theorem cell23_825736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_825736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825736 prefixEnd_825736 := by exact prefixLift 825736
  have htrace : WordTrace (prefixWord ++ tailWord_825736) baseStart_825736 baseEnd_825736 := by
    simpa [prefixWord, tailWord_825736, baseEnd_825736] using wordTrace_append hprefix tailTrace_825736
  have hstable : (prefixWord ++ tailWord_825736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825736).length < 2 ^ (prefixWord ++ tailWord_825736).sum := by decide
  have hdescent : baseEnd_825736 < baseStart_825736 := by decide
  rcases family_descends (prefixWord ++ tailWord_825736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825763 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 4]
def baseStart_825763 : Nat := 118140960795 + 825763 * 2 ^ 59
def prefixEnd_825763 : Nat := 4983230072969 + 3 ^ 40 * 825763 * 2
def baseEnd_825763 : Nat := 424013325698757932164891

theorem tailTrace_825763 : CollatzResearch.WordTrace tailWord_825763 prefixEnd_825763 424013325698757932164891 := by
  unfold tailWord_825763
  simp only [CollatzResearch.WordTrace]
  refine ⟨30118050907409154937609943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20078700604939436625073295 30118050907409154937609943)
  ·
    refine ⟨45177076361113732406414915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30118050907409154937609943 45177076361113732406414915)
    ·
      refine ⟨67765614541670598609622373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45177076361113732406414915 67765614541670598609622373)
      ·
        refine ⟨12706052726563237239304195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67765614541670598609622373 12706052726563237239304195)
        ·
          refine ⟨19059079089844855858956293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706052726563237239304195 19059079089844855858956293)
          ·
            refine ⟨3573577329345910473554305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19059079089844855858956293 3573577329345910473554305)
            ·
              refine ⟨2680182997009432855165729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3573577329345910473554305 2680182997009432855165729)
              ·
                refine ⟨2010137247757074641374297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680182997009432855165729 2010137247757074641374297)
                ·
                  refine ⟨1507602935817805981030723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010137247757074641374297 1507602935817805981030723)
                  ·
                    refine ⟨2261404403726708971546085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507602935817805981030723 2261404403726708971546085)
                    ·
                      refine ⟨424013325698757932164891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2261404403726708971546085 424013325698757932164891)
                      ·
                        rfl

theorem cell23_825763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_825763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825763 prefixEnd_825763 := by exact prefixLift 825763
  have htrace : WordTrace (prefixWord ++ tailWord_825763) baseStart_825763 baseEnd_825763 := by
    simpa [prefixWord, tailWord_825763, baseEnd_825763] using wordTrace_append hprefix tailTrace_825763
  have hstable : (prefixWord ++ tailWord_825763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825763).length < 2 ^ (prefixWord ++ tailWord_825763).sum := by decide
  have hdescent : baseEnd_825763 < baseStart_825763 := by decide
  rcases family_descends (prefixWord ++ tailWord_825763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825800 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_825800 : Nat := 118140960795 + 825800 * 2 ^ 59
def prefixEnd_825800 : Nat := 4983230072969 + 3 ^ 40 * 825800 * 2
def baseEnd_825800 : Nat := 424032324482974287402221

theorem tailTrace_825800 : CollatzResearch.WordTrace tailWord_825800 prefixEnd_825800 424032324482974287402221 := by
  unfold tailWord_825800
  simp only [CollatzResearch.WordTrace]
  refine ⟨15059700204137555128353427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20079600272183406837804569 15059700204137555128353427)
  ·
    refine ⟨22589550306206332692530141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15059700204137555128353427 22589550306206332692530141)
    ·
      refine ⟨8471081364827374759698803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22589550306206332692530141 8471081364827374759698803)
      ·
        refine ⟨12706622047241062139548205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8471081364827374759698803 12706622047241062139548205)
        ·
          refine ⟨4764983267715398302330577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12706622047241062139548205 4764983267715398302330577)
          ·
            refine ⟨3573737450786548726747933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764983267715398302330577 3573737450786548726747933)
            ·
              refine ⟨1340151544044955772530475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3573737450786548726747933 1340151544044955772530475)
              ·
                refine ⟨2010227316067433658795713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340151544044955772530475 2010227316067433658795713)
                ·
                  refine ⟨1507670487050575244096785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010227316067433658795713 1507670487050575244096785)
                  ·
                    refine ⟨1130752865287931433072589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507670487050575244096785 1130752865287931433072589)
                    ·
                      refine ⟨424032324482974287402221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130752865287931433072589 424032324482974287402221)
                      ·
                        rfl

theorem cell23_825800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_825800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825800 prefixEnd_825800 := by exact prefixLift 825800
  have htrace : WordTrace (prefixWord ++ tailWord_825800) baseStart_825800 baseEnd_825800 := by
    simpa [prefixWord, tailWord_825800, baseEnd_825800] using wordTrace_append hprefix tailTrace_825800
  have hstable : (prefixWord ++ tailWord_825800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825800).length < 2 ^ (prefixWord ++ tailWord_825800).sum := by decide
  have hdescent : baseEnd_825800 < baseStart_825800 := by decide
  rcases family_descends (prefixWord ++ tailWord_825800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825837 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 6]
def baseStart_825837 : Nat := 118140960795 + 825837 * 2 ^ 59
def prefixEnd_825837 : Nat := 4983230072969 + 3 ^ 40 * 825837 * 2
def baseEnd_825837 : Nat := 47116813696354515848839

theorem tailTrace_825837 : CollatzResearch.WordTrace tailWord_825837 prefixEnd_825837 47116813696354515848839 := by
  unfold tailWord_825837
  simp only [CollatzResearch.WordTrace]
  refine ⟨30120749909141065575803765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20080499939427377050535843 30120749909141065575803765)
  ·
    refine ⟨2823820303981974897731603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30120749909141065575803765 2823820303981974897731603)
    ·
      refine ⟨4235730455972962346597405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823820303981974897731603 4235730455972962346597405)
      ·
        refine ⟨1588398920989860879974027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4235730455972962346597405 1588398920989860879974027)
        ·
          refine ⟨2382598381484791319961041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588398920989860879974027 2382598381484791319961041)
          ·
            refine ⟨1786948786113593489970781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2382598381484791319961041 1786948786113593489970781)
            ·
              refine ⟨670105794792597558739043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786948786113593489970781 670105794792597558739043)
              ·
                refine ⟨1005158692188896338108565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670105794792597558739043 1005158692188896338108565)
                ·
                  refine ⟨47116813696354515848839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1005158692188896338108565 47116813696354515848839)
                  ·
                    rfl

theorem cell23_825837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_825837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825837 prefixEnd_825837 := by exact prefixLift 825837
  have htrace : WordTrace (prefixWord ++ tailWord_825837) baseStart_825837 baseEnd_825837 := by
    simpa [prefixWord, tailWord_825837, baseEnd_825837] using wordTrace_append hprefix tailTrace_825837
  have hstable : (prefixWord ++ tailWord_825837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825837).length < 2 ^ (prefixWord ++ tailWord_825837).sum := by decide
  have hdescent : baseEnd_825837 < baseStart_825837 := by decide
  rcases family_descends (prefixWord ++ tailWord_825837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825858 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_825858 : Nat := 118140960795 + 825858 * 2 ^ 59
def prefixEnd_825858 : Nat := 4983230072969 + 3 ^ 40 * 825858 * 2
def baseEnd_825858 : Nat := 141354035453645020158985

theorem tailTrace_825858 : CollatzResearch.WordTrace tailWord_825858 prefixEnd_825858 141354035453645020158985 := by
  unfold tailWord_825858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7530378960516246540579557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20081010561376657441545485 7530378960516246540579557)
  ·
    refine ⟨1411946055096796226358667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7530378960516246540579557 1411946055096796226358667)
    ·
      refine ⟨2117919082645194339538001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411946055096796226358667 2117919082645194339538001)
      ·
        refine ⟨1588439311983895754653501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2117919082645194339538001 1588439311983895754653501)
        ·
          refine ⟨595664741993960907995063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1588439311983895754653501 595664741993960907995063)
          ·
            refine ⟨893497112990941361992595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595664741993960907995063 893497112990941361992595)
            ·
              refine ⟨1340245669486412042988893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893497112990941361992595 1340245669486412042988893)
              ·
                refine ⟨502592126057404516120835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1340245669486412042988893 502592126057404516120835)
                ·
                  refine ⟨753888189086106774181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502592126057404516120835 753888189086106774181253)
                  ·
                    refine ⟨141354035453645020158985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753888189086106774181253 141354035453645020158985)
                    ·
                      rfl

theorem cell23_825858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_825858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825858 prefixEnd_825858 := by exact prefixLift 825858
  have htrace : WordTrace (prefixWord ++ tailWord_825858) baseStart_825858 baseEnd_825858 := by
    simpa [prefixWord, tailWord_825858, baseEnd_825858] using wordTrace_append hprefix tailTrace_825858
  have hstable : (prefixWord ++ tailWord_825858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825858).length < 2 ^ (prefixWord ++ tailWord_825858).sum := by decide
  have hdescent : baseEnd_825858 < baseStart_825858 := by decide
  rcases family_descends (prefixWord ++ tailWord_825858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825880 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 4, 4]
def baseStart_825880 : Nat := 118140960795 + 825880 * 2 ^ 59
def prefixEnd_825880 : Nat := 4983230072969 + 3 ^ 40 * 825880 * 2
def baseEnd_825880 : Nat := 141357800978444658133951

theorem tailTrace_825880 : CollatzResearch.WordTrace tailWord_825880 prefixEnd_825880 141357800978444658133951 := by
  unfold tailWord_825880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061159123992641959809547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20081545498656855946412729 15061159123992641959809547)
  ·
    refine ⟨22591738685988962939714321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061159123992641959809547 22591738685988962939714321)
    ·
      refine ⟨16943804014491722204785741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22591738685988962939714321 16943804014491722204785741)
      ·
        refine ⟨6353926505434395826794653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16943804014491722204785741 6353926505434395826794653)
        ·
          refine ⟨2382722439537898435047995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6353926505434395826794653 2382722439537898435047995)
          ·
            refine ⟨3574083659306847652571993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382722439537898435047995 3574083659306847652571993)
            ·
              refine ⟨2680562744480135739428995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574083659306847652571993 2680562744480135739428995)
              ·
                refine ⟨4020844116720203609143493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680562744480135739428995 4020844116720203609143493)
                ·
                  refine ⟨753908271885038176714405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4020844116720203609143493 753908271885038176714405)
                  ·
                    refine ⟨141357800978444658133951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753908271885038176714405 141357800978444658133951)
                    ·
                      rfl

theorem cell23_825880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_825880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825880 prefixEnd_825880 := by exact prefixLift 825880
  have htrace : WordTrace (prefixWord ++ tailWord_825880) baseStart_825880 baseEnd_825880 := by
    simpa [prefixWord, tailWord_825880, baseEnd_825880] using wordTrace_append hprefix tailTrace_825880
  have hstable : (prefixWord ++ tailWord_825880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825880).length < 2 ^ (prefixWord ++ tailWord_825880).sum := by decide
  have hdescent : baseEnd_825880 < baseStart_825880 := by decide
  rcases family_descends (prefixWord ++ tailWord_825880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825890 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_825890 : Nat := 118140960795 + 825890 * 2 ^ 59
def prefixEnd_825890 : Nat := 4983230072969 + 3 ^ 40 * 825890 * 2
def baseEnd_825890 : Nat := 424078537741878935276807

theorem tailTrace_825890 : CollatzResearch.WordTrace tailWord_825890 prefixEnd_825890 424078537741878935276807 := by
  unfold tailWord_825890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7530670744487263906870781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20081788651966037084988749 7530670744487263906870781)
  ·
    refine ⟨2824001529182723965076543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7530670744487263906870781 2824001529182723965076543)
    ·
      refine ⟨4236002293774085947614815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824001529182723965076543 4236002293774085947614815)
      ·
        refine ⟨6354003440661128921422223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236002293774085947614815 6354003440661128921422223)
        ·
          refine ⟨9531005160991693382133335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354003440661128921422223 9531005160991693382133335)
          ·
            refine ⟨14296507741487540073200003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9531005160991693382133335 14296507741487540073200003)
            ·
              refine ⟨21444761612231310109800005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14296507741487540073200003 21444761612231310109800005)
              ·
                refine ⟨4020892802293370645587501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21444761612231310109800005 4020892802293370645587501)
                ·
                  refine ⟨1507834800860013992095313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4020892802293370645587501 1507834800860013992095313)
                  ·
                    refine ⟨1130876100645010494071485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507834800860013992095313 1130876100645010494071485)
                    ·
                      refine ⟨424078537741878935276807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130876100645010494071485 424078537741878935276807)
                      ·
                        rfl

theorem cell23_825890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_825890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825890 prefixEnd_825890 := by exact prefixLift 825890
  have htrace : WordTrace (prefixWord ++ tailWord_825890) baseStart_825890 baseEnd_825890 := by
    simpa [prefixWord, tailWord_825890, baseEnd_825890] using wordTrace_append hprefix tailTrace_825890
  have hstable : (prefixWord ++ tailWord_825890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825890).length < 2 ^ (prefixWord ++ tailWord_825890).sum := by decide
  have hdescent : baseEnd_825890 < baseStart_825890 := by decide
  rcases family_descends (prefixWord ++ tailWord_825890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825903 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_825903 : Nat := 118140960795 + 825903 * 2 ^ 59
def prefixEnd_825903 : Nat := 4983230072969 + 3 ^ 40 * 825903 * 2
def baseEnd_825903 : Nat := 424085212990387384414247

theorem tailTrace_825903 : CollatzResearch.WordTrace tailWord_825903 prefixEnd_825903 424085212990387384414247 := by
  unfold tailWord_825903
  simp only [CollatzResearch.WordTrace]
  refine ⟨30123157126901958847706363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20082104751267972565137575 30123157126901958847706363)
  ·
    refine ⟨45184735690352938271559545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30123157126901958847706363 45184735690352938271559545)
    ·
      refine ⟨33888551767764703703669659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45184735690352938271559545 33888551767764703703669659)
      ·
        refine ⟨50832827651647055555504489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33888551767764703703669659 50832827651647055555504489)
        ·
          refine ⟨38124620738735291666628367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50832827651647055555504489 38124620738735291666628367)
          ·
            refine ⟨57186931108102937499942551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38124620738735291666628367 57186931108102937499942551)
            ·
              refine ⟨85780396662154406249913827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57186931108102937499942551 85780396662154406249913827)
              ·
                refine ⟨128670594993231609374870741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85780396662154406249913827 128670594993231609374870741)
                ·
                  refine ⟨3015717070153865844723533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128670594993231609374870741 3015717070153865844723533)
                  ·
                    refine ⟨1130893901307699691771325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015717070153865844723533 1130893901307699691771325)
                    ·
                      refine ⟨424085212990387384414247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130893901307699691771325 424085212990387384414247)
                      ·
                        rfl

theorem cell23_825903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_825903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825903 prefixEnd_825903 := by exact prefixLift 825903
  have htrace : WordTrace (prefixWord ++ tailWord_825903) baseStart_825903 baseEnd_825903 := by
    simpa [prefixWord, tailWord_825903, baseEnd_825903] using wordTrace_append hprefix tailTrace_825903
  have hstable : (prefixWord ++ tailWord_825903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825903).length < 2 ^ (prefixWord ++ tailWord_825903).sum := by decide
  have hdescent : baseEnd_825903 < baseStart_825903 := by decide
  rcases family_descends (prefixWord ++ tailWord_825903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825910 : List Nat := [5, 1, 2, 1, 2, 1, 2, 9]
def baseStart_825910 : Nat := 118140960795 + 825910 * 2 ^ 59
def prefixEnd_825910 : Nat := 4983230072969 + 3 ^ 40 * 825910 * 2
def baseEnd_825910 : Nat := 15706992864998846556545

theorem tailTrace_825910 : CollatzResearch.WordTrace tailWord_825910 prefixEnd_825910 15706992864998846556545 := by
  unfold tailWord_825910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882713277367287440200699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20082274958584399362140789 1882713277367287440200699)
  ·
    refine ⟨2824069916050931160301049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882713277367287440200699 2824069916050931160301049)
    ·
      refine ⟨2118052437038198370225787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2824069916050931160301049 2118052437038198370225787)
      ·
        refine ⟨3177078655557297555338681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118052437038198370225787 3177078655557297555338681)
        ·
          refine ⟨2382808991667973166504011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3177078655557297555338681 2382808991667973166504011)
          ·
            refine ⟨3574213487501959749756017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382808991667973166504011 3574213487501959749756017)
            ·
              refine ⟨2680660115626469812317013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574213487501959749756017 2680660115626469812317013)
              ·
                refine ⟨15706992864998846556545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2680660115626469812317013 15706992864998846556545)
                ·
                  rfl

theorem cell23_825910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_825910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825910 prefixEnd_825910 := by exact prefixLift 825910
  have htrace : WordTrace (prefixWord ++ tailWord_825910) baseStart_825910 baseEnd_825910 := by
    simpa [prefixWord, tailWord_825910, baseEnd_825910] using wordTrace_append hprefix tailTrace_825910
  have hstable : (prefixWord ++ tailWord_825910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825910).length < 2 ^ (prefixWord ++ tailWord_825910).sum := by decide
  have hdescent : baseEnd_825910 < baseStart_825910 := by decide
  rcases family_descends (prefixWord ++ tailWord_825910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825920 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 6, 1, 3]
def baseStart_825920 : Nat := 118140960795 + 825920 * 2 ^ 59
def prefixEnd_825920 : Nat := 4983230072969 + 3 ^ 40 * 825920 * 2
def baseEnd_825920 : Nat := 424093942161513817901669

theorem tailTrace_825920 : CollatzResearch.WordTrace tailWord_825920 prefixEnd_825920 424093942161513817901669 := by
  unfold tailWord_825920
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061888583920185375537607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20082518111893580500716809 15061888583920185375537607)
  ·
    refine ⟨22592832875880278063306411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061888583920185375537607 22592832875880278063306411)
    ·
      refine ⟨33889249313820417094959617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22592832875880278063306411 33889249313820417094959617)
      ·
        refine ⟨25416936985365312821219713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33889249313820417094959617 25416936985365312821219713)
        ·
          refine ⟨19062702739023984615914785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25416936985365312821219713 19062702739023984615914785)
          ·
            refine ⟨14297027054267988461936089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19062702739023984615914785 14297027054267988461936089)
            ·
              refine ⟨10722770290700991346452067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14297027054267988461936089 10722770290700991346452067)
              ·
                refine ⟨16084155436051487019678101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10722770290700991346452067 16084155436051487019678101)
                ·
                  refine ⟨753944786064913454047411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16084155436051487019678101 753944786064913454047411)
                  ·
                    refine ⟨1130917179097370181071117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 753944786064913454047411 1130917179097370181071117)
                    ·
                      refine ⟨424093942161513817901669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130917179097370181071117 424093942161513817901669)
                      ·
                        rfl

theorem cell23_825920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_825920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825920 prefixEnd_825920 := by exact prefixLift 825920
  have htrace : WordTrace (prefixWord ++ tailWord_825920) baseStart_825920 baseEnd_825920 := by
    simpa [prefixWord, tailWord_825920, baseEnd_825920] using wordTrace_append hprefix tailTrace_825920
  have hstable : (prefixWord ++ tailWord_825920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825920).length < 2 ^ (prefixWord ++ tailWord_825920).sum := by decide
  have hdescent : baseEnd_825920 < baseStart_825920 := by decide
  rcases family_descends (prefixWord ++ tailWord_825920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825937 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 3]
def baseStart_825937 : Nat := 118140960795 + 825937 * 2 ^ 59
def prefixEnd_825937 : Nat := 4983230072969 + 3 ^ 40 * 825937 * 2
def baseEnd_825937 : Nat := 424102671332640251389091

theorem tailTrace_825937 : CollatzResearch.WordTrace tailWord_825937 prefixEnd_825937 424102671332640251389091 := by
  unfold tailWord_825937
  simp only [CollatzResearch.WordTrace]
  refine ⟨30124397208778782654444065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20082931472519188436296043 30124397208778782654444065)
  ·
    refine ⟨22593297906584086990833049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30124397208778782654444065 22593297906584086990833049)
    ·
      refine ⟨16944973429938065243124787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22593297906584086990833049 16944973429938065243124787)
      ·
        refine ⟨25417460144907097864687181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16944973429938065243124787 25417460144907097864687181)
        ·
          refine ⟨9531547554340161699257693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25417460144907097864687181 9531547554340161699257693)
          ·
            refine ⟨3574330332877560637221635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9531547554340161699257693 3574330332877560637221635)
            ·
              refine ⟨5361495499316340955832453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574330332877560637221635 5361495499316340955832453)
              ·
                refine ⟨1005280406121813929218585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5361495499316340955832453 1005280406121813929218585)
                ·
                  refine ⟨753960304591360446913939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005280406121813929218585 753960304591360446913939)
                  ·
                    refine ⟨1130940456887040670370909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 753960304591360446913939 1130940456887040670370909)
                    ·
                      refine ⟨424102671332640251389091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1130940456887040670370909 424102671332640251389091)
                      ·
                        rfl

theorem cell23_825937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_825937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825937 prefixEnd_825937 := by exact prefixLift 825937
  have htrace : WordTrace (prefixWord ++ tailWord_825937) baseStart_825937 baseEnd_825937 := by
    simpa [prefixWord, tailWord_825937, baseEnd_825937] using wordTrace_append hprefix tailTrace_825937
  have hstable : (prefixWord ++ tailWord_825937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825937).length < 2 ^ (prefixWord ++ tailWord_825937).sum := by decide
  have hdescent : baseEnd_825937 < baseStart_825937 := by decide
  rcases family_descends (prefixWord ++ tailWord_825937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825943 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_825943 : Nat := 118140960795 + 825943 * 2 ^ 59
def prefixEnd_825943 : Nat := 4983230072969 + 3 ^ 40 * 825943 * 2
def baseEnd_825943 : Nat := 424105752216567227914063

theorem tailTrace_825943 : CollatzResearch.WordTrace tailWord_825943 prefixEnd_825943 424105752216567227914063 := by
  unfold tailWord_825943
  simp only [CollatzResearch.WordTrace]
  refine ⟨30124616046757045679162483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20083077364504697119441655 30124616046757045679162483)
  ·
    refine ⟨45186924070135568518743725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30124616046757045679162483 45186924070135568518743725)
    ·
      refine ⟨16945096526300838194528897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45186924070135568518743725 16945096526300838194528897)
      ·
        refine ⟨12708822394725628645896673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16945096526300838194528897 12708822394725628645896673)
        ·
          refine ⟨9531616796044221484422505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12708822394725628645896673 9531616796044221484422505)
          ·
            refine ⟨7148712597033166113316879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531616796044221484422505 7148712597033166113316879)
            ·
              refine ⟨10723068895549749169975319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148712597033166113316879 10723068895549749169975319)
              ·
                refine ⟨16084603343324623754962979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10723068895549749169975319 16084603343324623754962979)
                ·
                  refine ⟨24126905014986935632444469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16084603343324623754962979 24126905014986935632444469)
                  ·
                    refine ⟨2261897345155025215541669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24126905014986935632444469 2261897345155025215541669)
                    ·
                      refine ⟨424105752216567227914063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2261897345155025215541669 424105752216567227914063)
                      ·
                        rfl

theorem cell23_825943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_825943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825943 prefixEnd_825943 := by exact prefixLift 825943
  have htrace : WordTrace (prefixWord ++ tailWord_825943) baseStart_825943 baseEnd_825943 := by
    simpa [prefixWord, tailWord_825943, baseEnd_825943] using wordTrace_append hprefix tailTrace_825943
  have hstable : (prefixWord ++ tailWord_825943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825943).length < 2 ^ (prefixWord ++ tailWord_825943).sum := by decide
  have hdescent : baseEnd_825943 < baseStart_825943 := by decide
  rcases family_descends (prefixWord ++ tailWord_825943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825953 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 8]
def baseStart_825953 : Nat := 118140960795 + 825953 * 2 ^ 59
def prefixEnd_825953 : Nat := 4983230072969 + 3 ^ 40 * 825953 * 2
def baseEnd_825953 : Nat := 141370295674370729596339

theorem tailTrace_825953 : CollatzResearch.WordTrace tailWord_825953 prefixEnd_825953 141370295674370729596339 := by
  unfold tailWord_825953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30124980776720817387026513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20083320517813878258017675 30124980776720817387026513)
  ·
    refine ⟨22593735582540613040269885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30124980776720817387026513 22593735582540613040269885)
    ·
      refine ⟨8472650843452729890101207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22593735582540613040269885 8472650843452729890101207)
      ·
        refine ⟨12708976265179094835151811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472650843452729890101207 12708976265179094835151811)
        ·
          refine ⟨19063464397768642252727717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12708976265179094835151811 19063464397768642252727717)
          ·
            refine ⟨3574399574581620422386447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19063464397768642252727717 3574399574581620422386447)
            ·
              refine ⟨5361599361872430633579671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574399574581620422386447 5361599361872430633579671)
              ·
                refine ⟨8042399042808645950369507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361599361872430633579671 8042399042808645950369507)
                ·
                  refine ⟨12063598564212968925554261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042399042808645950369507 12063598564212968925554261)
                  ·
                    refine ⟨141370295674370729596339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12063598564212968925554261 141370295674370729596339)
                    ·
                      rfl

theorem cell23_825953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_825953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825953 prefixEnd_825953 := by exact prefixLift 825953
  have htrace : WordTrace (prefixWord ++ tailWord_825953) baseStart_825953 baseEnd_825953 := by
    simpa [prefixWord, tailWord_825953, baseEnd_825953] using wordTrace_append hprefix tailTrace_825953
  have hstable : (prefixWord ++ tailWord_825953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825953).length < 2 ^ (prefixWord ++ tailWord_825953).sum := by decide
  have hdescent : baseEnd_825953 < baseStart_825953 := by decide
  rcases family_descends (prefixWord ++ tailWord_825953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825963 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5]
def baseStart_825963 : Nat := 118140960795 + 825963 * 2 ^ 59
def prefixEnd_825963 : Nat := 4983230072969 + 3 ^ 40 * 825963 * 2
def baseEnd_825963 : Nat := 424116021829657149663971

theorem tailTrace_825963 : CollatzResearch.WordTrace tailWord_825963 prefixEnd_825963 424116021829657149663971 := by
  unfold tailWord_825963
  simp only [CollatzResearch.WordTrace]
  refine ⟨30125345506684589094890543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20083563671123059396593695 30125345506684589094890543)
  ·
    refine ⟨45188018260026883642335815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30125345506684589094890543 45188018260026883642335815)
    ·
      refine ⟨67782027390040325463503723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45188018260026883642335815 67782027390040325463503723)
      ·
        refine ⟨101673041085060488195255585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67782027390040325463503723 101673041085060488195255585)
        ·
          refine ⟨76254780813795366146441689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101673041085060488195255585 76254780813795366146441689)
          ·
            refine ⟨57191085610346524609831267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76254780813795366146441689 57191085610346524609831267)
            ·
              refine ⟨85786628415519786914746901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57191085610346524609831267 85786628415519786914746901)
              ·
                refine ⟨4021248206977490011628761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85786628415519786914746901 4021248206977490011628761)
                ·
                  refine ⟨3015936155233117508721571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021248206977490011628761 3015936155233117508721571)
                  ·
                    refine ⟨4523904232849676263082357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3015936155233117508721571 4523904232849676263082357)
                    ·
                      refine ⟨424116021829657149663971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4523904232849676263082357 424116021829657149663971)
                      ·
                        rfl

theorem cell23_825963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_825963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825963 prefixEnd_825963 := by exact prefixLift 825963
  have htrace : WordTrace (prefixWord ++ tailWord_825963) baseStart_825963 baseEnd_825963 := by
    simpa [prefixWord, tailWord_825963, baseEnd_825963] using wordTrace_append hprefix tailTrace_825963
  have hstable : (prefixWord ++ tailWord_825963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825963).length < 2 ^ (prefixWord ++ tailWord_825963).sum := by decide
  have hdescent : baseEnd_825963 < baseStart_825963 := by decide
  rcases family_descends (prefixWord ++ tailWord_825963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825977 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 1, 4, 2]
def baseStart_825977 : Nat := 118140960795 + 825977 * 2 ^ 59
def prefixEnd_825977 : Nat := 4983230072969 + 3 ^ 40 * 825977 * 2
def baseEnd_825977 : Nat := 424123210558820094888907

theorem tailTrace_825977 : CollatzResearch.WordTrace tailWord_825977 prefixEnd_825977 424123210558820094888907 := by
  unfold tailWord_825977
  simp only [CollatzResearch.WordTrace]
  refine ⟨30125856128633869485900185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20083904085755912990600123 30125856128633869485900185)
  ·
    refine ⟨22594392096475402114425139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30125856128633869485900185 22594392096475402114425139)
    ·
      refine ⟨33891588144713103171637709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22594392096475402114425139 33891588144713103171637709)
      ·
        refine ⟨12709345554267413689364141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33891588144713103171637709 12709345554267413689364141)
        ·
          refine ⟨4766004582850280133511553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12709345554267413689364141 4766004582850280133511553)
          ·
            refine ⟨3574503437137710100133665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4766004582850280133511553 3574503437137710100133665)
            ·
              refine ⟨2680877577853282575100249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574503437137710100133665 2680877577853282575100249)
              ·
                refine ⟨2010658183389961931325187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680877577853282575100249 2010658183389961931325187)
                ·
                  refine ⟨3015987275084942896987781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010658183389961931325187 3015987275084942896987781)
                  ·
                    refine ⟨565497614078426793185209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3015987275084942896987781 565497614078426793185209)
                    ·
                      refine ⟨424123210558820094888907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565497614078426793185209 424123210558820094888907)
                      ·
                        rfl

theorem cell23_825977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_825977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_825977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_825977 prefixEnd_825977 := by exact prefixLift 825977
  have htrace : WordTrace (prefixWord ++ tailWord_825977) baseStart_825977 baseEnd_825977 := by
    simpa [prefixWord, tailWord_825977, baseEnd_825977] using wordTrace_append hprefix tailTrace_825977
  have hstable : (prefixWord ++ tailWord_825977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825977).length < 2 ^ (prefixWord ++ tailWord_825977).sum := by decide
  have hdescent : baseEnd_825977 < baseStart_825977 := by decide
  rcases family_descends (prefixWord ++ tailWord_825977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826117 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_826117 : Nat := 118140960795 + 826117 * 2 ^ 59
def prefixEnd_826117 : Nat := 4983230072969 + 3 ^ 40 * 826117 * 2
def baseEnd_826117 : Nat := 424195097850449547138263

theorem tailTrace_826117 : CollatzResearch.WordTrace tailWord_826117 prefixEnd_826117 424195097850449547138263 := by
  unfold tailWord_826117
  simp only [CollatzResearch.WordTrace]
  refine ⟨30130962348126673395996605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20087308232084448930664403 30130962348126673395996605)
  ·
    refine ⟨11299110880547502523498727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30130962348126673395996605 11299110880547502523498727)
    ·
      refine ⟨16948666320821253785248091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11299110880547502523498727 16948666320821253785248091)
      ·
        refine ⟨25422999481231880677872137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16948666320821253785248091 25422999481231880677872137)
        ·
          refine ⟨19067249610923910508404103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25422999481231880677872137 19067249610923910508404103)
          ·
            refine ⟨28600874416385865762606155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19067249610923910508404103 28600874416385865762606155)
            ·
              refine ⟨42901311624578798643909233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28600874416385865762606155 42901311624578798643909233)
              ·
                refine ⟨32175983718434098982931925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42901311624578798643909233 32175983718434098982931925)
                ·
                  refine ⟨754124618400799194912467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32175983718434098982931925 754124618400799194912467)
                  ·
                    refine ⟨1131186927601198792368701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754124618400799194912467 1131186927601198792368701)
                    ·
                      refine ⟨424195097850449547138263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1131186927601198792368701 424195097850449547138263)
                      ·
                        rfl

theorem cell23_826117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_826117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826117 prefixEnd_826117 := by exact prefixLift 826117
  have htrace : WordTrace (prefixWord ++ tailWord_826117) baseStart_826117 baseEnd_826117 := by
    simpa [prefixWord, tailWord_826117, baseEnd_826117] using wordTrace_append hprefix tailTrace_826117
  have hstable : (prefixWord ++ tailWord_826117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826117).length < 2 ^ (prefixWord ++ tailWord_826117).sum := by decide
  have hdescent : baseEnd_826117 < baseStart_826117 := by decide
  rcases family_descends (prefixWord ++ tailWord_826117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826127 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 1, 5, 2]
def baseStart_826127 : Nat := 118140960795 + 826127 * 2 ^ 59
def prefixEnd_826127 : Nat := 4983230072969 + 3 ^ 40 * 826127 * 2
def baseEnd_826127 : Nat := 424200232656994508013217

theorem tailTrace_826127 : CollatzResearch.WordTrace tailWord_826127 prefixEnd_826127 424200232656994508013217 := by
  unfold tailWord_826127
  simp only [CollatzResearch.WordTrace]
  refine ⟨30131327078090445103860635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20087551385393630069240423 30131327078090445103860635)
  ·
    refine ⟨45196990617135667655790953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30131327078090445103860635 45196990617135667655790953)
    ·
      refine ⟨33897742962851750741843215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45196990617135667655790953 33897742962851750741843215)
      ·
        refine ⟨50846614444277626112764823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33897742962851750741843215 50846614444277626112764823)
        ·
          refine ⟨76269921666416439169147235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50846614444277626112764823 76269921666416439169147235)
          ·
            refine ⟨114404882499624658753720853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76269921666416439169147235 114404882499624658753720853)
            ·
              refine ⟨5362728867169905879080665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114404882499624658753720853 5362728867169905879080665)
              ·
                refine ⟨4022046650377429409310499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362728867169905879080665 4022046650377429409310499)
                ·
                  refine ⟨6033069975566144113965749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022046650377429409310499 6033069975566144113965749)
                  ·
                    refine ⟨565600310209326010684289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6033069975566144113965749 565600310209326010684289)
                    ·
                      refine ⟨424200232656994508013217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565600310209326010684289 424200232656994508013217)
                      ·
                        rfl

theorem cell23_826127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5, 2].length) (baseStart_826127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826127 prefixEnd_826127 := by exact prefixLift 826127
  have htrace : WordTrace (prefixWord ++ tailWord_826127) baseStart_826127 baseEnd_826127 := by
    simpa [prefixWord, tailWord_826127, baseEnd_826127] using wordTrace_append hprefix tailTrace_826127
  have hstable : (prefixWord ++ tailWord_826127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826127).length < 2 ^ (prefixWord ++ tailWord_826127).sum := by decide
  have hdescent : baseEnd_826127 < baseStart_826127 := by decide
  rcases family_descends (prefixWord ++ tailWord_826127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826144 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 1, 5, 2]
def baseStart_826144 : Nat := 118140960795 + 826144 * 2 ^ 59
def prefixEnd_826144 : Nat := 4983230072969 + 3 ^ 40 * 826144 * 2
def baseEnd_826144 : Nat := 424208961828120941500639

theorem tailTrace_826144 : CollatzResearch.WordTrace tailWord_826144 prefixEnd_826144 424208961828120941500639 := by
  unfold tailWord_826144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065973559514428503614743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20087964746019238004819657 15065973559514428503614743)
  ·
    refine ⟨22598960339271642755422115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15065973559514428503614743 22598960339271642755422115)
    ·
      refine ⟨33898440508907464133133173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22598960339271642755422115 33898440508907464133133173)
      ·
        refine ⟨3177978797710074762481235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33898440508907464133133173 3177978797710074762481235)
        ·
          refine ⟨4766968196565112143721853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177978797710074762481235 4766968196565112143721853)
          ·
            refine ⟨1787613073711917053895695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4766968196565112143721853 1787613073711917053895695)
            ·
              refine ⟨2681419610567875580843543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787613073711917053895695 2681419610567875580843543)
              ·
                refine ⟨4022129415851813371265315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681419610567875580843543 4022129415851813371265315)
                ·
                  refine ⟨6033194123777720056897973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022129415851813371265315 6033194123777720056897973)
                  ·
                    refine ⟨565611949104161255334185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6033194123777720056897973 565611949104161255334185)
                    ·
                      refine ⟨424208961828120941500639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565611949104161255334185 424208961828120941500639)
                      ·
                        rfl

theorem cell23_826144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_826144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826144 prefixEnd_826144 := by exact prefixLift 826144
  have htrace : WordTrace (prefixWord ++ tailWord_826144) baseStart_826144 baseEnd_826144 := by
    simpa [prefixWord, tailWord_826144, baseEnd_826144] using wordTrace_append hprefix tailTrace_826144
  have hstable : (prefixWord ++ tailWord_826144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826144).length < 2 ^ (prefixWord ++ tailWord_826144).sum := by decide
  have hdescent : baseEnd_826144 < baseStart_826144 := by decide
  rcases family_descends (prefixWord ++ tailWord_826144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826160 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_826160 : Nat := 118140960795 + 826160 * 2 ^ 59
def prefixEnd_826160 : Nat := 4983230072969 + 3 ^ 40 * 826160 * 2
def baseEnd_826160 : Nat := 424217177518592878900565

theorem tailTrace_826160 : CollatzResearch.WordTrace tailWord_826160 prefixEnd_826160 424217177518592878900565 := by
  unfold tailWord_826160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15066265343485445869905967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20088353791313927826541289 15066265343485445869905967)
  ·
    refine ⟨22599398015228168804858951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15066265343485445869905967 22599398015228168804858951)
    ·
      refine ⟨33899097022842253207288427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22599398015228168804858951 33899097022842253207288427)
      ·
        refine ⟨50848645534263379810932641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33899097022842253207288427 50848645534263379810932641)
        ·
          refine ⟨38136484150697534858199481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50848645534263379810932641 38136484150697534858199481)
          ·
            refine ⟨28602363113023151143649611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38136484150697534858199481 28602363113023151143649611)
            ·
              refine ⟨42903544669534726715474417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28602363113023151143649611 42903544669534726715474417)
              ·
                refine ⟨32177658502151045036605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42903544669534726715474417 32177658502151045036605813)
                ·
                  refine ⟨3016655484576660472181795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32177658502151045036605813 3016655484576660472181795)
                  ·
                    refine ⟨4524983226864990708272693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3016655484576660472181795 4524983226864990708272693)
                    ·
                      refine ⟨424217177518592878900565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4524983226864990708272693 424217177518592878900565)
                      ·
                        rfl

theorem cell23_826160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_826160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826160 prefixEnd_826160 := by exact prefixLift 826160
  have htrace : WordTrace (prefixWord ++ tailWord_826160) baseStart_826160 baseEnd_826160 := by
    simpa [prefixWord, tailWord_826160, baseEnd_826160] using wordTrace_append hprefix tailTrace_826160
  have hstable : (prefixWord ++ tailWord_826160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826160).length < 2 ^ (prefixWord ++ tailWord_826160).sum := by decide
  have hdescent : baseEnd_826160 < baseStart_826160 := by decide
  rcases family_descends (prefixWord ++ tailWord_826160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826167 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 4, 4]
def baseStart_826167 : Nat := 118140960795 + 826167 * 2 ^ 59
def prefixEnd_826167 : Nat := 4983230072969 + 3 ^ 40 * 826167 * 2
def baseEnd_826167 : Nat := 141406923961058117171011

theorem tailTrace_826167 : CollatzResearch.WordTrace tailWord_826167 prefixEnd_826167 141406923961058117171011 := by
  unfold tailWord_826167
  simp only [CollatzResearch.WordTrace]
  refine ⟨30132785997945531935316755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20088523998630354623544503 30132785997945531935316755)
  ·
    refine ⟨45199178996918297902975133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30132785997945531935316755 45199178996918297902975133)
    ·
      refine ⟨16949692123844361713615675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45199178996918297902975133 16949692123844361713615675)
      ·
        refine ⟨25424538185766542570423513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16949692123844361713615675 25424538185766542570423513)
        ·
          refine ⟨19068403639324906927817635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25424538185766542570423513 19068403639324906927817635)
          ·
            refine ⟨28602605458987360391726453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19068403639324906927817635 28602605458987360391726453)
            ·
              refine ⟨2681494261780065036724355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28602605458987360391726453 2681494261780065036724355)
              ·
                refine ⟨4022241392670097555086533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681494261780065036724355 4022241392670097555086533)
                ·
                  refine ⟨754170261125643291578725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4022241392670097555086533 754170261125643291578725)
                  ·
                    refine ⟨141406923961058117171011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 754170261125643291578725 141406923961058117171011)
                    ·
                      rfl

theorem cell23_826167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_826167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826167 prefixEnd_826167 := by exact prefixLift 826167
  have htrace : WordTrace (prefixWord ++ tailWord_826167) baseStart_826167 baseEnd_826167 := by
    simpa [prefixWord, tailWord_826167, baseEnd_826167] using wordTrace_append hprefix tailTrace_826167
  have hstable : (prefixWord ++ tailWord_826167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826167).length < 2 ^ (prefixWord ++ tailWord_826167).sum := by decide
  have hdescent : baseEnd_826167 < baseStart_826167 := by decide
  rcases family_descends (prefixWord ++ tailWord_826167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826200 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_826200 : Nat := 118140960795 + 826200 * 2 ^ 59
def prefixEnd_826200 : Nat := 4983230072969 + 3 ^ 40 * 826200 * 2
def baseEnd_826200 : Nat := 424237716744772722400381

theorem tailTrace_826200 : CollatzResearch.WordTrace tailWord_826200 prefixEnd_826200 424237716744772722400381 := by
  unfold tailWord_826200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15066994803412989285634027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20089326404550652380845369 15066994803412989285634027)
  ·
    refine ⟨22600492205119483928451041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15066994803412989285634027 22600492205119483928451041)
    ·
      refine ⟨16950369153839612946338281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22600492205119483928451041 16950369153839612946338281)
      ·
        refine ⟨12712776865379709709753711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16950369153839612946338281 12712776865379709709753711)
        ·
          refine ⟨19069165298069564564630567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12712776865379709709753711 19069165298069564564630567)
          ·
            refine ⟨28603747947104346846945851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19069165298069564564630567 28603747947104346846945851)
            ·
              refine ⟨42905621920656520270418777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28603747947104346846945851 42905621920656520270418777)
              ·
                refine ⟨32179216440492390202814083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42905621920656520270418777 32179216440492390202814083)
                ·
                  refine ⟨48268824660738585304221125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32179216440492390202814083 48268824660738585304221125)
                  ·
                    refine ⟨9050404623888484744541461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48268824660738585304221125 9050404623888484744541461)
                    ·
                      refine ⟨424237716744772722400381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9050404623888484744541461 424237716744772722400381)
                      ·
                        rfl

theorem cell23_826200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_826200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826200 prefixEnd_826200 := by exact prefixLift 826200
  have htrace : WordTrace (prefixWord ++ tailWord_826200) baseStart_826200 baseEnd_826200 := by
    simpa [prefixWord, tailWord_826200, baseEnd_826200] using wordTrace_append hprefix tailTrace_826200
  have hstable : (prefixWord ++ tailWord_826200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826200).length < 2 ^ (prefixWord ++ tailWord_826200).sum := by decide
  have hdescent : baseEnd_826200 < baseStart_826200 := by decide
  rcases family_descends (prefixWord ++ tailWord_826200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826207 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 3]
def baseStart_826207 : Nat := 118140960795 + 826207 * 2 ^ 59
def prefixEnd_826207 : Nat := 4983230072969 + 3 ^ 40 * 826207 * 2
def baseEnd_826207 : Nat := 424241311109354195012849

theorem tailTrace_826207 : CollatzResearch.WordTrace tailWord_826207 prefixEnd_826207 424241311109354195012849 := by
  unfold tailWord_826207
  simp only [CollatzResearch.WordTrace]
  refine ⟨30134244917800618766772875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20089496611867079177848583 30134244917800618766772875)
  ·
    refine ⟨45201367376700928150159313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30134244917800618766772875 45201367376700928150159313)
    ·
      refine ⟨33901025532525696112619485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45201367376700928150159313 33901025532525696112619485)
      ·
        refine ⟨12712884574697136042232307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33901025532525696112619485 12712884574697136042232307)
        ·
          refine ⟨19069326862045704063348461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12712884574697136042232307 19069326862045704063348461)
          ·
            refine ⟨7150997573267139023755673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19069326862045704063348461 7150997573267139023755673)
            ·
              refine ⟨5363248179950354267816755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150997573267139023755673 5363248179950354267816755)
              ·
                refine ⟨8044872269925531401725133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363248179950354267816755 8044872269925531401725133)
                ·
                  refine ⟨3016827101222074275646925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8044872269925531401725133 3016827101222074275646925)
                  ·
                    refine ⟨1131310162958277853367597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016827101222074275646925 1131310162958277853367597)
                    ·
                      refine ⟨424241311109354195012849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1131310162958277853367597 424241311109354195012849)
                      ·
                        rfl

theorem cell23_826207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_826207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826207 prefixEnd_826207 := by exact prefixLift 826207
  have htrace : WordTrace (prefixWord ++ tailWord_826207) baseStart_826207 baseEnd_826207 := by
    simpa [prefixWord, tailWord_826207, baseEnd_826207] using wordTrace_append hprefix tailTrace_826207
  have hstable : (prefixWord ++ tailWord_826207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826207).length < 2 ^ (prefixWord ++ tailWord_826207).sum := by decide
  have hdescent : baseEnd_826207 < baseStart_826207 := by decide
  rcases family_descends (prefixWord ++ tailWord_826207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826224 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 4, 1, 3]
def baseStart_826224 : Nat := 118140960795 + 826224 * 2 ^ 59
def prefixEnd_826224 : Nat := 4983230072969 + 3 ^ 40 * 826224 * 2
def baseEnd_826224 : Nat := 424250040280480628500271

theorem tailTrace_826224 : CollatzResearch.WordTrace tailWord_826224 prefixEnd_826224 424250040280480628500271 := by
  unfold tailWord_826224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067432479369515335070863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20089909972492687113427817 15067432479369515335070863)
  ·
    refine ⟨22601148719054273002606295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067432479369515335070863 22601148719054273002606295)
    ·
      refine ⟨33901723078581409503909443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22601148719054273002606295 33901723078581409503909443)
      ·
        refine ⟨50852584617872114255864165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33901723078581409503909443 50852584617872114255864165)
        ·
          refine ⟨9534859615851021422974531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50852584617872114255864165 9534859615851021422974531)
          ·
            refine ⟨14302289423776532134461797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534859615851021422974531 14302289423776532134461797)
            ·
              refine ⟨2681679266958099775211587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14302289423776532134461797 2681679266958099775211587)
              ·
                refine ⟨4022518900437149662817381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681679266958099775211587 4022518900437149662817381)
                ·
                  refine ⟨754222293831965561778259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4022518900437149662817381 754222293831965561778259)
                  ·
                    refine ⟨1131333440747948342667389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754222293831965561778259 1131333440747948342667389)
                    ·
                      refine ⟨424250040280480628500271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1131333440747948342667389 424250040280480628500271)
                      ·
                        rfl

theorem cell23_826224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_826224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826224 prefixEnd_826224 := by exact prefixLift 826224
  have htrace : WordTrace (prefixWord ++ tailWord_826224) baseStart_826224 baseEnd_826224 := by
    simpa [prefixWord, tailWord_826224, baseEnd_826224] using wordTrace_append hprefix tailTrace_826224
  have hstable : (prefixWord ++ tailWord_826224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826224).length < 2 ^ (prefixWord ++ tailWord_826224).sum := by decide
  have hdescent : baseEnd_826224 < baseStart_826224 := by decide
  rcases family_descends (prefixWord ++ tailWord_826224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826225 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 1, 2, 2]
def baseStart_826225 : Nat := 118140960795 + 826225 * 2 ^ 59
def prefixEnd_826225 : Nat := 4983230072969 + 3 ^ 40 * 826225 * 2
def baseEnd_826225 : Nat := 424250553761135124587767

theorem tailTrace_826225 : CollatzResearch.WordTrace tailWord_826225 prefixEnd_826225 424250553761135124587767 := by
  unfold tailWord_826225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30134901431735407840928129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20089934287823605227285419 30134901431735407840928129)
  ·
    refine ⟨22601176073801555880696097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30134901431735407840928129 22601176073801555880696097)
    ·
      refine ⟨16950882055351166910522073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22601176073801555880696097 16950882055351166910522073)
      ·
        refine ⟨12713161541513375182891555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16950882055351166910522073 12713161541513375182891555)
        ·
          refine ⟨19069742312270062774337333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12713161541513375182891555 19069742312270062774337333)
          ·
            refine ⟨1787788341775318385094125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19069742312270062774337333 1787788341775318385094125)
            ·
              refine ⟨670420628165744394410297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1787788341775318385094125 670420628165744394410297)
              ·
                refine ⟨502815471124308295807723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670420628165744394410297 502815471124308295807723)
                ·
                  refine ⟨754223206686462443711585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502815471124308295807723 754223206686462443711585)
                  ·
                    refine ⟨565667405014846832783689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 754223206686462443711585 565667405014846832783689)
                    ·
                      refine ⟨424250553761135124587767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565667405014846832783689 424250553761135124587767)
                      ·
                        rfl

theorem cell23_826225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_826225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826225 prefixEnd_826225 := by exact prefixLift 826225
  have htrace : WordTrace (prefixWord ++ tailWord_826225) baseStart_826225 baseEnd_826225 := by
    simpa [prefixWord, tailWord_826225, baseEnd_826225] using wordTrace_append hprefix tailTrace_826225
  have hstable : (prefixWord ++ tailWord_826225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826225).length < 2 ^ (prefixWord ++ tailWord_826225).sum := by decide
  have hdescent : baseEnd_826225 < baseStart_826225 := by decide
  rcases family_descends (prefixWord ++ tailWord_826225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826234 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2]
def baseStart_826234 : Nat := 118140960795 + 826234 * 2 ^ 59
def prefixEnd_826234 : Nat := 4983230072969 + 3 ^ 40 * 826234 * 2
def baseEnd_826234 : Nat := 424255175087025589375225

theorem tailTrace_826234 : CollatzResearch.WordTrace tailWord_826234 prefixEnd_826234 424255175087025589375225 := by
  unfold tailWord_826234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533807422175700594501439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20090153125801868252003837 7533807422175700594501439)
  ·
    refine ⟨11300711133263550891752159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7533807422175700594501439 11300711133263550891752159)
    ·
      refine ⟨16951066699895326337628239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11300711133263550891752159 16951066699895326337628239)
      ·
        refine ⟨25426600049842989506442359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16951066699895326337628239 25426600049842989506442359)
        ·
          refine ⟨38139900074764484259663539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25426600049842989506442359 38139900074764484259663539)
          ·
            refine ⟨57209850112146726389495309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38139900074764484259663539 57209850112146726389495309)
            ·
              refine ⟨21453693792055022396060741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57209850112146726389495309 21453693792055022396060741)
              ·
                refine ⟨4022567586010316699261389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21453693792055022396060741 4022567586010316699261389)
                ·
                  refine ⟨1508462844753868762223021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4022567586010316699261389 1508462844753868762223021)
                  ·
                    refine ⟨565673566782700785833633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508462844753868762223021 565673566782700785833633)
                    ·
                      refine ⟨424255175087025589375225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565673566782700785833633 424255175087025589375225)
                      ·
                        rfl

theorem cell23_826234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_826234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826234 prefixEnd_826234 := by exact prefixLift 826234
  have htrace : WordTrace (prefixWord ++ tailWord_826234) baseStart_826234 baseEnd_826234 := by
    simpa [prefixWord, tailWord_826234, baseEnd_826234] using wordTrace_append hprefix tailTrace_826234
  have hstable : (prefixWord ++ tailWord_826234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826234).length < 2 ^ (prefixWord ++ tailWord_826234).sum := by decide
  have hdescent : baseEnd_826234 < baseStart_826234 := by decide
  rcases family_descends (prefixWord ++ tailWord_826234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826242 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_826242 : Nat := 118140960795 + 826242 * 2 ^ 59
def prefixEnd_826242 : Nat := 4983230072969 + 3 ^ 40 * 826242 * 2
def baseEnd_826242 : Nat := 424259282932261558075189

theorem tailTrace_826242 : CollatzResearch.WordTrace tailWord_826242 prefixEnd_826242 424259282932261558075189 := by
  unfold tailWord_826242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533880368168454936074245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20090347648449213162864653 7533880368168454936074245)
  ·
    refine ⟨1412602569031585300513921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7533880368168454936074245 1412602569031585300513921)
    ·
      refine ⟨1059451926773688975385441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1412602569031585300513921 1059451926773688975385441)
      ·
        refine ⟨794588945080266731539081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059451926773688975385441 794588945080266731539081)
        ·
          refine ⟨595941708810200048654311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 794588945080266731539081 595941708810200048654311)
          ·
            refine ⟨893912563215300072981467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595941708810200048654311 893912563215300072981467)
            ·
              refine ⟨1340868844822950109472201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893912563215300072981467 1340868844822950109472201)
              ·
                refine ⟨1005651633617212582104151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340868844822950109472201 1005651633617212582104151)
                ·
                  refine ⟨1508477450425818873156227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005651633617212582104151 1508477450425818873156227)
                  ·
                    refine ⟨2262716175638728309734341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1508477450425818873156227 2262716175638728309734341)
                    ·
                      refine ⟨424259282932261558075189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2262716175638728309734341 424259282932261558075189)
                      ·
                        rfl

theorem cell23_826242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_826242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826242 prefixEnd_826242 := by exact prefixLift 826242
  have htrace : WordTrace (prefixWord ++ tailWord_826242) baseStart_826242 baseEnd_826242 := by
    simpa [prefixWord, tailWord_826242, baseEnd_826242] using wordTrace_append hprefix tailTrace_826242
  have hstable : (prefixWord ++ tailWord_826242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826242).length < 2 ^ (prefixWord ++ tailWord_826242).sum := by decide
  have hdescent : baseEnd_826242 < baseStart_826242 := by decide
  rcases family_descends (prefixWord ++ tailWord_826242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826251 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 1, 3, 2]
def baseStart_826251 : Nat := 118140960795 + 826251 * 2 ^ 59
def prefixEnd_826251 : Nat := 4983230072969 + 3 ^ 40 * 826251 * 2
def baseEnd_826251 : Nat := 424263904258152022862647

theorem tailTrace_826251 : CollatzResearch.WordTrace tailWord_826251 prefixEnd_826251 424263904258152022862647 := by
  unfold tailWord_826251
  simp only [CollatzResearch.WordTrace]
  refine ⟨30135849729641214281374607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20090566486427476187583071 30135849729641214281374607)
  ·
    refine ⟨45203774594461821422061911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30135849729641214281374607 45203774594461821422061911)
    ·
      refine ⟨67805661891692732133092867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45203774594461821422061911 67805661891692732133092867)
      ·
        refine ⟨101708492837539098199639301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67805661891692732133092867 101708492837539098199639301)
        ·
          refine ⟨19070342407038580912432369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101708492837539098199639301 19070342407038580912432369)
          ·
            refine ⟨14302756805278935684324277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19070342407038580912432369 14302756805278935684324277)
            ·
              refine ⟨1340883450494900220405401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14302756805278935684324277 1340883450494900220405401)
              ·
                refine ⟨1005662587871175165304051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340883450494900220405401 1005662587871175165304051)
                ·
                  refine ⟨1508493881806762747956077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005662587871175165304051 1508493881806762747956077)
                  ·
                    refine ⟨565685205677536030483529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508493881806762747956077 565685205677536030483529)
                    ·
                      refine ⟨424263904258152022862647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565685205677536030483529 424263904258152022862647)
                      ·
                        rfl

theorem cell23_826251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 3, 2].length) (baseStart_826251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826251 prefixEnd_826251 := by exact prefixLift 826251
  have htrace : WordTrace (prefixWord ++ tailWord_826251) baseStart_826251 baseEnd_826251 := by
    simpa [prefixWord, tailWord_826251, baseEnd_826251] using wordTrace_append hprefix tailTrace_826251
  have hstable : (prefixWord ++ tailWord_826251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826251).length < 2 ^ (prefixWord ++ tailWord_826251).sum := by decide
  have hdescent : baseEnd_826251 < baseStart_826251 := by decide
  rcases family_descends (prefixWord ++ tailWord_826251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826262 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_826262 : Nat := 118140960795 + 826262 * 2 ^ 59
def prefixEnd_826262 : Nat := 4983230072969 + 3 ^ 40 * 826262 * 2
def baseEnd_826262 : Nat := 424269552545351479825097

theorem tailTrace_826262 : CollatzResearch.WordTrace tailWord_826262 prefixEnd_826262 424269552545351479825097 := by
  unfold tailWord_826262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1883515683287585197501565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20090833955067575440016693 1883515683287585197501565)
  ·
    refine ⟨706318381232844449063087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1883515683287585197501565 706318381232844449063087)
    ·
      refine ⟨1059477571849266673594631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706318381232844449063087 1059477571849266673594631)
      ·
        refine ⟨1589216357773900010391947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059477571849266673594631 1589216357773900010391947)
        ·
          refine ⟨2383824536660850015587921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589216357773900010391947 2383824536660850015587921)
          ·
            refine ⟨1787868402495637511690941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383824536660850015587921 1787868402495637511690941)
            ·
              refine ⟨670450650935864066884103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1787868402495637511690941 670450650935864066884103)
              ·
                refine ⟨1005675976403796100326155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670450650935864066884103 1005675976403796100326155)
                ·
                  refine ⟨1508513964605694150489233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005675976403796100326155 1508513964605694150489233)
                  ·
                    refine ⟨1131385473454270612866925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1508513964605694150489233 1131385473454270612866925)
                    ·
                      refine ⟨424269552545351479825097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1131385473454270612866925 424269552545351479825097)
                      ·
                        rfl

theorem cell23_826262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_826262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826262 prefixEnd_826262 := by exact prefixLift 826262
  have htrace : WordTrace (prefixWord ++ tailWord_826262) baseStart_826262 baseEnd_826262 := by
    simpa [prefixWord, tailWord_826262, baseEnd_826262] using wordTrace_append hprefix tailTrace_826262
  have hstable : (prefixWord ++ tailWord_826262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826262).length < 2 ^ (prefixWord ++ tailWord_826262).sum := by decide
  have hdescent : baseEnd_826262 < baseStart_826262 := by decide
  rcases family_descends (prefixWord ++ tailWord_826262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826327 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_826327 : Nat := 118140960795 + 826327 * 2 ^ 59
def prefixEnd_826327 : Nat := 4983230072969 + 3 ^ 40 * 826327 * 2
def baseEnd_826327 : Nat := 424302928787893725512297

theorem tailTrace_826327 : CollatzResearch.WordTrace tailWord_826327 prefixEnd_826327 424302928787893725512297 := by
  unfold tailWord_826327
  simp only [CollatzResearch.WordTrace]
  refine ⟨30138621677365879261141235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20092414451577252840760823 30138621677365879261141235)
  ·
    refine ⟨45207932516048818891711853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30138621677365879261141235 45207932516048818891711853)
    ·
      refine ⟨16952974693518307084391945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45207932516048818891711853 16952974693518307084391945)
      ·
        refine ⟨12714731020138730313293959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16952974693518307084391945 12714731020138730313293959)
        ·
          refine ⟨19072096530208095469940939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12714731020138730313293959 19072096530208095469940939)
          ·
            refine ⟨28608144795312143204911409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19072096530208095469940939 28608144795312143204911409)
            ·
              refine ⟨21456108596484107403683557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28608144795312143204911409 21456108596484107403683557)
              ·
                refine ⟨4023020361840770138190667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21456108596484107403683557 4023020361840770138190667)
                ·
                  refine ⟨6034530542761155207286001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023020361840770138190667 6034530542761155207286001)
                  ·
                    refine ⟨4525897907070866405464501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034530542761155207286001 4525897907070866405464501)
                    ·
                      refine ⟨424302928787893725512297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4525897907070866405464501 424302928787893725512297)
                      ·
                        rfl

theorem cell23_826327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_826327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826327 prefixEnd_826327 := by exact prefixLift 826327
  have htrace : WordTrace (prefixWord ++ tailWord_826327) baseStart_826327 baseEnd_826327 := by
    simpa [prefixWord, tailWord_826327, baseEnd_826327] using wordTrace_append hprefix tailTrace_826327
  have hstable : (prefixWord ++ tailWord_826327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826327).length < 2 ^ (prefixWord ++ tailWord_826327).sum := by decide
  have hdescent : baseEnd_826327 < baseStart_826327 := by decide
  rcases family_descends (prefixWord ++ tailWord_826327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826338 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 5]
def baseStart_826338 : Nat := 118140960795 + 826338 * 2 ^ 59
def prefixEnd_826338 : Nat := 4983230072969 + 3 ^ 40 * 826338 * 2
def baseEnd_826338 : Nat := 47145397452788131386083

theorem tailTrace_826338 : CollatzResearch.WordTrace tailWord_826338 prefixEnd_826338 47145397452788131386083 := by
  unfold tailWord_826338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534755720081507034947917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20092681920217352093194445 7534755720081507034947917)
  ·
    refine ⟨2825533395030565138105469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7534755720081507034947917 2825533395030565138105469)
    ·
      refine ⟨1059575023136461926789551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2825533395030565138105469 1059575023136461926789551)
      ·
        refine ⟨1589362534704692890184327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059575023136461926789551 1589362534704692890184327)
        ·
          refine ⟨2384043802057039335276491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589362534704692890184327 2384043802057039335276491)
          ·
            refine ⟨3576065703085559002914737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384043802057039335276491 3576065703085559002914737)
            ·
              refine ⟨2682049277314169252186053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576065703085559002914737 2682049277314169252186053)
              ·
                refine ⟨502884239496406734784885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2682049277314169252186053 502884239496406734784885)
                ·
                  refine ⟨47145397452788131386083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 502884239496406734784885 47145397452788131386083)
                  ·
                    rfl

theorem cell23_826338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_826338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826338 prefixEnd_826338 := by exact prefixLift 826338
  have htrace : WordTrace (prefixWord ++ tailWord_826338) baseStart_826338 baseEnd_826338 := by
    simpa [prefixWord, tailWord_826338, baseEnd_826338] using wordTrace_append hprefix tailTrace_826338
  have hstable : (prefixWord ++ tailWord_826338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826338).length < 2 ^ (prefixWord ++ tailWord_826338).sum := by decide
  have hdescent : baseEnd_826338 < baseStart_826338 := by decide
  rcases family_descends (prefixWord ++ tailWord_826338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826391 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_826391 : Nat := 118140960795 + 826391 * 2 ^ 59
def prefixEnd_826391 : Nat := 4983230072969 + 3 ^ 40 * 826391 * 2
def baseEnd_826391 : Nat := 424335791549781475112003

theorem tailTrace_826391 : CollatzResearch.WordTrace tailWord_826391 prefixEnd_826391 424335791549781475112003 := by
  unfold tailWord_826391
  simp only [CollatzResearch.WordTrace]
  refine ⟨30140955949134018191471027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20093970632756012127647351 30140955949134018191471027)
  ·
    refine ⟨45211433923701027287206541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30140955949134018191471027 45211433923701027287206541)
    ·
      refine ⟨16954287721387885232702453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45211433923701027287206541 16954287721387885232702453)
      ·
        refine ⟨1589464473880114240565855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16954287721387885232702453 1589464473880114240565855)
        ·
          refine ⟨2384196710820171360848783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589464473880114240565855 2384196710820171360848783)
          ·
            refine ⟨3576295066230257041273175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384196710820171360848783 3576295066230257041273175)
            ·
              refine ⟨5364442599345385561909763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576295066230257041273175 5364442599345385561909763)
              ·
                refine ⟨8046663899018078342864645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364442599345385561909763 8046663899018078342864645)
                ·
                  refine ⟨1508749481065889689287121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8046663899018078342864645 1508749481065889689287121)
                  ·
                    refine ⟨1131562110799417266965341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1508749481065889689287121 1131562110799417266965341)
                    ·
                      refine ⟨424335791549781475112003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1131562110799417266965341 424335791549781475112003)
                      ·
                        rfl

theorem cell23_826391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_826391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826391 prefixEnd_826391 := by exact prefixLift 826391
  have htrace : WordTrace (prefixWord ++ tailWord_826391) baseStart_826391 baseEnd_826391 := by
    simpa [prefixWord, tailWord_826391, baseEnd_826391] using wordTrace_append hprefix tailTrace_826391
  have hstable : (prefixWord ++ tailWord_826391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826391).length < 2 ^ (prefixWord ++ tailWord_826391).sum := by decide
  have hdescent : baseEnd_826391 < baseStart_826391 := by decide
  rcases family_descends (prefixWord ++ tailWord_826391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826394 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_826394 : Nat := 118140960795 + 826394 * 2 ^ 59
def prefixEnd_826394 : Nat := 4983230072969 + 3 ^ 40 * 826394 * 2
def baseEnd_826394 : Nat := 47148592443527218152721

theorem tailTrace_826394 : CollatzResearch.WordTrace tailWord_826394 prefixEnd_826394 47148592443527218152721 := by
  unfold tailWord_826394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7535266342030787425957559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20094043578748766469220157 7535266342030787425957559)
  ·
    refine ⟨11302899513046181138936339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7535266342030787425957559 11302899513046181138936339)
    ·
      refine ⟨16954349269569271708404509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11302899513046181138936339 16954349269569271708404509)
      ·
        refine ⟨6357880976088476890651691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16954349269569271708404509 6357880976088476890651691)
        ·
          refine ⟨9536821464132715335977537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357880976088476890651691 9536821464132715335977537)
          ·
            refine ⟨7152616098099536501983153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9536821464132715335977537 7152616098099536501983153)
            ·
              refine ⟨5364462073574652376487365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7152616098099536501983153 5364462073574652376487365)
              ·
                refine ⟨1005836638795247320591381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5364462073574652376487365 1005836638795247320591381)
                ·
                  refine ⟨47148592443527218152721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1005836638795247320591381 47148592443527218152721)
                  ·
                    rfl

theorem cell23_826394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_826394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826394 prefixEnd_826394 := by exact prefixLift 826394
  have htrace : WordTrace (prefixWord ++ tailWord_826394) baseStart_826394 baseEnd_826394 := by
    simpa [prefixWord, tailWord_826394, baseEnd_826394] using wordTrace_append hprefix tailTrace_826394
  have hstable : (prefixWord ++ tailWord_826394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826394).length < 2 ^ (prefixWord ++ tailWord_826394).sum := by decide
  have hdescent : baseEnd_826394 < baseStart_826394 := by decide
  rcases family_descends (prefixWord ++ tailWord_826394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826421 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_826421 : Nat := 118140960795 + 826421 * 2 ^ 59
def prefixEnd_826421 : Nat := 4983230072969 + 3 ^ 40 * 826421 * 2
def baseEnd_826421 : Nat := 424351195969416357736865

theorem tailTrace_826421 : CollatzResearch.WordTrace tailWord_826421 prefixEnd_826421 424351195969416357736865 := by
  unfold tailWord_826421
  simp only [CollatzResearch.WordTrace]
  refine ⟨30142050139025333315063117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20094700092683555543375411 30142050139025333315063117)
  ·
    refine ⟨11303268802134499993148669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30142050139025333315063117 11303268802134499993148669)
    ·
      refine ⟨4238725800800437497430751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11303268802134499993148669 4238725800800437497430751)
      ·
        refine ⟨6358088701200656246146127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238725800800437497430751 6358088701200656246146127)
        ·
          refine ⟨9537133051800984369219191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358088701200656246146127 9537133051800984369219191)
          ·
            refine ⟨14305699577701476553828787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9537133051800984369219191 14305699577701476553828787)
            ·
              refine ⟨21458549366552214830743181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14305699577701476553828787 21458549366552214830743181)
              ·
                refine ⟨8046956012457080561528693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21458549366552214830743181 8046956012457080561528693)
                ·
                  refine ⟨754402126167851302643315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8046956012457080561528693 754402126167851302643315)
                  ·
                    refine ⟨1131603189251776953964973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754402126167851302643315 1131603189251776953964973)
                    ·
                      refine ⟨424351195969416357736865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1131603189251776953964973 424351195969416357736865)
                      ·
                        rfl

theorem cell23_826421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_826421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826421 prefixEnd_826421 := by exact prefixLift 826421
  have htrace : WordTrace (prefixWord ++ tailWord_826421) baseStart_826421 baseEnd_826421 := by
    simpa [prefixWord, tailWord_826421, baseEnd_826421] using wordTrace_append hprefix tailTrace_826421
  have hstable : (prefixWord ++ tailWord_826421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826421).length < 2 ^ (prefixWord ++ tailWord_826421).sum := by decide
  have hdescent : baseEnd_826421 < baseStart_826421 := by decide
  rcases family_descends (prefixWord ++ tailWord_826421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826464 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_826464 : Nat := 118140960795 + 826464 * 2 ^ 59
def prefixEnd_826464 : Nat := 4983230072969 + 3 ^ 40 * 826464 * 2
def baseEnd_826464 : Nat := 424373275637559689499167

theorem tailTrace_826464 : CollatzResearch.WordTrace tailWord_826464 prefixEnd_826464 424373275637559689499167 := by
  unfold tailWord_826464
  simp only [CollatzResearch.WordTrace]
  refine ⟨15071809238934775829439223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20095745651913034439252297 15071809238934775829439223)
  ·
    refine ⟨22607713858402163744158835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15071809238934775829439223 22607713858402163744158835)
    ·
      refine ⟨33911570787603245616238253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22607713858402163744158835 33911570787603245616238253)
      ·
        refine ⟨12716839045351217106089345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33911570787603245616238253 12716839045351217106089345)
        ·
          refine ⟨9537629284013412829567009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12716839045351217106089345 9537629284013412829567009)
          ·
            refine ⟨7153221963010059622175257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9537629284013412829567009 7153221963010059622175257)
            ·
              refine ⟨5364916472257544716631443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7153221963010059622175257 5364916472257544716631443)
              ·
                refine ⟨8047374708386317074947165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364916472257544716631443 8047374708386317074947165)
                ·
                  refine ⟨3017765515644868903105187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8047374708386317074947165 3017765515644868903105187)
                  ·
                    refine ⟨4526648273467303354657781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017765515644868903105187 4526648273467303354657781)
                    ·
                      refine ⟨424373275637559689499167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4526648273467303354657781 424373275637559689499167)
                      ·
                        rfl

theorem cell23_826464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_826464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826464 prefixEnd_826464 := by exact prefixLift 826464
  have htrace : WordTrace (prefixWord ++ tailWord_826464) baseStart_826464 baseEnd_826464 := by
    simpa [prefixWord, tailWord_826464, baseEnd_826464] using wordTrace_append hprefix tailTrace_826464
  have hstable : (prefixWord ++ tailWord_826464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826464).length < 2 ^ (prefixWord ++ tailWord_826464).sum := by decide
  have hdescent : baseEnd_826464 < baseStart_826464 := by decide
  rcases family_descends (prefixWord ++ tailWord_826464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826471 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 1, 6]
def baseStart_826471 : Nat := 118140960795 + 826471 * 2 ^ 59
def prefixEnd_826471 : Nat := 4983230072969 + 3 ^ 40 * 826471 * 2
def baseEnd_826471 : Nat := 141458956667380387370545

theorem tailTrace_826471 : CollatzResearch.WordTrace tailWord_826471 prefixEnd_826471 141458956667380387370545 := by
  unfold tailWord_826471
  simp only [CollatzResearch.WordTrace]
  refine ⟨30143873788844191854383267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20095915859229461236255511 30143873788844191854383267)
  ·
    refine ⟨45215810683266287781574901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30143873788844191854383267 45215810683266287781574901)
    ·
      refine ⟨4238982251556214479522647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45215810683266287781574901 4238982251556214479522647)
      ·
        refine ⟨6358473377334321719283971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238982251556214479522647 6358473377334321719283971)
        ·
          refine ⟨9537710066001482578925957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358473377334321719283971 9537710066001482578925957)
          ·
            refine ⟨1788320637375277983548617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9537710066001482578925957 1788320637375277983548617)
            ·
              refine ⟨1341240478031458487661463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788320637375277983548617 1341240478031458487661463)
              ·
                refine ⟨2011860717047187731492195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341240478031458487661463 2011860717047187731492195)
                ·
                  refine ⟨3017791075570781597238293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011860717047187731492195 3017791075570781597238293)
                  ·
                    refine ⟨141458956667380387370545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3017791075570781597238293 141458956667380387370545)
                    ·
                      rfl

theorem cell23_826471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_826471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826471 prefixEnd_826471 := by exact prefixLift 826471
  have htrace : WordTrace (prefixWord ++ tailWord_826471) baseStart_826471 baseEnd_826471 := by
    simpa [prefixWord, tailWord_826471, baseEnd_826471] using wordTrace_append hprefix tailTrace_826471
  have hstable : (prefixWord ++ tailWord_826471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826471).length < 2 ^ (prefixWord ++ tailWord_826471).sum := by decide
  have hdescent : baseEnd_826471 < baseStart_826471 := by decide
  rcases family_descends (prefixWord ++ tailWord_826471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826589 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_826589 : Nat := 118140960795 + 826589 * 2 ^ 59
def prefixEnd_826589 : Nat := 4983230072969 + 3 ^ 40 * 826589 * 2
def baseEnd_826589 : Nat := 424437460719371700436093

theorem tailTrace_826589 : CollatzResearch.WordTrace tailWord_826589 prefixEnd_826589 424437460719371700436093 := by
  unfold tailWord_826589
  simp only [CollatzResearch.WordTrace]
  refine ⟨30148177602416698007178821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20098785068277798671452547 30148177602416698007178821)
  ·
    refine ⟨5652783300453130876346029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30148177602416698007178821 5652783300453130876346029)
    ·
      refine ⟨2119793737669924078629761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5652783300453130876346029 2119793737669924078629761)
      ·
        refine ⟨1589845303252443058972321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2119793737669924078629761 1589845303252443058972321)
        ·
          refine ⟨1192383977439332294229241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589845303252443058972321 1192383977439332294229241)
          ·
            refine ⟨894287983079499220671931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192383977439332294229241 894287983079499220671931)
            ·
              refine ⟨1341431974619248831007897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894287983079499220671931 1341431974619248831007897)
              ·
                refine ⟨1006073980964436623255923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341431974619248831007897 1006073980964436623255923)
                ·
                  refine ⟨1509110971446654934883885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006073980964436623255923 1509110971446654934883885)
                  ·
                    refine ⟨565916614292495600581457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509110971446654934883885 565916614292495600581457)
                    ·
                      refine ⟨424437460719371700436093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565916614292495600581457 424437460719371700436093)
                      ·
                        rfl

theorem cell23_826589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_826589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826589 prefixEnd_826589 := by exact prefixLift 826589
  have htrace : WordTrace (prefixWord ++ tailWord_826589) baseStart_826589 baseEnd_826589 := by
    simpa [prefixWord, tailWord_826589, baseEnd_826589] using wordTrace_append hprefix tailTrace_826589
  have hstable : (prefixWord ++ tailWord_826589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826589).length < 2 ^ (prefixWord ++ tailWord_826589).sum := by decide
  have hdescent : baseEnd_826589 < baseStart_826589 := by decide
  rcases family_descends (prefixWord ++ tailWord_826589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826625 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 5]
def baseStart_826625 : Nat := 118140960795 + 826625 * 2 ^ 59
def prefixEnd_826625 : Nat := 4983230072969 + 3 ^ 40 * 826625 * 2
def baseEnd_826625 : Nat := 47161771780325951065103

theorem tailTrace_826625 : CollatzResearch.WordTrace tailWord_826625 prefixEnd_826625 47161771780325951065103 := by
  unfold tailWord_826625
  simp only [CollatzResearch.WordTrace]
  refine ⟨30149490630286276155489329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20099660420190850770326219 30149490630286276155489329)
  ·
    refine ⟨22612117972714707116616997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30149490630286276155489329 22612117972714707116616997)
    ·
      refine ⟨4239772119884007584365687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22612117972714707116616997 4239772119884007584365687)
      ·
        refine ⟨6359658179826011376548531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239772119884007584365687 6359658179826011376548531)
        ·
          refine ⟨9539487269739017064822797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359658179826011376548531 9539487269739017064822797)
          ·
            refine ⟨3577307726152131399308549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9539487269739017064822797 3577307726152131399308549)
            ·
              refine ⟨670745198653524637370353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3577307726152131399308549 670745198653524637370353)
              ·
                refine ⟨503058898990143478027765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670745198653524637370353 503058898990143478027765)
                ·
                  refine ⟨47161771780325951065103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 503058898990143478027765 47161771780325951065103)
                  ·
                    rfl

theorem cell23_826625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 5].length) (baseStart_826625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826625 prefixEnd_826625 := by exact prefixLift 826625
  have htrace : WordTrace (prefixWord ++ tailWord_826625) baseStart_826625 baseEnd_826625 := by
    simpa [prefixWord, tailWord_826625, baseEnd_826625] using wordTrace_append hprefix tailTrace_826625
  have hstable : (prefixWord ++ tailWord_826625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826625).length < 2 ^ (prefixWord ++ tailWord_826625).sum := by decide
  have hdescent : baseEnd_826625 < baseStart_826625 := by decide
  rcases family_descends (prefixWord ++ tailWord_826625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826641 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 4]
def baseStart_826641 : Nat := 118140960795 + 826641 * 2 ^ 59
def prefixEnd_826641 : Nat := 4983230072969 + 3 ^ 40 * 826641 * 2
def baseEnd_826641 : Nat := 424464161713405496985853

theorem tailTrace_826641 : CollatzResearch.WordTrace tailWord_826641 prefixEnd_826641 424464161713405496985853 := by
  unfold tailWord_826641
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150074198228310888071777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20100049465485540592047851 30150074198228310888071777)
  ·
    refine ⟨22612555648671233166053833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30150074198228310888071777 22612555648671233166053833)
    ·
      refine ⟨16959416736503424874540375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22612555648671233166053833 16959416736503424874540375)
      ·
        refine ⟨25439125104755137311810563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16959416736503424874540375 25439125104755137311810563)
        ·
          refine ⟨38158687657132705967715845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25439125104755137311810563 38158687657132705967715845)
          ·
            refine ⟨7154753935712382368946721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38158687657132705967715845 7154753935712382368946721)
            ·
              refine ⟨5366065451784286776710041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154753935712382368946721 5366065451784286776710041)
              ·
                refine ⟨4024549088838215082532531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366065451784286776710041 4024549088838215082532531)
                ·
                  refine ⟨6036823633257322623798797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024549088838215082532531 6036823633257322623798797)
                  ·
                    refine ⟨2263808862471495983924549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6036823633257322623798797 2263808862471495983924549)
                    ·
                      refine ⟨424464161713405496985853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2263808862471495983924549 424464161713405496985853)
                      ·
                        rfl

theorem cell23_826641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_826641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826641 prefixEnd_826641 := by exact prefixLift 826641
  have htrace : WordTrace (prefixWord ++ tailWord_826641) baseStart_826641 baseEnd_826641 := by
    simpa [prefixWord, tailWord_826641, baseEnd_826641] using wordTrace_append hprefix tailTrace_826641
  have hstable : (prefixWord ++ tailWord_826641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826641).length < 2 ^ (prefixWord ++ tailWord_826641).sum := by decide
  have hdescent : baseEnd_826641 < baseStart_826641 := by decide
  rcases family_descends (prefixWord ++ tailWord_826641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826655 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 2, 5]
def baseStart_826655 : Nat := 118140960795 + 826655 * 2 ^ 59
def prefixEnd_826655 : Nat := 4983230072969 + 3 ^ 40 * 826655 * 2
def baseEnd_826655 : Nat := 141490450147522814070263

theorem tailTrace_826655 : CollatzResearch.WordTrace tailWord_826655 prefixEnd_826655 141490450147522814070263 := by
  unfold tailWord_826655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150584820177591279081419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20100389880118394186054279 30150584820177591279081419)
  ·
    refine ⟨45225877230266386918622129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30150584820177591279081419 45225877230266386918622129)
    ·
      refine ⟨33919407922699790188966597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45225877230266386918622129 33919407922699790188966597)
      ·
        refine ⟨6359888985506210660431237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33919407922699790188966597 6359888985506210660431237)
        ·
          refine ⟨1192479184782414498830857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6359888985506210660431237 1192479184782414498830857)
          ·
            refine ⟨894359388586810874123143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192479184782414498830857 894359388586810874123143)
            ·
              refine ⟨1341539082880216311184715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894359388586810874123143 1341539082880216311184715)
              ·
                refine ⟨2012308624320324466777073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341539082880216311184715 2012308624320324466777073)
                ·
                  refine ⟨1509231468240243350082805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2012308624320324466777073 1509231468240243350082805)
                  ·
                    refine ⟨141490450147522814070263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1509231468240243350082805 141490450147522814070263)
                    ·
                      rfl

theorem cell23_826655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_826655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826655 prefixEnd_826655 := by exact prefixLift 826655
  have htrace : WordTrace (prefixWord ++ tailWord_826655) baseStart_826655 baseEnd_826655 := by
    simpa [prefixWord, tailWord_826655, baseEnd_826655] using wordTrace_append hprefix tailTrace_826655
  have hstable : (prefixWord ++ tailWord_826655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826655).length < 2 ^ (prefixWord ++ tailWord_826655).sum := by decide
  have hdescent : baseEnd_826655 < baseStart_826655 := by decide
  rcases family_descends (prefixWord ++ tailWord_826655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826692 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_826692 : Nat := 118140960795 + 826692 * 2 ^ 59
def prefixEnd_826692 : Nat := 4983230072969 + 3 ^ 40 * 826692 * 2
def baseEnd_826692 : Nat := 424490349226784797448119

theorem tailTrace_826692 : CollatzResearch.WordTrace tailWord_826692 prefixEnd_826692 424490349226784797448119 := by
  unfold tailWord_826692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075967160521773299089165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20101289547362364398785553 15075967160521773299089165)
  ·
    refine ⟨5653487685195664987158437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15075967160521773299089165 5653487685195664987158437)
    ·
      refine ⟨1060028940974187185092207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5653487685195664987158437 1060028940974187185092207)
      ·
        refine ⟨1590043411461280777638311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060028940974187185092207 1590043411461280777638311)
        ·
          refine ⟨2385065117191921166457467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590043411461280777638311 2385065117191921166457467)
          ·
            refine ⟨3577597675787881749686201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385065117191921166457467 3577597675787881749686201)
            ·
              refine ⟨2683198256840911312264651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577597675787881749686201 2683198256840911312264651)
              ·
                refine ⟨4024797385261366968396977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683198256840911312264651 4024797385261366968396977)
                ·
                  refine ⟨3018598038946025226297733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024797385261366968396977 3018598038946025226297733)
                  ·
                    refine ⟨565987132302379729930825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3018598038946025226297733 565987132302379729930825)
                    ·
                      refine ⟨424490349226784797448119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 565987132302379729930825 424490349226784797448119)
                      ·
                        rfl

theorem cell23_826692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_826692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826692 prefixEnd_826692 := by exact prefixLift 826692
  have htrace : WordTrace (prefixWord ++ tailWord_826692) baseStart_826692 baseEnd_826692 := by
    simpa [prefixWord, tailWord_826692, baseEnd_826692] using wordTrace_append hprefix tailTrace_826692
  have hstable : (prefixWord ++ tailWord_826692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826692).length < 2 ^ (prefixWord ++ tailWord_826692).sum := by decide
  have hdescent : baseEnd_826692 < baseStart_826692 := by decide
  rcases family_descends (prefixWord ++ tailWord_826692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826708 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_826708 : Nat := 118140960795 + 826708 * 2 ^ 59
def prefixEnd_826708 : Nat := 4983230072969 + 3 ^ 40 * 826708 * 2
def baseEnd_826708 : Nat := 424498564917256734848045

theorem tailTrace_826708 : CollatzResearch.WordTrace tailWord_826708 prefixEnd_826708 424498564917256734848045 := by
  unfold tailWord_826708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15076258944492790665380389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20101678592657054220507185 15076258944492790665380389)
  ·
    refine ⟨2826798552092398249758823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15076258944492790665380389 2826798552092398249758823)
    ·
      refine ⟨4240197828138597374638235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826798552092398249758823 4240197828138597374638235)
      ·
        refine ⟨6360296742207896061957353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240197828138597374638235 6360296742207896061957353)
        ·
          refine ⟨4770222556655922046468015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6360296742207896061957353 4770222556655922046468015)
          ·
            refine ⟨7155333834983883069702023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4770222556655922046468015 7155333834983883069702023)
            ·
              refine ⟨10733000752475824604553035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155333834983883069702023 10733000752475824604553035)
              ·
                refine ⟨16099501128713736906829553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733000752475824604553035 16099501128713736906829553)
                ·
                  refine ⟨12074625846535302680122165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16099501128713736906829553 12074625846535302680122165)
                  ·
                    refine ⟨1131996173112684626261453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12074625846535302680122165 1131996173112684626261453)
                    ·
                      refine ⟨424498564917256734848045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1131996173112684626261453 424498564917256734848045)
                      ·
                        rfl

theorem cell23_826708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_826708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826708 prefixEnd_826708 := by exact prefixLift 826708
  have htrace : WordTrace (prefixWord ++ tailWord_826708) baseStart_826708 baseEnd_826708 := by
    simpa [prefixWord, tailWord_826708, baseEnd_826708] using wordTrace_append hprefix tailTrace_826708
  have hstable : (prefixWord ++ tailWord_826708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826708).length < 2 ^ (prefixWord ++ tailWord_826708).sum := by decide
  have hdescent : baseEnd_826708 < baseStart_826708 := by decide
  rcases family_descends (prefixWord ++ tailWord_826708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826735 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 2, 3, 2]
def baseStart_826735 : Nat := 118140960795 + 826735 * 2 ^ 59
def prefixEnd_826735 : Nat := 4983230072969 + 3 ^ 40 * 826735 * 2
def baseEnd_826735 : Nat := 424512428894928129210421

theorem tailTrace_826735 : CollatzResearch.WordTrace tailWord_826735 prefixEnd_826735 424512428894928129210421 := by
  unfold tailWord_826735
  simp only [CollatzResearch.WordTrace]
  refine ⟨30153502659887764941993659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20102335106591843294662439 30153502659887764941993659)
  ·
    refine ⟨45230253989831647412990489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30153502659887764941993659 45230253989831647412990489)
    ·
      refine ⟨33922690492373735559742867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45230253989831647412990489 33922690492373735559742867)
      ·
        refine ⟨50884035738560603339614301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33922690492373735559742867 50884035738560603339614301)
        ·
          refine ⟨19081513401960226252355363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50884035738560603339614301 19081513401960226252355363)
          ·
            refine ⟨28622270102940339378533045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19081513401960226252355363 28622270102940339378533045)
            ·
              refine ⟨2683337822150656816737473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28622270102940339378533045 2683337822150656816737473)
              ·
                refine ⟨2012503366612992612553105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2683337822150656816737473 2012503366612992612553105)
                ·
                  refine ⟨1509377524959744459414829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2012503366612992612553105 1509377524959744459414829)
                  ·
                    refine ⟨566016571859904172280561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1509377524959744459414829 566016571859904172280561)
                    ·
                      refine ⟨424512428894928129210421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566016571859904172280561 424512428894928129210421)
                      ·
                        rfl

theorem cell23_826735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 3, 2].length) (baseStart_826735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826735 prefixEnd_826735 := by exact prefixLift 826735
  have htrace : WordTrace (prefixWord ++ tailWord_826735) baseStart_826735 baseEnd_826735 := by
    simpa [prefixWord, tailWord_826735, baseEnd_826735] using wordTrace_append hprefix tailTrace_826735
  have hstable : (prefixWord ++ tailWord_826735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826735).length < 2 ^ (prefixWord ++ tailWord_826735).sum := by decide
  have hdescent : baseEnd_826735 < baseStart_826735 := by decide
  rcases family_descends (prefixWord ++ tailWord_826735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826748 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_826748 : Nat := 118140960795 + 826748 * 2 ^ 59
def prefixEnd_826748 : Nat := 4983230072969 + 3 ^ 40 * 826748 * 2
def baseEnd_826748 : Nat := 424519104143436578347861

theorem tailTrace_826748 : CollatzResearch.WordTrace tailWord_826748 prefixEnd_826748 424519104143436578347861 := by
  unfold tailWord_826748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15076988404420334081108449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20102651205893778774811265 15076988404420334081108449)
  ·
    refine ⟨11307741303315250560831337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15076988404420334081108449 11307741303315250560831337)
    ·
      refine ⟨8480805977486437920623503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11307741303315250560831337 8480805977486437920623503)
      ·
        refine ⟨12721208966229656880935255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480805977486437920623503 12721208966229656880935255)
        ·
          refine ⟨19081813449344485321402883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721208966229656880935255 19081813449344485321402883)
          ·
            refine ⟨28622720174016727982104325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19081813449344485321402883 28622720174016727982104325)
            ·
              refine ⟨5366760032628136496644561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28622720174016727982104325 5366760032628136496644561)
              ·
                refine ⟨4025070024471102372483421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5366760032628136496644561 4025070024471102372483421)
                ·
                  refine ⟨1509401259176663389681283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4025070024471102372483421 1509401259176663389681283)
                  ·
                    refine ⟨2264101888764995084521925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1509401259176663389681283 2264101888764995084521925)
                    ·
                      refine ⟨424519104143436578347861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2264101888764995084521925 424519104143436578347861)
                      ·
                        rfl

theorem cell23_826748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_826748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826748 prefixEnd_826748 := by exact prefixLift 826748
  have htrace : WordTrace (prefixWord ++ tailWord_826748) baseStart_826748 baseEnd_826748 := by
    simpa [prefixWord, tailWord_826748, baseEnd_826748] using wordTrace_append hprefix tailTrace_826748
  have hstable : (prefixWord ++ tailWord_826748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826748).length < 2 ^ (prefixWord ++ tailWord_826748).sum := by decide
  have hdescent : baseEnd_826748 < baseStart_826748 := by decide
  rcases family_descends (prefixWord ++ tailWord_826748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826805 : List Nat := [1, 3, 3, 2, 2, 3, 1, 8]
def baseStart_826805 : Nat := 118140960795 + 826805 * 2 ^ 59
def prefixEnd_826805 : Nat := 4983230072969 + 3 ^ 40 * 826805 * 2
def baseEnd_826805 : Nat := 15724013797805290938337

theorem tailTrace_826805 : CollatzResearch.WordTrace tailWord_826805 prefixEnd_826805 15724013797805290938337 := by
  unfold tailWord_826805
  simp only [CollatzResearch.WordTrace]
  refine ⟨30156055769634166897041869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20104037179756111264694579 30156055769634166897041869)
  ·
    refine ⟨11308520913612812586390701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30156055769634166897041869 11308520913612812586390701)
    ·
      refine ⟨4240695342604804719896513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11308520913612812586390701 4240695342604804719896513)
      ·
        refine ⟨3180521506953603539922385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4240695342604804719896513 3180521506953603539922385)
        ·
          refine ⟨2385391130215202654941789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3180521506953603539922385 2385391130215202654941789)
          ·
            refine ⟨894521673830700995603171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2385391130215202654941789 894521673830700995603171)
            ·
              refine ⟨1341782510746051493404757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894521673830700995603171 1341782510746051493404757)
              ·
                refine ⟨15724013797805290938337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1341782510746051493404757 15724013797805290938337)
                ·
                  rfl

theorem cell23_826805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 8].length) (baseStart_826805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826805 prefixEnd_826805 := by exact prefixLift 826805
  have htrace : WordTrace (prefixWord ++ tailWord_826805) baseStart_826805 baseEnd_826805 := by
    simpa [prefixWord, tailWord_826805, baseEnd_826805] using wordTrace_append hprefix tailTrace_826805
  have hstable : (prefixWord ++ tailWord_826805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826805).length < 2 ^ (prefixWord ++ tailWord_826805).sum := by decide
  have hdescent : baseEnd_826805 < baseStart_826805 := by decide
  rcases family_descends (prefixWord ++ tailWord_826805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826812 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_826812 : Nat := 118140960795 + 826812 * 2 ^ 59
def prefixEnd_826812 : Nat := 4983230072969 + 3 ^ 40 * 826812 * 2
def baseEnd_826812 : Nat := 424551966905324327947567

theorem tailTrace_826812 : CollatzResearch.WordTrace tailWord_826812 prefixEnd_826812 424551966905324327947567 := by
  unfold tailWord_826812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15078155540304403546273345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20104207387072538061697793 15078155540304403546273345)
  ·
    refine ⟨11308616655228302659705009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15078155540304403546273345 11308616655228302659705009)
    ·
      refine ⟨8481462491421226994778757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11308616655228302659705009 8481462491421226994778757)
      ·
        refine ⟨1590274217141480061521017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8481462491421226994778757 1590274217141480061521017)
        ·
          refine ⟨1192705662856110046140763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590274217141480061521017 1192705662856110046140763)
          ·
            refine ⟨1789058494284165069211145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192705662856110046140763 1789058494284165069211145)
            ·
              refine ⟨1341793870713123801908359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789058494284165069211145 1341793870713123801908359)
              ·
                refine ⟨2012690806069685702862539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341793870713123801908359 2012690806069685702862539)
                ·
                  refine ⟨3019036209104528554293809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012690806069685702862539 3019036209104528554293809)
                  ·
                    refine ⟨2264277156828396415720357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3019036209104528554293809 2264277156828396415720357)
                    ·
                      refine ⟨424551966905324327947567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2264277156828396415720357 424551966905324327947567)
                      ·
                        rfl

theorem cell23_826812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_826812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826812 prefixEnd_826812 := by exact prefixLift 826812
  have htrace : WordTrace (prefixWord ++ tailWord_826812) baseStart_826812 baseEnd_826812 := by
    simpa [prefixWord, tailWord_826812, baseEnd_826812] using wordTrace_append hprefix tailTrace_826812
  have hstable : (prefixWord ++ tailWord_826812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826812).length < 2 ^ (prefixWord ++ tailWord_826812).sum := by decide
  have hdescent : baseEnd_826812 < baseStart_826812 := by decide
  rcases family_descends (prefixWord ++ tailWord_826812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826836 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_826836 : Nat := 118140960795 + 826836 * 2 ^ 59
def prefixEnd_826836 : Nat := 4983230072969 + 3 ^ 40 * 826836 * 2
def baseEnd_826836 : Nat := 424564290441032234047457

theorem tailTrace_826836 : CollatzResearch.WordTrace tailWord_826836 prefixEnd_826836 424564290441032234047457 := by
  unfold tailWord_826836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15078593216260929595710181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20104790955014572794280241 15078593216260929595710181)
  ·
    refine ⟨2827236228048924299195659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15078593216260929595710181 2827236228048924299195659)
    ·
      refine ⟨4240854342073386448793489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827236228048924299195659 4240854342073386448793489)
      ·
        refine ⟨3180640756555039836595117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4240854342073386448793489 3180640756555039836595117)
        ·
          refine ⟨1192740283708139938723169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3180640756555039836595117 1192740283708139938723169)
          ·
            refine ⟨894555212781104954042377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192740283708139938723169 894555212781104954042377)
            ·
              refine ⟨670916409585828715531783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894555212781104954042377 670916409585828715531783)
              ·
                refine ⟨1006374614378743073297675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670916409585828715531783 1006374614378743073297675)
                ·
                  refine ⟨1509561921568114609946513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006374614378743073297675 1509561921568114609946513)
                  ·
                    refine ⟨1132171441176085957459885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509561921568114609946513 1132171441176085957459885)
                    ·
                      refine ⟨424564290441032234047457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132171441176085957459885 424564290441032234047457)
                      ·
                        rfl

theorem cell23_826836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_826836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826836 prefixEnd_826836 := by exact prefixLift 826836
  have htrace : WordTrace (prefixWord ++ tailWord_826836) baseStart_826836 baseEnd_826836 := by
    simpa [prefixWord, tailWord_826836, baseEnd_826836] using wordTrace_append hprefix tailTrace_826836
  have hstable : (prefixWord ++ tailWord_826836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826836).length < 2 ^ (prefixWord ++ tailWord_826836).sum := by decide
  have hdescent : baseEnd_826836 < baseStart_826836 := by decide
  rcases family_descends (prefixWord ++ tailWord_826836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826849 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_826849 : Nat := 118140960795 + 826849 * 2 ^ 59
def prefixEnd_826849 : Nat := 4983230072969 + 3 ^ 40 * 826849 * 2
def baseEnd_826849 : Nat := 424570965689540683184897

theorem tailTrace_826849 : CollatzResearch.WordTrace tailWord_826849 prefixEnd_826849 424570965689540683184897 := by
  unfold tailWord_826849
  simp only [CollatzResearch.WordTrace]
  refine ⟨30157660581474762411643601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20105107054316508274429067 30157660581474762411643601)
  ·
    refine ⟨22618245436106071808732701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30157660581474762411643601 22618245436106071808732701)
    ·
      refine ⟨8481842038539776928274763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22618245436106071808732701 8481842038539776928274763)
      ·
        refine ⟨12722763057809665392412145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8481842038539776928274763 12722763057809665392412145)
        ·
          refine ⟨9542072293357249044309109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12722763057809665392412145 9542072293357249044309109)
          ·
            refine ⟨894569277502242097903979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9542072293357249044309109 894569277502242097903979)
            ·
              refine ⟨1341853916253363146855969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894569277502242097903979 1341853916253363146855969)
              ·
                refine ⟨1006390437190022360141977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341853916253363146855969 1006390437190022360141977)
                ·
                  refine ⟨754792827892516770106483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006390437190022360141977 754792827892516770106483)
                  ·
                    refine ⟨1132189241838775155159725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754792827892516770106483 1132189241838775155159725)
                    ·
                      refine ⟨424570965689540683184897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132189241838775155159725 424570965689540683184897)
                      ·
                        rfl

theorem cell23_826849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_826849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826849 prefixEnd_826849 := by exact prefixLift 826849
  have htrace : WordTrace (prefixWord ++ tailWord_826849) baseStart_826849 baseEnd_826849 := by
    simpa [prefixWord, tailWord_826849, baseEnd_826849] using wordTrace_append hprefix tailTrace_826849
  have hstable : (prefixWord ++ tailWord_826849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826849).length < 2 ^ (prefixWord ++ tailWord_826849).sum := by decide
  have hdescent : baseEnd_826849 < baseStart_826849 := by decide
  rcases family_descends (prefixWord ++ tailWord_826849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826866 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_826866 : Nat := 118140960795 + 826866 * 2 ^ 59
def prefixEnd_826866 : Nat := 4983230072969 + 3 ^ 40 * 826866 * 2
def baseEnd_826866 : Nat := 424579694860667116672319

theorem tailTrace_826866 : CollatzResearch.WordTrace tailWord_826866 prefixEnd_826866 424579694860667116672319 := by
  unfold tailWord_826866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539570155603293578753113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20105520414942116210008301 7539570155603293578753113)
  ·
    refine ⟨5654677616702470184064835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7539570155603293578753113 5654677616702470184064835)
    ·
      refine ⟨8482016425053705276097253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654677616702470184064835 8482016425053705276097253)
      ·
        refine ⟨1590378079697569739268235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8482016425053705276097253 1590378079697569739268235)
        ·
          refine ⟨2385567119546354608902353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590378079697569739268235 2385567119546354608902353)
          ·
            refine ⟨1789175339659765956676765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385567119546354608902353 1789175339659765956676765)
            ·
              refine ⟨670940752372412233753787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1789175339659765956676765 670940752372412233753787)
              ·
                refine ⟨1006411128558618350630681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670940752372412233753787 1006411128558618350630681)
                ·
                  refine ⟨754808346418963762973011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006411128558618350630681 754808346418963762973011)
                  ·
                    refine ⟨1132212519628445644459517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754808346418963762973011 1132212519628445644459517)
                    ·
                      refine ⟨424579694860667116672319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132212519628445644459517 424579694860667116672319)
                      ·
                        rfl

theorem cell23_826866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_826866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826866 prefixEnd_826866 := by exact prefixLift 826866
  have htrace : WordTrace (prefixWord ++ tailWord_826866) baseStart_826866 baseEnd_826866 := by
    simpa [prefixWord, tailWord_826866, baseEnd_826866] using wordTrace_append hprefix tailTrace_826866
  have hstable : (prefixWord ++ tailWord_826866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826866).length < 2 ^ (prefixWord ++ tailWord_826866).sum := by decide
  have hdescent : baseEnd_826866 < baseStart_826866 := by decide
  rcases family_descends (prefixWord ++ tailWord_826866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826872 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 1, 4, 2]
def baseStart_826872 : Nat := 118140960795 + 826872 * 2 ^ 59
def prefixEnd_826872 : Nat := 4983230072969 + 3 ^ 40 * 826872 * 2
def baseEnd_826872 : Nat := 424582775744594093197291

theorem tailTrace_826872 : CollatzResearch.WordTrace tailWord_826872 prefixEnd_826872 424582775744594093197291 := by
  unfold tailWord_826872
  simp only [CollatzResearch.WordTrace]
  refine ⟨15079249730195718669865435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20105666306927624893153913 15079249730195718669865435)
  ·
    refine ⟨22618874595293578004798153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15079249730195718669865435 22618874595293578004798153)
    ·
      refine ⟨16964155946470183503598615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22618874595293578004798153 16964155946470183503598615)
      ·
        refine ⟨25446233919705275255397923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16964155946470183503598615 25446233919705275255397923)
        ·
          refine ⟨38169350879557912883096885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25446233919705275255397923 38169350879557912883096885)
          ·
            refine ⟨3578376644958554332790333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38169350879557912883096885 3578376644958554332790333)
            ·
              refine ⟨1341891241859457874796375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3578376644958554332790333 1341891241859457874796375)
              ·
                refine ⟨2012836862789186812194563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341891241859457874796375 2012836862789186812194563)
                ·
                  refine ⟨3019255294183780218291845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012836862789186812194563 3019255294183780218291845)
                  ·
                    refine ⟨566110367659458790929721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3019255294183780218291845 566110367659458790929721)
                    ·
                      refine ⟨424582775744594093197291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566110367659458790929721 424582775744594093197291)
                      ·
                        rfl

theorem cell23_826872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_826872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826872 prefixEnd_826872 := by exact prefixLift 826872
  have htrace : WordTrace (prefixWord ++ tailWord_826872) baseStart_826872 baseEnd_826872 := by
    simpa [prefixWord, tailWord_826872, baseEnd_826872] using wordTrace_append hprefix tailTrace_826872
  have hstable : (prefixWord ++ tailWord_826872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826872).length < 2 ^ (prefixWord ++ tailWord_826872).sum := by decide
  have hdescent : baseEnd_826872 < baseStart_826872 := by decide
  rcases family_descends (prefixWord ++ tailWord_826872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826912 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 7]
def baseStart_826912 : Nat := 118140960795 + 826912 * 2 ^ 59
def prefixEnd_826912 : Nat := 4983230072969 + 3 ^ 40 * 826912 * 2
def baseEnd_826912 : Nat := 47178146107863770744123

theorem tailTrace_826912 : CollatzResearch.WordTrace tailWord_826912 prefixEnd_826912 47178146107863770744123 := by
  unfold tailWord_826912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15079979190123262085593495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20106638920164349447457993 15079979190123262085593495)
  ·
    refine ⟨22619968785184893128390243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15079979190123262085593495 22619968785184893128390243)
    ·
      refine ⟨33929953177777339692585365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22619968785184893128390243 33929953177777339692585365)
      ·
        refine ⟨1590466555208312798089939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33929953177777339692585365 1590466555208312798089939)
        ·
          refine ⟨2385699832812469197134909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590466555208312798089939 2385699832812469197134909)
          ·
            refine ⟨894637437304675948925591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2385699832812469197134909 894637437304675948925591)
            ·
              refine ⟨1341956155957013923388387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894637437304675948925591 1341956155957013923388387)
              ·
                refine ⟨2012934233935520885082581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341956155957013923388387 2012934233935520885082581)
                ·
                  refine ⟨47178146107863770744123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2012934233935520885082581 47178146107863770744123)
                  ·
                    rfl

theorem cell23_826912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_826912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826912 prefixEnd_826912 := by exact prefixLift 826912
  have htrace : WordTrace (prefixWord ++ tailWord_826912) baseStart_826912 baseEnd_826912 := by
    simpa [prefixWord, tailWord_826912, baseEnd_826912] using wordTrace_append hprefix tailTrace_826912
  have hstable : (prefixWord ++ tailWord_826912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826912).length < 2 ^ (prefixWord ++ tailWord_826912).sum := by decide
  have hdescent : baseEnd_826912 < baseStart_826912 := by decide
  rcases family_descends (prefixWord ++ tailWord_826912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826962 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_826962 : Nat := 118140960795 + 826962 * 2 ^ 59
def prefixEnd_826962 : Nat := 4983230072969 + 3 ^ 40 * 826962 * 2
def baseEnd_826962 : Nat := 424628989003498741071877

theorem tailTrace_826962 : CollatzResearch.WordTrace tailWord_826962 prefixEnd_826962 424628989003498741071877 := by
  unfold tailWord_826962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540445507516345677626785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20107854686710255140338093 7540445507516345677626785)
  ·
    refine ⟨5655334130637259258220089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7540445507516345677626785 5655334130637259258220089)
    ·
      refine ⟨4241500597977944443665067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5655334130637259258220089 4241500597977944443665067)
      ·
        refine ⟨6362250896966916665497601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241500597977944443665067 6362250896966916665497601)
        ·
          refine ⟨4771688172725187499123201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6362250896966916665497601 4771688172725187499123201)
          ·
            refine ⟨3578766129543890624342401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771688172725187499123201 3578766129543890624342401)
            ·
              refine ⟨2684074597157917968256801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3578766129543890624342401 2684074597157917968256801)
              ·
                refine ⟨2013055947868438476192601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684074597157917968256801 2013055947868438476192601)
                ·
                  refine ⟨1509791960901328857144451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013055947868438476192601 1509791960901328857144451)
                  ·
                    refine ⟨2264687941351993285716677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1509791960901328857144451 2264687941351993285716677)
                    ·
                      refine ⟨424628989003498741071877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2264687941351993285716677 424628989003498741071877)
                      ·
                        rfl

theorem cell23_826962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_826962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826962 prefixEnd_826962 := by exact prefixLift 826962
  have htrace : WordTrace (prefixWord ++ tailWord_826962) baseStart_826962 baseEnd_826962 := by
    simpa [prefixWord, tailWord_826962, baseEnd_826962] using wordTrace_append hprefix tailTrace_826962
  have hstable : (prefixWord ++ tailWord_826962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826962).length < 2 ^ (prefixWord ++ tailWord_826962).sum := by decide
  have hdescent : baseEnd_826962 < baseStart_826962 := by decide
  rcases family_descends (prefixWord ++ tailWord_826962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826965 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_826965 : Nat := 118140960795 + 826965 * 2 ^ 59
def prefixEnd_826965 : Nat := 4983230072969 + 3 ^ 40 * 826965 * 2
def baseEnd_826965 : Nat := 424630529445462229334363

theorem tailTrace_826965 : CollatzResearch.WordTrace tailWord_826965 prefixEnd_826965 424630529445462229334363 := by
  unfold tailWord_826965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30161891449054514222866349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20107927632703009481910899 30161891449054514222866349)
  ·
    refine ⟨11310709293395442833574881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30161891449054514222866349 11310709293395442833574881)
    ·
      refine ⟨8483031970046582125181161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11310709293395442833574881 8483031970046582125181161)
      ·
        refine ⟨6362273977534936593885871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8483031970046582125181161 6362273977534936593885871)
        ·
          refine ⟨9543410966302404890828807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362273977534936593885871 9543410966302404890828807)
          ·
            refine ⟨14315116449453607336243211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9543410966302404890828807 14315116449453607336243211)
            ·
              refine ⟨21472674674180411004364817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14315116449453607336243211 21472674674180411004364817)
              ·
                refine ⟨16104506005635308253273613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21472674674180411004364817 16104506005635308253273613)
                ·
                  refine ⟨6039189752113240594977605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16104506005635308253273613 6039189752113240594977605)
                  ·
                    refine ⟨1132348078521232611558301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039189752113240594977605 1132348078521232611558301)
                    ·
                      refine ⟨424630529445462229334363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132348078521232611558301 424630529445462229334363)
                      ·
                        rfl

theorem cell23_826965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_826965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826965 prefixEnd_826965 := by exact prefixLift 826965
  have htrace : WordTrace (prefixWord ++ tailWord_826965) baseStart_826965 baseEnd_826965 := by
    simpa [prefixWord, tailWord_826965, baseEnd_826965] using wordTrace_append hprefix tailTrace_826965
  have hstable : (prefixWord ++ tailWord_826965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826965).length < 2 ^ (prefixWord ++ tailWord_826965).sum := by decide
  have hdescent : baseEnd_826965 < baseStart_826965 := by decide
  rcases family_descends (prefixWord ++ tailWord_826965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826985 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 6]
def baseStart_826985 : Nat := 118140960795 + 826985 * 2 ^ 59
def prefixEnd_826985 : Nat := 4983230072969 + 3 ^ 40 * 826985 * 2
def baseEnd_826985 : Nat := 47182311006505794564919

theorem tailTrace_826985 : CollatzResearch.WordTrace tailWord_826985 prefixEnd_826985 47182311006505794564919 := by
  unfold tailWord_826985
  simp only [CollatzResearch.WordTrace]
  refine ⟨30162620908982057638594409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20108413939321371759062939 30162620908982057638594409)
  ·
    refine ⟨22621965681736543228945807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30162620908982057638594409 22621965681736543228945807)
    ·
      refine ⟨33932948522604814843418711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22621965681736543228945807 33932948522604814843418711)
      ·
        refine ⟨50899422783907222265128067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33932948522604814843418711 50899422783907222265128067)
        ·
          refine ⟨76349134175860833397692101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50899422783907222265128067 76349134175860833397692101)
          ·
            refine ⟨14315462657973906262067269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76349134175860833397692101 14315462657973906262067269)
            ·
              refine ⟨2684149248370107424137613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14315462657973906262067269 2684149248370107424137613)
              ·
                refine ⟨1006555968138790284051605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2684149248370107424137613 1006555968138790284051605)
                ·
                  refine ⟨47182311006505794564919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1006555968138790284051605 47182311006505794564919)
                  ·
                    rfl

theorem cell23_826985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 6].length) (baseStart_826985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826985 prefixEnd_826985 := by exact prefixLift 826985
  have htrace : WordTrace (prefixWord ++ tailWord_826985) baseStart_826985 baseEnd_826985 := by
    simpa [prefixWord, tailWord_826985, baseEnd_826985] using wordTrace_append hprefix tailTrace_826985
  have hstable : (prefixWord ++ tailWord_826985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826985).length < 2 ^ (prefixWord ++ tailWord_826985).sum := by decide
  have hdescent : baseEnd_826985 < baseStart_826985 := by decide
  rcases family_descends (prefixWord ++ tailWord_826985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826989 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_826989 : Nat := 118140960795 + 826989 * 2 ^ 59
def prefixEnd_826989 : Nat := 4983230072969 + 3 ^ 40 * 826989 * 2
def baseEnd_826989 : Nat := 141547617660390045144751

theorem tailTrace_826989 : CollatzResearch.WordTrace tailWord_826989 prefixEnd_826989 141547617660390045144751 := by
  unfold tailWord_826989
  simp only [CollatzResearch.WordTrace]
  refine ⟨30162766800967566321740021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20108511200645044214493347 30162766800967566321740021)
  ·
    refine ⟨2827759387590709342663127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30162766800967566321740021 2827759387590709342663127)
    ·
      refine ⟨4241639081386064013994691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827759387590709342663127 4241639081386064013994691)
      ·
        refine ⟨6362458622079096020992037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241639081386064013994691 6362458622079096020992037)
        ·
          refine ⟨1192960991639830503936007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6362458622079096020992037 1192960991639830503936007)
          ·
            refine ⟨1789441487459745755904011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192960991639830503936007 1789441487459745755904011)
            ·
              refine ⟨2684162231189618633856017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789441487459745755904011 2684162231189618633856017)
              ·
                refine ⟨2013121673392213975392013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684162231189618633856017 2013121673392213975392013)
                ·
                  refine ⟨754920627522080240772005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2013121673392213975392013 754920627522080240772005)
                  ·
                    refine ⟨141547617660390045144751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 754920627522080240772005 141547617660390045144751)
                    ·
                      rfl

theorem cell23_826989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_826989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_826989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_826989 prefixEnd_826989 := by exact prefixLift 826989
  have htrace : WordTrace (prefixWord ++ tailWord_826989) baseStart_826989 baseEnd_826989 := by
    simpa [prefixWord, tailWord_826989, baseEnd_826989] using wordTrace_append hprefix tailTrace_826989
  have hstable : (prefixWord ++ tailWord_826989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826989).length < 2 ^ (prefixWord ++ tailWord_826989).sum := by decide
  have hdescent : baseEnd_826989 < baseStart_826989 := by decide
  rcases family_descends (prefixWord ++ tailWord_826989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827055 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_827055 : Nat := 118140960795 + 827055 * 2 ^ 59
def prefixEnd_827055 : Nat := 4983230072969 + 3 ^ 40 * 827055 * 2
def baseEnd_827055 : Nat := 424676742704366877208949

theorem tailTrace_827055 : CollatzResearch.WordTrace tailWord_827055 prefixEnd_827055 424676742704366877208949 := by
  unfold tailWord_827055
  simp only [CollatzResearch.WordTrace]
  refine ⟨30165174018728459593642619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20110116012485639729095079 30165174018728459593642619)
  ·
    refine ⟨45247761028092689390463929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30165174018728459593642619 45247761028092689390463929)
    ·
      refine ⟨33935820771069517042847947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45247761028092689390463929 33935820771069517042847947)
      ·
        refine ⟨50903731156604275564271921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33935820771069517042847947 50903731156604275564271921)
        ·
          refine ⟨38177798367453206673203941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50903731156604275564271921 38177798367453206673203941)
          ·
            refine ⟨7158337193897476251225739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38177798367453206673203941 7158337193897476251225739)
            ·
              refine ⟨10737505790846214376838609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158337193897476251225739 10737505790846214376838609)
              ·
                refine ⟨8053129343134660782628957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10737505790846214376838609 8053129343134660782628957)
                ·
                  refine ⟨3019923503675497793485859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8053129343134660782628957 3019923503675497793485859)
                  ·
                    refine ⟨4529885255513246690228789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019923503675497793485859 4529885255513246690228789)
                    ·
                      refine ⟨424676742704366877208949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4529885255513246690228789 424676742704366877208949)
                      ·
                        rfl

theorem cell23_827055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_827055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827055 prefixEnd_827055 := by exact prefixLift 827055
  have htrace : WordTrace (prefixWord ++ tailWord_827055) baseStart_827055 baseEnd_827055 := by
    simpa [prefixWord, tailWord_827055, baseEnd_827055] using wordTrace_append hprefix tailTrace_827055
  have hstable : (prefixWord ++ tailWord_827055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827055).length < 2 ^ (prefixWord ++ tailWord_827055).sum := by decide
  have hdescent : baseEnd_827055 < baseStart_827055 := by decide
  rcases family_descends (prefixWord ++ tailWord_827055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827063 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 1, 1, 3]
def baseStart_827063 : Nat := 118140960795 + 827063 * 2 ^ 59
def prefixEnd_827063 : Nat := 4983230072969 + 3 ^ 40 * 827063 * 2
def baseEnd_827063 : Nat := 424680850549602845908913

theorem tailTrace_827063 : CollatzResearch.WordTrace tailWord_827063 prefixEnd_827063 424680850549602845908913 := by
  unfold tailWord_827063
  simp only [CollatzResearch.WordTrace]
  refine ⟨30165465802699476959933843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20110310535132984639955895 30165465802699476959933843)
  ·
    refine ⟨45248198704049215439900765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30165465802699476959933843 45248198704049215439900765)
    ·
      refine ⟨16968074514018455789962787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45248198704049215439900765 16968074514018455789962787)
      ·
        refine ⟨25452111771027683684944181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16968074514018455789962787 25452111771027683684944181)
        ·
          refine ⟨2386135478533845345463517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25452111771027683684944181 2386135478533845345463517)
          ·
            refine ⟨894800804450192004548819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2386135478533845345463517 894800804450192004548819)
            ·
              refine ⟨1342201206675288006823229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894800804450192004548819 1342201206675288006823229)
              ·
                refine ⟨503325452503233002558711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1342201206675288006823229 503325452503233002558711)
                ·
                  refine ⟨754988178754849503838067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503325452503233002558711 754988178754849503838067)
                  ·
                    refine ⟨1132482268132274255757101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 754988178754849503838067 1132482268132274255757101)
                    ·
                      refine ⟨424680850549602845908913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132482268132274255757101 424680850549602845908913)
                      ·
                        rfl

theorem cell23_827063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_827063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827063 prefixEnd_827063 := by exact prefixLift 827063
  have htrace : WordTrace (prefixWord ++ tailWord_827063) baseStart_827063 baseEnd_827063 := by
    simpa [prefixWord, tailWord_827063, baseEnd_827063] using wordTrace_append hprefix tailTrace_827063
  have hstable : (prefixWord ++ tailWord_827063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827063).length < 2 ^ (prefixWord ++ tailWord_827063).sum := by decide
  have hdescent : baseEnd_827063 < baseStart_827063 := by decide
  rcases family_descends (prefixWord ++ tailWord_827063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827072 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_827072 : Nat := 118140960795 + 827072 * 2 ^ 59
def prefixEnd_827072 : Nat := 4983230072969 + 3 ^ 40 * 827072 * 2
def baseEnd_827072 : Nat := 424685471875493310696371

theorem tailTrace_827072 : CollatzResearch.WordTrace tailWord_827072 prefixEnd_827072 424685471875493310696371 := by
  unfold tailWord_827072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15082897029833435748505735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20110529373111247664674313 15082897029833435748505735)
  ·
    refine ⟨22624345544750153622758603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15082897029833435748505735 22624345544750153622758603)
    ·
      refine ⟨33936518317125230434137905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22624345544750153622758603 33936518317125230434137905)
      ·
        refine ⟨25452388737843922825603429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33936518317125230434137905 25452388737843922825603429)
        ·
          refine ⟨4772322888345735529800643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25452388737843922825603429 4772322888345735529800643)
          ·
            refine ⟨7158484332518603294700965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772322888345735529800643 7158484332518603294700965)
            ·
              refine ⟨1342215812347238117756431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7158484332518603294700965 1342215812347238117756431)
              ·
                refine ⟨2013323718520857176634647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342215812347238117756431 2013323718520857176634647)
                ·
                  refine ⟨3019985577781285764951971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013323718520857176634647 3019985577781285764951971)
                  ·
                    refine ⟨4529978366671928647427957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019985577781285764951971 4529978366671928647427957)
                    ·
                      refine ⟨424685471875493310696371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4529978366671928647427957 424685471875493310696371)
                      ·
                        rfl

theorem cell23_827072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_827072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827072 prefixEnd_827072 := by exact prefixLift 827072
  have htrace : WordTrace (prefixWord ++ tailWord_827072) baseStart_827072 baseEnd_827072 := by
    simpa [prefixWord, tailWord_827072, baseEnd_827072] using wordTrace_append hprefix tailTrace_827072
  have hstable : (prefixWord ++ tailWord_827072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827072).length < 2 ^ (prefixWord ++ tailWord_827072).sum := by decide
  have hdescent : baseEnd_827072 < baseStart_827072 := by decide
  rcases family_descends (prefixWord ++ tailWord_827072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827092 : List Nat := [2, 4, 1, 3, 1, 1, 1, 10]
def baseStart_827092 : Nat := 118140960795 + 827092 * 2 ^ 59
def prefixEnd_827092 : Nat := 4983230072969 + 3 ^ 40 * 827092 * 2
def baseEnd_827092 : Nat := 15729471906984564164677

theorem tailTrace_827092 : CollatzResearch.WordTrace tailWord_827092 prefixEnd_827092 15729471906984564164677 := by
  unfold tailWord_827092
  simp only [CollatzResearch.WordTrace]
  refine ⟨15083261759797207456369765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20111015679729609941826353 15083261759797207456369765)
  ·
    refine ⟨2828111579961976398069331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15083261759797207456369765 2828111579961976398069331)
    ·
      refine ⟨4242167369942964597103997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828111579961976398069331 4242167369942964597103997)
      ·
        refine ⟨1590812763728611723913999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4242167369942964597103997 1590812763728611723913999)
        ·
          refine ⟨2386219145592917585870999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590812763728611723913999 2386219145592917585870999)
          ·
            refine ⟨3579328718389376378806499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386219145592917585870999 3579328718389376378806499)
            ·
              refine ⟨5368993077584064568209749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579328718389376378806499 5368993077584064568209749)
              ·
                refine ⟨15729471906984564164677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5368993077584064568209749 15729471906984564164677)
                ·
                  rfl

theorem cell23_827092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 10].length) (baseStart_827092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827092 prefixEnd_827092 := by exact prefixLift 827092
  have htrace : WordTrace (prefixWord ++ tailWord_827092) baseStart_827092 baseEnd_827092 := by
    simpa [prefixWord, tailWord_827092, baseEnd_827092] using wordTrace_append hprefix tailTrace_827092
  have hstable : (prefixWord ++ tailWord_827092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827092).length < 2 ^ (prefixWord ++ tailWord_827092).sum := by decide
  have hdescent : baseEnd_827092 < baseStart_827092 := by decide
  rcases family_descends (prefixWord ++ tailWord_827092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827095 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_827095 : Nat := 118140960795 + 827095 * 2 ^ 59
def prefixEnd_827095 : Nat := 4983230072969 + 3 ^ 40 * 827095 * 2
def baseEnd_827095 : Nat := 424697281930546720708765

theorem tailTrace_827095 : CollatzResearch.WordTrace tailWord_827095 prefixEnd_827095 424697281930546720708765 := by
  unfold tailWord_827095
  simp only [CollatzResearch.WordTrace]
  refine ⟨30166632938583546425098739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20111088625722364283399159 30166632938583546425098739)
  ·
    refine ⟨45249949407875319637648109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30166632938583546425098739 45249949407875319637648109)
    ·
      refine ⟨16968731027953244864118041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45249949407875319637648109 16968731027953244864118041)
      ·
        refine ⟨12726548270964933648088531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16968731027953244864118041 12726548270964933648088531)
        ·
          refine ⟨19089822406447400472132797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12726548270964933648088531 19089822406447400472132797)
          ·
            refine ⟨7158683402417775177049799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19089822406447400472132797 7158683402417775177049799)
            ·
              refine ⟨10738025103626662765574699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158683402417775177049799 10738025103626662765574699)
              ·
                refine ⟨16107037655439994148362049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738025103626662765574699 16107037655439994148362049)
                ·
                  refine ⟨12080278241579995611271537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16107037655439994148362049 12080278241579995611271537)
                  ·
                    refine ⟨9060208681184996708453653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12080278241579995611271537 9060208681184996708453653)
                    ·
                      refine ⟨424697281930546720708765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9060208681184996708453653 424697281930546720708765)
                      ·
                        rfl

theorem cell23_827095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_827095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827095 prefixEnd_827095 := by exact prefixLift 827095
  have htrace : WordTrace (prefixWord ++ tailWord_827095) baseStart_827095 baseEnd_827095 := by
    simpa [prefixWord, tailWord_827095, baseEnd_827095] using wordTrace_append hprefix tailTrace_827095
  have hstable : (prefixWord ++ tailWord_827095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827095).length < 2 ^ (prefixWord ++ tailWord_827095).sum := by decide
  have hdescent : baseEnd_827095 < baseStart_827095 := by decide
  rcases family_descends (prefixWord ++ tailWord_827095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827115 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_827115 : Nat := 118140960795 + 827115 * 2 ^ 59
def prefixEnd_827115 : Nat := 4983230072969 + 3 ^ 40 * 827115 * 2
def baseEnd_827115 : Nat := 424707551543636642458673

theorem tailTrace_827115 : CollatzResearch.WordTrace tailWord_827115 prefixEnd_827115 424707551543636642458673 := by
  unfold tailWord_827115
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167362398511089840826799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20111574932340726560551199 30167362398511089840826799)
  ·
    refine ⟨45251043597766634761240199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30167362398511089840826799 45251043597766634761240199)
    ·
      refine ⟨67876565396649952141860299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45251043597766634761240199 67876565396649952141860299)
      ·
        refine ⟨101814848094974928212790449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67876565396649952141860299 101814848094974928212790449)
        ·
          refine ⟨76361136071231196159592837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101814848094974928212790449 76361136071231196159592837)
          ·
            refine ⟨14317713013355849279923657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76361136071231196159592837 14317713013355849279923657)
            ·
              refine ⟨10738284760016886959942743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14317713013355849279923657 10738284760016886959942743)
              ·
                refine ⟨16107427140025330439914115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738284760016886959942743 16107427140025330439914115)
                ·
                  refine ⟨24161140710037995659871173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16107427140025330439914115 24161140710037995659871173)
                  ·
                    refine ⟨4530213883132124186225845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24161140710037995659871173 4530213883132124186225845)
                    ·
                      refine ⟨424707551543636642458673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4530213883132124186225845 424707551543636642458673)
                      ·
                        rfl

theorem cell23_827115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_827115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827115 prefixEnd_827115 := by exact prefixLift 827115
  have htrace : WordTrace (prefixWord ++ tailWord_827115) baseStart_827115 baseEnd_827115 := by
    simpa [prefixWord, tailWord_827115, baseEnd_827115] using wordTrace_append hprefix tailTrace_827115
  have hstable : (prefixWord ++ tailWord_827115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827115).length < 2 ^ (prefixWord ++ tailWord_827115).sum := by decide
  have hdescent : baseEnd_827115 < baseStart_827115 := by decide
  rcases family_descends (prefixWord ++ tailWord_827115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827176 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_827176 : Nat := 118140960795 + 827176 * 2 ^ 59
def prefixEnd_827176 : Nat := 4983230072969 + 3 ^ 40 * 827176 * 2
def baseEnd_827176 : Nat := 424738873863560903795893

theorem tailTrace_827176 : CollatzResearch.WordTrace tailWord_827176 prefixEnd_827176 424738873863560903795893 := by
  unfold tailWord_827176
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084793625645048629398691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20113058167526731505864921 15084793625645048629398691)
  ·
    refine ⟨22627190438467572944098037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15084793625645048629398691 22627190438467572944098037)
    ·
      refine ⟨2121299103606334963509191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22627190438467572944098037 2121299103606334963509191)
      ·
        refine ⟨3181948655409502445263787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121299103606334963509191 3181948655409502445263787)
        ·
          refine ⟨4772922983114253667895681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181948655409502445263787 4772922983114253667895681)
          ·
            refine ⟨3579692237335690250921761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4772922983114253667895681 3579692237335690250921761)
            ·
              refine ⟨2684769178001767688191321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579692237335690250921761 2684769178001767688191321)
              ·
                refine ⟨2013576883501325766143491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684769178001767688191321 2013576883501325766143491)
                ·
                  refine ⟨3020365325251988649215237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013576883501325766143491 3020365325251988649215237)
                  ·
                    refine ⟨566318498484747871727857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3020365325251988649215237 566318498484747871727857)
                    ·
                      refine ⟨424738873863560903795893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566318498484747871727857 424738873863560903795893)
                      ·
                        rfl

theorem cell23_827176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_827176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827176 prefixEnd_827176 := by exact prefixLift 827176
  have htrace : WordTrace (prefixWord ++ tailWord_827176) baseStart_827176 baseEnd_827176 := by
    simpa [prefixWord, tailWord_827176, baseEnd_827176] using wordTrace_append hprefix tailTrace_827176
  have hstable : (prefixWord ++ tailWord_827176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827176).length < 2 ^ (prefixWord ++ tailWord_827176).sum := by decide
  have hdescent : baseEnd_827176 < baseStart_827176 := by decide
  rcases family_descends (prefixWord ++ tailWord_827176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827199 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 7]
def baseStart_827199 : Nat := 118140960795 + 827199 * 2 ^ 59
def prefixEnd_827199 : Nat := 4983230072969 + 3 ^ 40 * 827199 * 2
def baseEnd_827199 : Nat := 47194520435401590423143

theorem tailTrace_827199 : CollatzResearch.WordTrace tailWord_827199 prefixEnd_827199 47194520435401590423143 := by
  unfold tailWord_827199
  simp only [CollatzResearch.WordTrace]
  refine ⟨30170426130206772186884651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20113617420137848124589767 30170426130206772186884651)
  ·
    refine ⟨45255639195310158280326977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30170426130206772186884651 45255639195310158280326977)
    ·
      refine ⟨33941729396482618710245233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45255639195310158280326977 33941729396482618710245233)
      ·
        refine ⟨25456297047361964032683925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33941729396482618710245233 25456297047361964032683925)
        ·
          refine ⟨1193263924095092064032059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25456297047361964032683925 1193263924095092064032059)
          ·
            refine ⟨1789895886142638096048089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193263924095092064032059 1789895886142638096048089)
            ·
              refine ⟨1342421914606978572036067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789895886142638096048089 1342421914606978572036067)
              ·
                refine ⟨2013632871910467858054101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342421914606978572036067 2013632871910467858054101)
                ·
                  refine ⟨47194520435401590423143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2013632871910467858054101 47194520435401590423143)
                  ·
                    rfl

theorem cell23_827199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 7].length) (baseStart_827199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827199 prefixEnd_827199 := by exact prefixLift 827199
  have htrace : WordTrace (prefixWord ++ tailWord_827199) baseStart_827199 baseEnd_827199 := by
    simpa [prefixWord, tailWord_827199, baseEnd_827199] using wordTrace_append hprefix tailTrace_827199
  have hstable : (prefixWord ++ tailWord_827199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827199).length < 2 ^ (prefixWord ++ tailWord_827199).sum := by decide
  have hdescent : baseEnd_827199 < baseStart_827199 := by decide
  rcases family_descends (prefixWord ++ tailWord_827199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827246 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_827246 : Nat := 118140960795 + 827246 * 2 ^ 59
def prefixEnd_827246 : Nat := 4983230072969 + 3 ^ 40 * 827246 * 2
def baseEnd_827246 : Nat := 141591605836458543306857

theorem tailTrace_827246 : CollatzResearch.WordTrace tailWord_827246 prefixEnd_827246 141591605836458543306857 := by
  unfold tailWord_827246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771517545129562401730699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20114760240690999475897061 3771517545129562401730699)
  ·
    refine ⟨5657276317694343602596049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3771517545129562401730699 5657276317694343602596049)
    ·
      refine ⟨4242957238270757701947037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5657276317694343602596049 4242957238270757701947037)
      ·
        refine ⟨1591108964351534138230139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4242957238270757701947037 1591108964351534138230139)
        ·
          refine ⟨2386663446527301207345209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591108964351534138230139 2386663446527301207345209)
          ·
            refine ⟨1789997584895475905508907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2386663446527301207345209 1789997584895475905508907)
            ·
              refine ⟨2684996377343213858263361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789997584895475905508907 2684996377343213858263361)
              ·
                refine ⟨2013747283007410393697521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684996377343213858263361 2013747283007410393697521)
                ·
                  refine ⟨1510310462255557795273141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013747283007410393697521 1510310462255557795273141)
                  ·
                    refine ⟨141591605836458543306857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1510310462255557795273141 141591605836458543306857)
                    ·
                      rfl

theorem cell23_827246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_827246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827246 prefixEnd_827246 := by exact prefixLift 827246
  have htrace : WordTrace (prefixWord ++ tailWord_827246) baseStart_827246 baseEnd_827246 := by
    simpa [prefixWord, tailWord_827246, baseEnd_827246] using wordTrace_append hprefix tailTrace_827246
  have hstable : (prefixWord ++ tailWord_827246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827246).length < 2 ^ (prefixWord ++ tailWord_827246).sum := by decide
  have hdescent : baseEnd_827246 < baseStart_827246 := by decide
  rcases family_descends (prefixWord ++ tailWord_827246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827249 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_827249 : Nat := 118140960795 + 827249 * 2 ^ 59
def prefixEnd_827249 : Nat := 4983230072969 + 3 ^ 40 * 827249 * 2
def baseEnd_827249 : Nat := 424776357951339118183057

theorem tailTrace_827249 : CollatzResearch.WordTrace tailWord_827249 prefixEnd_827249 424776357951339118183057 := by
  unfold tailWord_827249
  simp only [CollatzResearch.WordTrace]
  refine ⟨30172249780025630726204801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20114833186683753817469867 30172249780025630726204801)
  ·
    refine ⟨22629187335019223044653601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30172249780025630726204801 22629187335019223044653601)
    ·
      refine ⟨16971890501264417283490201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22629187335019223044653601 16971890501264417283490201)
      ·
        refine ⟨12728917875948312962617651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16971890501264417283490201 12728917875948312962617651)
        ·
          refine ⟨19093376813922469443926477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12728917875948312962617651 19093376813922469443926477)
          ·
            refine ⟨7160016305220926041472429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19093376813922469443926477 7160016305220926041472429)
            ·
              refine ⟨2685006114457847265552161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7160016305220926041472429 2685006114457847265552161)
              ·
                refine ⟨2013754585843385449164121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685006114457847265552161 2013754585843385449164121)
                ·
                  refine ⟨1510315939382539086873091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013754585843385449164121 1510315939382539086873091)
                  ·
                    refine ⟨2265473909073808630309637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510315939382539086873091 2265473909073808630309637)
                    ·
                      refine ⟨424776357951339118183057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2265473909073808630309637 424776357951339118183057)
                      ·
                        rfl

theorem cell23_827249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_827249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827249 prefixEnd_827249 := by exact prefixLift 827249
  have htrace : WordTrace (prefixWord ++ tailWord_827249) baseStart_827249 baseEnd_827249 := by
    simpa [prefixWord, tailWord_827249, baseEnd_827249] using wordTrace_append hprefix tailTrace_827249
  have hstable : (prefixWord ++ tailWord_827249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827249).length < 2 ^ (prefixWord ++ tailWord_827249).sum := by decide
  have hdescent : baseEnd_827249 < baseStart_827249 := by decide
  rcases family_descends (prefixWord ++ tailWord_827249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827269 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_827269 : Nat := 118140960795 + 827269 * 2 ^ 59
def prefixEnd_827269 : Nat := 4983230072969 + 3 ^ 40 * 827269 * 2
def baseEnd_827269 : Nat := 424786627564429039932965

theorem tailTrace_827269 : CollatzResearch.WordTrace tailWord_827269 prefixEnd_827269 424786627564429039932965 := by
  unfold tailWord_827269
  simp only [CollatzResearch.WordTrace]
  refine ⟨30172979239953174141932861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20115319493302116094621907 30172979239953174141932861)
  ·
    refine ⟨11314867214982440303224823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30172979239953174141932861 11314867214982440303224823)
    ·
      refine ⟨16972300822473660454837235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11314867214982440303224823 16972300822473660454837235)
      ·
        refine ⟨25458451233710490682255853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16972300822473660454837235 25458451233710490682255853)
        ·
          refine ⟨9546919212641434005845945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25458451233710490682255853 9546919212641434005845945)
          ·
            refine ⟨7160189409481075504384459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9546919212641434005845945 7160189409481075504384459)
            ·
              refine ⟨10740284114221613256576689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160189409481075504384459 10740284114221613256576689)
              ·
                refine ⟨8055213085666209942432517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10740284114221613256576689 8055213085666209942432517)
                ·
                  refine ⟨1510352453562414364206097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8055213085666209942432517 1510352453562414364206097)
                  ·
                    refine ⟨1132764340171810773154573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510352453562414364206097 1132764340171810773154573)
                    ·
                      refine ⟨424786627564429039932965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132764340171810773154573 424786627564429039932965)
                      ·
                        rfl

theorem cell23_827269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_827269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827269 prefixEnd_827269 := by exact prefixLift 827269
  have htrace : WordTrace (prefixWord ++ tailWord_827269) baseStart_827269 baseEnd_827269 := by
    simpa [prefixWord, tailWord_827269, baseEnd_827269] using wordTrace_append hprefix tailTrace_827269
  have hstable : (prefixWord ++ tailWord_827269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827269).length < 2 ^ (prefixWord ++ tailWord_827269).sum := by decide
  have hdescent : baseEnd_827269 < baseStart_827269 := by decide
  rcases family_descends (prefixWord ++ tailWord_827269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827312 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_827312 : Nat := 118140960795 + 827312 * 2 ^ 59
def prefixEnd_827312 : Nat := 4983230072969 + 3 ^ 40 * 827312 * 2
def baseEnd_827312 : Nat := 424808707232572371695267

theorem tailTrace_827312 : CollatzResearch.WordTrace tailWord_827312 prefixEnd_827312 424808707232572371695267 := by
  unfold tailWord_827312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087273789398696242874095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20116365052531594990498793 15087273789398696242874095)
  ·
    refine ⟨22630910684098044364311143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15087273789398696242874095 22630910684098044364311143)
    ·
      refine ⟨33946366026147066546466715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22630910684098044364311143 33946366026147066546466715)
      ·
        refine ⟨50919549039220599819700073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33946366026147066546466715 50919549039220599819700073)
        ·
          refine ⟨38189661779415449864775055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50919549039220599819700073 38189661779415449864775055)
          ·
            refine ⟨57284492669123174797162583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38189661779415449864775055 57284492669123174797162583)
            ·
              refine ⟨85926739003684762195743875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57284492669123174797162583 85926739003684762195743875)
              ·
                refine ⟨128890108505527143293615813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85926739003684762195743875 128890108505527143293615813)
                ·
                  refine ⟨24166895344786339367552965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128890108505527143293615813 24166895344786339367552965)
                  ·
                    refine ⟨4531292877147438631416181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24166895344786339367552965 4531292877147438631416181)
                    ·
                      refine ⟨424808707232572371695267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4531292877147438631416181 424808707232572371695267)
                      ·
                        rfl

theorem cell23_827312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_827312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827312 prefixEnd_827312 := by exact prefixLift 827312
  have htrace : WordTrace (prefixWord ++ tailWord_827312) baseStart_827312 baseEnd_827312 := by
    simpa [prefixWord, tailWord_827312, baseEnd_827312] using wordTrace_append hprefix tailTrace_827312
  have hstable : (prefixWord ++ tailWord_827312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827312).length < 2 ^ (prefixWord ++ tailWord_827312).sum := by decide
  have hdescent : baseEnd_827312 < baseStart_827312 := by decide
  rcases family_descends (prefixWord ++ tailWord_827312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827339 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 4]
def baseStart_827339 : Nat := 118140960795 + 827339 * 2 ^ 59
def prefixEnd_827339 : Nat := 4983230072969 + 3 ^ 40 * 827339 * 2
def baseEnd_827339 : Nat := 424822571210243766057643

theorem tailTrace_827339 : CollatzResearch.WordTrace tailWord_827339 prefixEnd_827339 424822571210243766057643 := by
  unfold tailWord_827339
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175532349699576096981071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20117021566466384064654047 30175532349699576096981071)
  ·
    refine ⟨45263298524549364145471607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30175532349699576096981071 45263298524549364145471607)
    ·
      refine ⟨67894947786824046218207411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45263298524549364145471607 67894947786824046218207411)
      ·
        refine ⟨101842421680236069327311117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67894947786824046218207411 101842421680236069327311117)
        ·
          refine ⟨38190908130088525997741669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101842421680236069327311117 38190908130088525997741669)
          ·
            refine ⟨7160795274391598624576563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38190908130088525997741669 7160795274391598624576563)
            ·
              refine ⟨10741192911587397936864845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160795274391598624576563 10741192911587397936864845)
              ·
                refine ⟨4027947341845274226324317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10741192911587397936864845 4027947341845274226324317)
                ·
                  refine ⟨1510480253191977834871619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4027947341845274226324317 1510480253191977834871619)
                  ·
                    refine ⟨2265720379787966752307429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510480253191977834871619 2265720379787966752307429)
                    ·
                      refine ⟨424822571210243766057643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2265720379787966752307429 424822571210243766057643)
                      ·
                        rfl

theorem cell23_827339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 4].length) (baseStart_827339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827339 prefixEnd_827339 := by exact prefixLift 827339
  have htrace : WordTrace (prefixWord ++ tailWord_827339) baseStart_827339 baseEnd_827339 := by
    simpa [prefixWord, tailWord_827339, baseEnd_827339] using wordTrace_append hprefix tailTrace_827339
  have hstable : (prefixWord ++ tailWord_827339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827339).length < 2 ^ (prefixWord ++ tailWord_827339).sum := by decide
  have hdescent : baseEnd_827339 < baseStart_827339 := by decide
  rcases family_descends (prefixWord ++ tailWord_827339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827390 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_827390 : Nat := 118140960795 + 827390 * 2 ^ 59
def prefixEnd_827390 : Nat := 4983230072969 + 3 ^ 40 * 827390 * 2
def baseEnd_827390 : Nat := 424848758723623066519909

theorem tailTrace_827390 : CollatzResearch.WordTrace tailWord_827390 prefixEnd_827390 424848758723623066519909 := by
  unfold tailWord_827390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3772174059064351475885953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20118261648343207871391749 3772174059064351475885953)
  ·
    refine ⟨2829130544298263606914465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3772174059064351475885953 2829130544298263606914465)
    ·
      refine ⟨2121847908223697705185849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2829130544298263606914465 2121847908223697705185849)
      ·
        refine ⟨1591385931167773278889387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121847908223697705185849 1591385931167773278889387)
        ·
          refine ⟨2387078896751659918334081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591385931167773278889387 2387078896751659918334081)
          ·
            refine ⟨1790309172563744938750561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2387078896751659918334081 1790309172563744938750561)
            ·
              refine ⟨1342731879422808704062921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790309172563744938750561 1342731879422808704062921)
              ·
                refine ⟨1007048909567106528047191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342731879422808704062921 1007048909567106528047191)
                ·
                  refine ⟨1510573364350659792070787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007048909567106528047191 1510573364350659792070787)
                  ·
                    refine ⟨2265860046525989688106181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510573364350659792070787 2265860046525989688106181)
                    ·
                      refine ⟨424848758723623066519909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2265860046525989688106181 424848758723623066519909)
                      ·
                        rfl

theorem cell23_827390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_827390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827390 prefixEnd_827390 := by exact prefixLift 827390
  have htrace : WordTrace (prefixWord ++ tailWord_827390) baseStart_827390 baseEnd_827390 := by
    simpa [prefixWord, tailWord_827390, baseEnd_827390] using wordTrace_append hprefix tailTrace_827390
  have hstable : (prefixWord ++ tailWord_827390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827390).length < 2 ^ (prefixWord ++ tailWord_827390).sum := by decide
  have hdescent : baseEnd_827390 < baseStart_827390 := by decide
  rcases family_descends (prefixWord ++ tailWord_827390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827393 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_827393 : Nat := 118140960795 + 827393 * 2 ^ 59
def prefixEnd_827393 : Nat := 4983230072969 + 3 ^ 40 * 827393 * 2
def baseEnd_827393 : Nat := 424850299165586554782395

theorem tailTrace_827393 : CollatzResearch.WordTrace tailWord_827393 prefixEnd_827393 424850299165586554782395 := by
  unfold tailWord_827393
  simp only [CollatzResearch.WordTrace]
  refine ⟨30177501891503943319446833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20118334594335962212964555 30177501891503943319446833)
  ·
    refine ⟨22633126418627957489585125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30177501891503943319446833 22633126418627957489585125)
    ·
      refine ⟨4243711203492742029297211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22633126418627957489585125 4243711203492742029297211)
      ·
        refine ⟨6365566805239113043945817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243711203492742029297211 6365566805239113043945817)
        ·
          refine ⟨4774175103929334782959363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6365566805239113043945817 4774175103929334782959363)
          ·
            refine ⟨7161262655894002174439045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774175103929334782959363 7161262655894002174439045)
            ·
              refine ⟨1342736747980125407707321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7161262655894002174439045 1342736747980125407707321)
              ·
                refine ⟨1007052560985094055780491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342736747980125407707321 1007052560985094055780491)
                ·
                  refine ⟨1510578841477641083670737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007052560985094055780491 1510578841477641083670737)
                  ·
                    refine ⟨1132934131108230812753053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510578841477641083670737 1132934131108230812753053)
                    ·
                      refine ⟨424850299165586554782395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132934131108230812753053 424850299165586554782395)
                      ·
                        rfl

theorem cell23_827393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_827393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827393 prefixEnd_827393 := by exact prefixLift 827393
  have htrace : WordTrace (prefixWord ++ tailWord_827393) baseStart_827393 baseEnd_827393 := by
    simpa [prefixWord, tailWord_827393, baseEnd_827393] using wordTrace_append hprefix tailTrace_827393
  have hstable : (prefixWord ++ tailWord_827393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827393).length < 2 ^ (prefixWord ++ tailWord_827393).sum := by decide
  have hdescent : baseEnd_827393 < baseStart_827393 := by decide
  rcases family_descends (prefixWord ++ tailWord_827393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827406 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_827406 : Nat := 118140960795 + 827406 * 2 ^ 59
def prefixEnd_827406 : Nat := 4983230072969 + 3 ^ 40 * 827406 * 2
def baseEnd_827406 : Nat := 424856974414095003919835

theorem tailTrace_827406 : CollatzResearch.WordTrace tailWord_827406 prefixEnd_827406 424856974414095003919835 := by
  unfold tailWord_827406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3772247005057105817458759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20118650693637897693113381 3772247005057105817458759)
  ·
    refine ⟨5658370507585658726188139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3772247005057105817458759 5658370507585658726188139)
    ·
      refine ⟨8487555761378488089282209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5658370507585658726188139 8487555761378488089282209)
      ·
        refine ⟨6365666821033866066961657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8487555761378488089282209 6365666821033866066961657)
        ·
          refine ⟨4774250115775399550221243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6365666821033866066961657 4774250115775399550221243)
          ·
            refine ⟨7161375173663099325331865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774250115775399550221243 7161375173663099325331865)
            ·
              refine ⟨5371031380247324493998899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7161375173663099325331865 5371031380247324493998899)
              ·
                refine ⟨8056547070370986740998349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371031380247324493998899 8056547070370986740998349)
                ·
                  refine ⟨3021205151389120027874381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8056547070370986740998349 3021205151389120027874381)
                  ·
                    refine ⟨1132951931770920010452893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021205151389120027874381 1132951931770920010452893)
                    ·
                      refine ⟨424856974414095003919835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132951931770920010452893 424856974414095003919835)
                      ·
                        rfl

theorem cell23_827406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_827406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827406 prefixEnd_827406 := by exact prefixLift 827406
  have htrace : WordTrace (prefixWord ++ tailWord_827406) baseStart_827406 baseEnd_827406 := by
    simpa [prefixWord, tailWord_827406, baseEnd_827406] using wordTrace_append hprefix tailTrace_827406
  have hstable : (prefixWord ++ tailWord_827406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827406).length < 2 ^ (prefixWord ++ tailWord_827406).sum := by decide
  have hdescent : baseEnd_827406 < baseStart_827406 := by decide
  rcases family_descends (prefixWord ++ tailWord_827406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827423 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 3]
def baseStart_827423 : Nat := 118140960795 + 827423 * 2 ^ 59
def prefixEnd_827423 : Nat := 4983230072969 + 3 ^ 40 * 827423 * 2
def baseEnd_827423 : Nat := 424865703585221437407257

theorem tailTrace_827423 : CollatzResearch.WordTrace tailWord_827423 prefixEnd_827423 424865703585221437407257 := by
  unfold tailWord_827423
  simp only [CollatzResearch.WordTrace]
  refine ⟨30178596081395258443038923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20119064054263505628692615 30178596081395258443038923)
  ·
    refine ⟨45267894122092887664558385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30178596081395258443038923 45267894122092887664558385)
    ·
      refine ⟨33950920591569665748418789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45267894122092887664558385 33950920591569665748418789)
      ·
        refine ⟨6365797610919312327828523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33950920591569665748418789 6365797610919312327828523)
        ·
          refine ⟨9548696416378968491742785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365797610919312327828523 9548696416378968491742785)
          ·
            refine ⟨7161522312284226368807089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9548696416378968491742785 7161522312284226368807089)
            ·
              refine ⟨5371141734213169776605317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7161522312284226368807089 5371141734213169776605317)
              ·
                refine ⟨1007089075164969333113497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5371141734213169776605317 1007089075164969333113497)
                ·
                  refine ⟨755316806373726999835123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007089075164969333113497 755316806373726999835123)
                  ·
                    refine ⟨1132975209560590499752685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 755316806373726999835123 1132975209560590499752685)
                    ·
                      refine ⟨424865703585221437407257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132975209560590499752685 424865703585221437407257)
                      ·
                        rfl

theorem cell23_827423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_827423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827423 prefixEnd_827423 := by exact prefixLift 827423
  have htrace : WordTrace (prefixWord ++ tailWord_827423) baseStart_827423 baseEnd_827423 := by
    simpa [prefixWord, tailWord_827423, baseEnd_827423] using wordTrace_append hprefix tailTrace_827423
  have hstable : (prefixWord ++ tailWord_827423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827423).length < 2 ^ (prefixWord ++ tailWord_827423).sum := by decide
  have hdescent : baseEnd_827423 < baseStart_827423 := by decide
  rcases family_descends (prefixWord ++ tailWord_827423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827440 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 2, 1, 3]
def baseStart_827440 : Nat := 118140960795 + 827440 * 2 ^ 59
def prefixEnd_827440 : Nat := 4983230072969 + 3 ^ 40 * 827440 * 2
def baseEnd_827440 : Nat := 424874432756347870894679

theorem tailTrace_827440 : CollatzResearch.WordTrace tailWord_827440 prefixEnd_827440 424874432756347870894679 := by
  unfold tailWord_827440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089608061166835173203887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20119477414889113564271849 15089608061166835173203887)
  ·
    refine ⟨22634412091750252759805831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15089608061166835173203887 22634412091750252759805831)
    ·
      refine ⟨33951618137625379139708747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22634412091750252759805831 33951618137625379139708747)
      ·
        refine ⟨50927427206438068709563121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33951618137625379139708747 50927427206438068709563121)
        ·
          refine ⟨38195570404828551532172341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50927427206438068709563121 38195570404828551532172341)
          ·
            refine ⟨3580834725452676706141157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38195570404828551532172341 3580834725452676706141157)
            ·
              refine ⟨671406511022376882401467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3580834725452676706141157 671406511022376882401467)
              ·
                refine ⟨1007109766533565323602201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671406511022376882401467 1007109766533565323602201)
                ·
                  refine ⟨755332324900173992701651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007109766533565323602201 755332324900173992701651)
                  ·
                    refine ⟨1132998487350260989052477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 755332324900173992701651 1132998487350260989052477)
                    ·
                      refine ⟨424874432756347870894679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1132998487350260989052477 424874432756347870894679)
                      ·
                        rfl

theorem cell23_827440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 2, 1, 3].length) (baseStart_827440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827440 prefixEnd_827440 := by exact prefixLift 827440
  have htrace : WordTrace (prefixWord ++ tailWord_827440) baseStart_827440 baseEnd_827440 := by
    simpa [prefixWord, tailWord_827440, baseEnd_827440] using wordTrace_append hprefix tailTrace_827440
  have hstable : (prefixWord ++ tailWord_827440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827440).length < 2 ^ (prefixWord ++ tailWord_827440).sum := by decide
  have hdescent : baseEnd_827440 < baseStart_827440 := by decide
  rcases family_descends (prefixWord ++ tailWord_827440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827444 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_827444 : Nat := 118140960795 + 827444 * 2 ^ 59
def prefixEnd_827444 : Nat := 4983230072969 + 3 ^ 40 * 827444 * 2
def baseEnd_827444 : Nat := 424876486678965855244661

theorem tailTrace_827444 : CollatzResearch.WordTrace tailWord_827444 prefixEnd_827444 424876486678965855244661 := by
  unfold tailWord_827444
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089681007159589514776693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20119574676212786019702257 15089681007159589514776693)
  ·
    refine ⟨1414657594421211517010315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15089681007159589514776693 1414657594421211517010315)
    ·
      refine ⟨2121986391631817275515473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414657594421211517010315 2121986391631817275515473)
      ·
        refine ⟨1591489793723862956636605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121986391631817275515473 1591489793723862956636605)
        ·
          refine ⟨596808672646448608738727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1591489793723862956636605 596808672646448608738727)
          ·
            refine ⟨895213008969672913108091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596808672646448608738727 895213008969672913108091)
            ·
              refine ⟨1342819513454509369662137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895213008969672913108091 1342819513454509369662137)
              ·
                refine ⟨1007114635090882027246603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342819513454509369662137 1007114635090882027246603)
                ·
                  refine ⟨1510671952636323040869905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007114635090882027246603 1510671952636323040869905)
                  ·
                    refine ⟨1133003964477242280652429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510671952636323040869905 1133003964477242280652429)
                    ·
                      refine ⟨424876486678965855244661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1133003964477242280652429 424876486678965855244661)
                      ·
                        rfl

theorem cell23_827444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_827444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827444 prefixEnd_827444 := by exact prefixLift 827444
  have htrace : WordTrace (prefixWord ++ tailWord_827444) baseStart_827444 baseEnd_827444 := by
    simpa [prefixWord, tailWord_827444, baseEnd_827444] using wordTrace_append hprefix tailTrace_827444
  have hstable : (prefixWord ++ tailWord_827444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827444).length < 2 ^ (prefixWord ++ tailWord_827444).sum := by decide
  have hdescent : baseEnd_827444 < baseStart_827444 := by decide
  rcases family_descends (prefixWord ++ tailWord_827444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827459 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4]
def baseStart_827459 : Nat := 118140960795 + 827459 * 2 ^ 59
def prefixEnd_827459 : Nat := 4983230072969 + 3 ^ 40 * 827459 * 2
def baseEnd_827459 : Nat := 424884188888783296557091

theorem tailTrace_827459 : CollatzResearch.WordTrace tailWord_827459 prefixEnd_827459 424884188888783296557091 := by
  unfold tailWord_827459
  simp only [CollatzResearch.WordTrace]
  refine ⟨30179909109264836591349431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20119939406176557727566287 30179909109264836591349431)
  ·
    refine ⟨45269863663897254887024147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30179909109264836591349431 45269863663897254887024147)
    ·
      refine ⟨67904795495845882330536221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45269863663897254887024147 67904795495845882330536221)
      ·
        refine ⟨25464298310942205873951083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67904795495845882330536221 25464298310942205873951083)
        ·
          refine ⟨38196447466413308810926625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25464298310942205873951083 38196447466413308810926625)
          ·
            refine ⟨28647335599809981608194969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38196447466413308810926625 28647335599809981608194969)
            ·
              refine ⟨21485501699857486206146227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28647335599809981608194969 21485501699857486206146227)
              ·
                refine ⟨32228252549786229309219341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21485501699857486206146227 32228252549786229309219341)
                ·
                  refine ⟨12085594706169835990957253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32228252549786229309219341 12085594706169835990957253)
                  ·
                    refine ⟨2266049007406844248304485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12085594706169835990957253 2266049007406844248304485)
                    ·
                      refine ⟨424884188888783296557091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2266049007406844248304485 424884188888783296557091)
                      ·
                        rfl

theorem cell23_827459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_827459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827459 prefixEnd_827459 := by exact prefixLift 827459
  have htrace : WordTrace (prefixWord ++ tailWord_827459) baseStart_827459 baseEnd_827459 := by
    simpa [prefixWord, tailWord_827459, baseEnd_827459] using wordTrace_append hprefix tailTrace_827459
  have hstable : (prefixWord ++ tailWord_827459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827459).length < 2 ^ (prefixWord ++ tailWord_827459).sum := by decide
  have hdescent : baseEnd_827459 < baseStart_827459 := by decide
  rcases family_descends (prefixWord ++ tailWord_827459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827463 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_827463 : Nat := 118140960795 + 827463 * 2 ^ 59
def prefixEnd_827463 : Nat := 4983230072969 + 3 ^ 40 * 827463 * 2
def baseEnd_827463 : Nat := 424886242811401280907073

theorem tailTrace_827463 : CollatzResearch.WordTrace tailWord_827463 prefixEnd_827463 424886242811401280907073 := by
  unfold tailWord_827463
  simp only [CollatzResearch.WordTrace]
  refine ⟨30180055001250345274495043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20120036667500230182996695 30180055001250345274495043)
  ·
    refine ⟨45270082501875517911742565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30180055001250345274495043 45270082501875517911742565)
    ·
      refine ⟨8488140469101659608451731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45270082501875517911742565 8488140469101659608451731)
      ·
        refine ⟨12732210703652489412677597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8488140469101659608451731 12732210703652489412677597)
        ·
          refine ⟨4774579013869683529754099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12732210703652489412677597 4774579013869683529754099)
          ·
            refine ⟨7161868520804525294631149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774579013869683529754099 7161868520804525294631149)
            ·
              refine ⟨2685700695301696985486681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7161868520804525294631149 2685700695301696985486681)
              ·
                refine ⟨2014275521476272739115011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685700695301696985486681 2014275521476272739115011)
                ·
                  refine ⟨3021413282214409108672517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014275521476272739115011 3021413282214409108672517)
                  ·
                    refine ⟨566514990415201707876097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3021413282214409108672517 566514990415201707876097)
                    ·
                      refine ⟨424886242811401280907073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566514990415201707876097 424886242811401280907073)
                      ·
                        rfl

theorem cell23_827463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_827463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827463 prefixEnd_827463 := by exact prefixLift 827463
  have htrace : WordTrace (prefixWord ++ tailWord_827463) baseStart_827463 baseEnd_827463 := by
    simpa [prefixWord, tailWord_827463, baseEnd_827463] using wordTrace_append hprefix tailTrace_827463
  have hstable : (prefixWord ++ tailWord_827463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827463).length < 2 ^ (prefixWord ++ tailWord_827463).sum := by decide
  have hdescent : baseEnd_827463 < baseStart_827463 := by decide
  rcases family_descends (prefixWord ++ tailWord_827463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827476 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_827476 : Nat := 118140960795 + 827476 * 2 ^ 59
def prefixEnd_827476 : Nat := 4983230072969 + 3 ^ 40 * 827476 * 2
def baseEnd_827476 : Nat := 424892918059909730044513

theorem tailTrace_827476 : CollatzResearch.WordTrace tailWord_827476 prefixEnd_827476 424892918059909730044513 := by
  unfold tailWord_827476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090264575101624247359141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20120352766802165663145521 15090264575101624247359141)
  ·
    refine ⟨2829424607831554546379839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15090264575101624247359141 2829424607831554546379839)
    ·
      refine ⟨4244136911747331819569759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2829424607831554546379839 4244136911747331819569759)
      ·
        refine ⟨6366205367620997729354639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4244136911747331819569759 6366205367620997729354639)
        ·
          refine ⟨9549308051431496594031959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6366205367620997729354639 9549308051431496594031959)
          ·
            refine ⟨14323962077147244891047939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9549308051431496594031959 14323962077147244891047939)
            ·
              refine ⟨21485943115720867336571909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14323962077147244891047939 21485943115720867336571909)
              ·
                refine ⟨4028614334197662625607233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21485943115720867336571909 4028614334197662625607233)
                ·
                  refine ⟨3021460750648246969205425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4028614334197662625607233 3021460750648246969205425)
                  ·
                    refine ⟨2266095562986185226904069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3021460750648246969205425 2266095562986185226904069)
                    ·
                      refine ⟨424892918059909730044513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2266095562986185226904069 424892918059909730044513)
                      ·
                        rfl

theorem cell23_827476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_827476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827476 prefixEnd_827476 := by exact prefixLift 827476
  have htrace : WordTrace (prefixWord ++ tailWord_827476) baseStart_827476 baseEnd_827476 := by
    simpa [prefixWord, tailWord_827476, baseEnd_827476] using wordTrace_append hprefix tailTrace_827476
  have hstable : (prefixWord ++ tailWord_827476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827476).length < 2 ^ (prefixWord ++ tailWord_827476).sum := by decide
  have hdescent : baseEnd_827476 < baseStart_827476 := by decide
  rcases family_descends (prefixWord ++ tailWord_827476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827479 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_827479 : Nat := 118140960795 + 827479 * 2 ^ 59
def prefixEnd_827479 : Nat := 4983230072969 + 3 ^ 40 * 827479 * 2
def baseEnd_827479 : Nat := 424894458501873218306999

theorem tailTrace_827479 : CollatzResearch.WordTrace tailWord_827479 prefixEnd_827479 424894458501873218306999 := by
  unfold tailWord_827479
  simp only [CollatzResearch.WordTrace]
  refine ⟨30180638569192380007077491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20120425712794920004718327 30180638569192380007077491)
  ·
    refine ⟨45270957853788570010616237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30180638569192380007077491 45270957853788570010616237)
    ·
      refine ⟨16976609195170713753981089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45270957853788570010616237 16976609195170713753981089)
      ·
        refine ⟨12732456896378035315485817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16976609195170713753981089 12732456896378035315485817)
        ·
          refine ⟨9549342672283526486614363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12732456896378035315485817 9549342672283526486614363)
          ·
            refine ⟨14324014008425289729921545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9549342672283526486614363 14324014008425289729921545)
            ·
              refine ⟨10743010506318967297441159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14324014008425289729921545 10743010506318967297441159)
              ·
                refine ⟨16114515759478450946161739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743010506318967297441159 16114515759478450946161739)
                ·
                  refine ⟨24171773639217676419242609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16114515759478450946161739 24171773639217676419242609)
                  ·
                    refine ⟨18128830229413257314431957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24171773639217676419242609 18128830229413257314431957)
                    ·
                      refine ⟨424894458501873218306999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18128830229413257314431957 424894458501873218306999)
                      ·
                        rfl

theorem cell23_827479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_827479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827479 prefixEnd_827479 := by exact prefixLift 827479
  have htrace : WordTrace (prefixWord ++ tailWord_827479) baseStart_827479 baseEnd_827479 := by
    simpa [prefixWord, tailWord_827479, baseEnd_827479] using wordTrace_append hprefix tailTrace_827479
  have hstable : (prefixWord ++ tailWord_827479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827479).length < 2 ^ (prefixWord ++ tailWord_827479).sum := by decide
  have hdescent : baseEnd_827479 < baseStart_827479 := by decide
  rcases family_descends (prefixWord ++ tailWord_827479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827480 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 2, 2, 2]
def baseStart_827480 : Nat := 118140960795 + 827480 * 2 ^ 59
def prefixEnd_827480 : Nat := 4983230072969 + 3 ^ 40 * 827480 * 2
def baseEnd_827480 : Nat := 424894971982527714394495

theorem tailTrace_827480 : CollatzResearch.WordTrace tailWord_827480 prefixEnd_827480 424894971982527714394495 := by
  unfold tailWord_827480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090337521094378588931947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20120450028125838118575929 15090337521094378588931947)
  ·
    refine ⟨22635506281641567883397921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15090337521094378588931947 22635506281641567883397921)
    ·
      refine ⟨16976629711231175912548441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22635506281641567883397921 16976629711231175912548441)
      ·
        refine ⟨12732472283423381934411331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16976629711231175912548441 12732472283423381934411331)
        ·
          refine ⟨19098708425135072901616997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12732472283423381934411331 19098708425135072901616997)
          ·
            refine ⟨3581007829712826169053187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19098708425135072901616997 3581007829712826169053187)
            ·
              refine ⟨5371511744569239253579781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581007829712826169053187 5371511744569239253579781)
              ·
                refine ⟨1007158452106732360046209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5371511744569239253579781 1007158452106732360046209)
                ·
                  refine ⟨755368839080049270034657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007158452106732360046209 755368839080049270034657)
                  ·
                    refine ⟨566526629310036952525993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 755368839080049270034657 566526629310036952525993)
                    ·
                      refine ⟨424894971982527714394495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566526629310036952525993 424894971982527714394495)
                      ·
                        rfl

theorem cell23_827480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_827480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827480 prefixEnd_827480 := by exact prefixLift 827480
  have htrace : WordTrace (prefixWord ++ tailWord_827480) baseStart_827480 baseEnd_827480 := by
    simpa [prefixWord, tailWord_827480, baseEnd_827480] using wordTrace_append hprefix tailTrace_827480
  have hstable : (prefixWord ++ tailWord_827480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827480).length < 2 ^ (prefixWord ++ tailWord_827480).sum := by decide
  have hdescent : baseEnd_827480 < baseStart_827480 := by decide
  rcases family_descends (prefixWord ++ tailWord_827480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827489 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_827489 : Nat := 118140960795 + 827489 * 2 ^ 59
def prefixEnd_827489 : Nat := 4983230072969 + 3 ^ 40 * 827489 * 2
def baseEnd_827489 : Nat := 424899593308418179181953

theorem tailTrace_827489 : CollatzResearch.WordTrace tailWord_827489 prefixEnd_827489 424899593308418179181953 := by
  unfold tailWord_827489
  simp only [CollatzResearch.WordTrace]
  refine ⟨30181003299156151714941521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20120668866104101143294347 30181003299156151714941521)
  ·
    refine ⟨22635752474367113786206141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30181003299156151714941521 22635752474367113786206141)
    ·
      refine ⟨8488407177887667669827303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22635752474367113786206141 8488407177887667669827303)
      ·
        refine ⟨12732610766831501504740955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8488407177887667669827303 12732610766831501504740955)
        ·
          refine ⟨19098916150247252257111433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12732610766831501504740955 19098916150247252257111433)
          ·
            refine ⟨14324187112685439192833575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19098916150247252257111433 14324187112685439192833575)
            ·
              refine ⟨21486280669028158789250363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14324187112685439192833575 21486280669028158789250363)
              ·
                refine ⟨32229421003542238183875545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21486280669028158789250363 32229421003542238183875545)
                ·
                  refine ⟨24172065752656678637906659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32229421003542238183875545 24172065752656678637906659)
                  ·
                    refine ⟨36258098628985017956859989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24172065752656678637906659 36258098628985017956859989)
                    ·
                      refine ⟨424899593308418179181953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36258098628985017956859989 424899593308418179181953)
                      ·
                        rfl

theorem cell23_827489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_827489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827489 prefixEnd_827489 := by exact prefixLift 827489
  have htrace : WordTrace (prefixWord ++ tailWord_827489) baseStart_827489 baseEnd_827489 := by
    simpa [prefixWord, tailWord_827489, baseEnd_827489] using wordTrace_append hprefix tailTrace_827489
  have hstable : (prefixWord ++ tailWord_827489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827489).length < 2 ^ (prefixWord ++ tailWord_827489).sum := by decide
  have hdescent : baseEnd_827489 < baseStart_827489 := by decide
  rcases family_descends (prefixWord ++ tailWord_827489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827516 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_827516 : Nat := 118140960795 + 827516 * 2 ^ 59
def prefixEnd_827516 : Nat := 4983230072969 + 3 ^ 40 * 827516 * 2
def baseEnd_827516 : Nat := 141637819095363191181443

theorem tailTrace_827516 : CollatzResearch.WordTrace tailWord_827516 prefixEnd_827516 141637819095363191181443 := by
  unfold tailWord_827516
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090994035029167663087201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20121325380038890217449601 15090994035029167663087201)
  ·
    refine ⟨11318245526271875747315401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15090994035029167663087201 11318245526271875747315401)
    ·
      refine ⟨8488684144703906810486551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11318245526271875747315401 8488684144703906810486551)
      ·
        refine ⟨12733026217055860215729827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8488684144703906810486551 12733026217055860215729827)
        ·
          refine ⟨19099539325583790323594741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12733026217055860215729827 19099539325583790323594741)
          ·
            refine ⟨1790581811773480342837007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19099539325583790323594741 1790581811773480342837007)
            ·
              refine ⟨2685872717660220514255511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790581811773480342837007 2685872717660220514255511)
              ·
                refine ⟨4028809076490330771383267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685872717660220514255511 4028809076490330771383267)
                ·
                  refine ⟨6043213614735496157074901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028809076490330771383267 6043213614735496157074901)
                  ·
                    refine ⟨141637819095363191181443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6043213614735496157074901 141637819095363191181443)
                    ·
                      rfl

theorem cell23_827516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_827516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827516 prefixEnd_827516 := by exact prefixLift 827516
  have htrace : WordTrace (prefixWord ++ tailWord_827516) baseStart_827516 baseEnd_827516 := by
    simpa [prefixWord, tailWord_827516, baseEnd_827516] using wordTrace_append hprefix tailTrace_827516
  have hstable : (prefixWord ++ tailWord_827516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827516).length < 2 ^ (prefixWord ++ tailWord_827516).sum := by decide
  have hdescent : baseEnd_827516 < baseStart_827516 := by decide
  rcases family_descends (prefixWord ++ tailWord_827516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827536 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_827536 : Nat := 118140960795 + 827536 * 2 ^ 59
def prefixEnd_827536 : Nat := 4983230072969 + 3 ^ 40 * 827536 * 2
def baseEnd_827536 : Nat := 424923726899179495294237

theorem tailTrace_827536 : CollatzResearch.WordTrace tailWord_827536 prefixEnd_827536 424923726899179495294237 := by
  unfold tailWord_827536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15091358764992939370951231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20121811686657252494601641 15091358764992939370951231)
  ·
    refine ⟨22637038147489409056426847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15091358764992939370951231 22637038147489409056426847)
    ·
      refine ⟨33955557221234113584640271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22637038147489409056426847 33955557221234113584640271)
      ·
        refine ⟨50933335831851170376960407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33955557221234113584640271 50933335831851170376960407)
        ·
          refine ⟨76400003747776755565440611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50933335831851170376960407 76400003747776755565440611)
          ·
            refine ⟨114600005621665133348160917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76400003747776755565440611 114600005621665133348160917)
            ·
              refine ⟨5371875263515553125695043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114600005621665133348160917 5371875263515553125695043)
              ·
                refine ⟨8057812895273329688542565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5371875263515553125695043 8057812895273329688542565)
                ·
                  refine ⟨1510839917863749316601731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8057812895273329688542565 1510839917863749316601731)
                  ·
                    refine ⟨2266259876795623974902597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510839917863749316601731 2266259876795623974902597)
                    ·
                      refine ⟨424923726899179495294237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2266259876795623974902597 424923726899179495294237)
                      ·
                        rfl

theorem cell23_827536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_827536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827536 prefixEnd_827536 := by exact prefixLift 827536
  have htrace : WordTrace (prefixWord ++ tailWord_827536) baseStart_827536 baseEnd_827536 := by
    simpa [prefixWord, tailWord_827536, baseEnd_827536] using wordTrace_append hprefix tailTrace_827536
  have hstable : (prefixWord ++ tailWord_827536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827536).length < 2 ^ (prefixWord ++ tailWord_827536).sum := by decide
  have hdescent : baseEnd_827536 < baseStart_827536 := by decide
  rcases family_descends (prefixWord ++ tailWord_827536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827680 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_827680 : Nat := 118140960795 + 827680 * 2 ^ 59
def prefixEnd_827680 : Nat := 4983230072969 + 3 ^ 40 * 827680 * 2
def baseEnd_827680 : Nat := 424997668113426931893575

theorem tailTrace_827680 : CollatzResearch.WordTrace tailWord_827680 prefixEnd_827680 424997668113426931893575 := by
  unfold tailWord_827680
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093984820732095667572247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20125313094309460890096329 15093984820732095667572247)
  ·
    refine ⟨22640977231098143501358371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15093984820732095667572247 22640977231098143501358371)
    ·
      refine ⟨33961465846647215252037557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22640977231098143501358371 33961465846647215252037557)
      ·
        refine ⟨3183887423123176429878521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33961465846647215252037557 3183887423123176429878521)
        ·
          refine ⟨2387915567342382322408891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3183887423123176429878521 2387915567342382322408891)
          ·
            refine ⟨3581873351013573483613337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387915567342382322408891 3581873351013573483613337)
            ·
              refine ⟨2686405013260180112710003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3581873351013573483613337 2686405013260180112710003)
              ·
                refine ⟨4029607519890270169065005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686405013260180112710003 4029607519890270169065005)
                ·
                  refine ⟨1511102819958851313399377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4029607519890270169065005 1511102819958851313399377)
                  ·
                    refine ⟨1133327114969138485049533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511102819958851313399377 1133327114969138485049533)
                    ·
                      refine ⟨424997668113426931893575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1133327114969138485049533 424997668113426931893575)
                      ·
                        rfl

theorem cell23_827680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_827680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827680 prefixEnd_827680 := by exact prefixLift 827680
  have htrace : WordTrace (prefixWord ++ tailWord_827680) baseStart_827680 baseEnd_827680 := by
    simpa [prefixWord, tailWord_827680, baseEnd_827680] using wordTrace_append hprefix tailTrace_827680
  have hstable : (prefixWord ++ tailWord_827680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827680).length < 2 ^ (prefixWord ++ tailWord_827680).sum := by decide
  have hdescent : baseEnd_827680 < baseStart_827680 := by decide
  rcases family_descends (prefixWord ++ tailWord_827680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827683 : List Nat := [1, 1, 1, 4, 2, 2, 5, 7]
def baseStart_827683 : Nat := 118140960795 + 827683 * 2 ^ 59
def prefixEnd_827683 : Nat := 4983230072969 + 3 ^ 40 * 827683 * 2
def baseEnd_827683 : Nat := 15740711427977422968743

theorem tailTrace_827683 : CollatzResearch.WordTrace tailWord_827683 prefixEnd_827683 15740711427977422968743 := by
  unfold tailWord_827683
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188079060453322847503703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20125386040302215231669135 30188079060453322847503703)
  ·
    refine ⟨45282118590679984271255555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30188079060453322847503703 45282118590679984271255555)
    ·
      refine ⟨67923177886019976406883333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45282118590679984271255555 67923177886019976406883333)
      ·
        refine ⟨12735595853628745576290625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67923177886019976406883333 12735595853628745576290625)
        ·
          refine ⟨9551696890221559182217969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12735595853628745576290625 9551696890221559182217969)
          ·
            refine ⟨7163772667666169386663477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9551696890221559182217969 7163772667666169386663477)
            ·
              refine ⟨671603687593703379999701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7163772667666169386663477 671603687593703379999701)
              ·
                refine ⟨15740711427977422968743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 671603687593703379999701 15740711427977422968743)
                ·
                  rfl

theorem cell23_827683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 7].length) (baseStart_827683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827683 prefixEnd_827683 := by exact prefixLift 827683
  have htrace : WordTrace (prefixWord ++ tailWord_827683) baseStart_827683 baseEnd_827683 := by
    simpa [prefixWord, tailWord_827683, baseEnd_827683] using wordTrace_append hprefix tailTrace_827683
  have hstable : (prefixWord ++ tailWord_827683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827683).length < 2 ^ (prefixWord ++ tailWord_827683).sum := by decide
  have hdescent : baseEnd_827683 < baseStart_827683 := by decide
  rcases family_descends (prefixWord ++ tailWord_827683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827694 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_827694 : Nat := 118140960795 + 827694 * 2 ^ 59
def prefixEnd_827694 : Nat := 4983230072969 + 3 ^ 40 * 827694 * 2
def baseEnd_827694 : Nat := 425004856842589877118511

theorem tailTrace_827694 : CollatzResearch.WordTrace tailWord_827694 prefixEnd_827694 425004856842589877118511 := by
  unfold tailWord_827694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3773560032926683965769267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20125653508942314484102757 3773560032926683965769267)
  ·
    refine ⟨5660340049390025948653901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3773560032926683965769267 5660340049390025948653901)
    ·
      refine ⟨2122627518521259730745213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5660340049390025948653901 2122627518521259730745213)
      ·
        refine ⟨795985319445472399029455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2122627518521259730745213 795985319445472399029455)
        ·
          refine ⟨1193977979168208598544183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795985319445472399029455 1193977979168208598544183)
          ·
            refine ⟨1790966968752312897816275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193977979168208598544183 1790966968752312897816275)
            ·
              refine ⟨2686450453128469346724413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790966968752312897816275 2686450453128469346724413)
              ·
                refine ⟨1007418919923176005021655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686450453128469346724413 1007418919923176005021655)
                ·
                  refine ⟨1511128379884764007532483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007418919923176005021655 1511128379884764007532483)
                  ·
                    refine ⟨2266692569827146011298725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511128379884764007532483 2266692569827146011298725)
                    ·
                      refine ⟨425004856842589877118511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2266692569827146011298725 425004856842589877118511)
                      ·
                        rfl

theorem cell23_827694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_827694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827694 prefixEnd_827694 := by exact prefixLift 827694
  have htrace : WordTrace (prefixWord ++ tailWord_827694) baseStart_827694 baseEnd_827694 := by
    simpa [prefixWord, tailWord_827694, baseEnd_827694] using wordTrace_append hprefix tailTrace_827694
  have hstable : (prefixWord ++ tailWord_827694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827694).length < 2 ^ (prefixWord ++ tailWord_827694).sum := by decide
  have hdescent : baseEnd_827694 < baseStart_827694 := by decide
  rcases family_descends (prefixWord ++ tailWord_827694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827696 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_827696 : Nat := 118140960795 + 827696 * 2 ^ 59
def prefixEnd_827696 : Nat := 4983230072969 + 3 ^ 40 * 827696 * 2
def baseEnd_827696 : Nat := 141668627934632956431167

theorem tailTrace_827696 : CollatzResearch.WordTrace tailWord_827696 prefixEnd_827696 141668627934632956431167 := by
  unfold tailWord_827696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15094276604703113033863471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20125702139604150711817961 15094276604703113033863471)
  ·
    refine ⟨22641414907054669550795207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15094276604703113033863471 22641414907054669550795207)
    ·
      refine ⟨33962122360582004326192811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22641414907054669550795207 33962122360582004326192811)
      ·
        refine ⟨50943183540873006489289217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33962122360582004326192811 50943183540873006489289217)
        ·
          refine ⟨38207387655654754866966913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50943183540873006489289217 38207387655654754866966913)
          ·
            refine ⟨28655540741741066150225185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38207387655654754866966913 28655540741741066150225185)
            ·
              refine ⟨21491655556305799612668889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28655540741741066150225185 21491655556305799612668889)
              ·
                refine ⟨16118741667229349709501667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21491655556305799612668889 16118741667229349709501667)
                ·
                  refine ⟨24178112500844024564252501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16118741667229349709501667 24178112500844024564252501)
                  ·
                    refine ⟨141668627934632956431167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24178112500844024564252501 141668627934632956431167)
                    ·
                      rfl

theorem cell23_827696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_827696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827696 prefixEnd_827696 := by exact prefixLift 827696
  have htrace : WordTrace (prefixWord ++ tailWord_827696) baseStart_827696 baseEnd_827696 := by
    simpa [prefixWord, tailWord_827696, baseEnd_827696] using wordTrace_append hprefix tailTrace_827696
  have hstable : (prefixWord ++ tailWord_827696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827696).length < 2 ^ (prefixWord ++ tailWord_827696).sum := by decide
  have hdescent : baseEnd_827696 < baseStart_827696 := by decide
  rcases family_descends (prefixWord ++ tailWord_827696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827697 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 3]
def baseStart_827697 : Nat := 118140960795 + 827697 * 2 ^ 59
def prefixEnd_827697 : Nat := 4983230072969 + 3 ^ 40 * 827697 * 2
def baseEnd_827697 : Nat := 425006397284553365380997

theorem tailTrace_827697 : CollatzResearch.WordTrace tailWord_827697 prefixEnd_827697 425006397284553365380997 := by
  unfold tailWord_827697
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188589682402603238513345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20125726454935068825675563 30188589682402603238513345)
  ·
    refine ⟨22641442261801952428885009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30188589682402603238513345 22641442261801952428885009)
    ·
      refine ⟨16981081696351464321663757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22641442261801952428885009 16981081696351464321663757)
      ·
        refine ⟨6367905636131799120623909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16981081696351464321663757 6367905636131799120623909)
        ·
          refine ⟨1193982306774712335116983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6367905636131799120623909 1193982306774712335116983)
          ·
            refine ⟨1790973460162068502675475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193982306774712335116983 1790973460162068502675475)
            ·
              refine ⟨2686460190243102754013213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790973460162068502675475 2686460190243102754013213)
              ·
                refine ⟨1007422571341163532754955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686460190243102754013213 1007422571341163532754955)
                ·
                  refine ⟨1511133857011745299132433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007422571341163532754955 1511133857011745299132433)
                  ·
                    refine ⟨1133350392758808974349325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511133857011745299132433 1133350392758808974349325)
                    ·
                      refine ⟨425006397284553365380997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1133350392758808974349325 425006397284553365380997)
                      ·
                        rfl

theorem cell23_827697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_827697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827697 prefixEnd_827697 := by exact prefixLift 827697
  have htrace : WordTrace (prefixWord ++ tailWord_827697) baseStart_827697 baseEnd_827697 := by
    simpa [prefixWord, tailWord_827697, baseEnd_827697] using wordTrace_append hprefix tailTrace_827697
  have hstable : (prefixWord ++ tailWord_827697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827697).length < 2 ^ (prefixWord ++ tailWord_827697).sum := by decide
  have hdescent : baseEnd_827697 < baseStart_827697 := by decide
  rcases family_descends (prefixWord ++ tailWord_827697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827720 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_827720 : Nat := 118140960795 + 827720 * 2 ^ 59
def prefixEnd_827720 : Nat := 4983230072969 + 3 ^ 40 * 827720 * 2
def baseEnd_827720 : Nat := 425018207339606775393391

theorem tailTrace_827720 : CollatzResearch.WordTrace tailWord_827720 prefixEnd_827720 425018207339606775393391 := by
  unfold tailWord_827720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15094714280659639083300307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20126285707546185444400409 15094714280659639083300307)
  ·
    refine ⟨22642071420989458624950461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15094714280659639083300307 22642071420989458624950461)
    ·
      refine ⟨8490776782871046984356423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22642071420989458624950461 8490776782871046984356423)
      ·
        refine ⟨12736165174306570476534635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8490776782871046984356423 12736165174306570476534635)
        ·
          refine ⟨19104247761459855714801953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12736165174306570476534635 19104247761459855714801953)
          ·
            refine ⟨14328185821094891786101465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19104247761459855714801953 14328185821094891786101465)
            ·
              refine ⟨10746139365821168839576099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14328185821094891786101465 10746139365821168839576099)
              ·
                refine ⟨16119209048731753259364149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746139365821168839576099 16119209048731753259364149)
                ·
                  refine ⟨1511175848318601868065389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16119209048731753259364149 1511175848318601868065389)
                  ·
                    refine ⟨566690943119475700524521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511175848318601868065389 566690943119475700524521)
                    ·
                      refine ⟨425018207339606775393391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566690943119475700524521 425018207339606775393391)
                      ·
                        rfl

theorem cell23_827720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_827720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827720 prefixEnd_827720 := by exact prefixLift 827720
  have htrace : WordTrace (prefixWord ++ tailWord_827720) baseStart_827720 baseEnd_827720 := by
    simpa [prefixWord, tailWord_827720, baseEnd_827720] using wordTrace_append hprefix tailTrace_827720
  have hstable : (prefixWord ++ tailWord_827720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827720).length < 2 ^ (prefixWord ++ tailWord_827720).sum := by decide
  have hdescent : baseEnd_827720 < baseStart_827720 := by decide
  rcases family_descends (prefixWord ++ tailWord_827720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827753 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_827753 : Nat := 118140960795 + 827753 * 2 ^ 59
def prefixEnd_827753 : Nat := 4983230072969 + 3 ^ 40 * 827753 * 2
def baseEnd_827753 : Nat := 425035152201205146280739

theorem tailTrace_827753 : CollatzResearch.WordTrace tailWord_827753 prefixEnd_827753 425035152201205146280739 := by
  unfold tailWord_827753
  simp only [CollatzResearch.WordTrace]
  refine ⟨30190632170199724802551913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20127088113466483201701275 30190632170199724802551913)
  ·
    refine ⟨22642974127649793601913935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30190632170199724802551913 22642974127649793601913935)
    ·
      refine ⟨33964461191474690402870903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22642974127649793601913935 33964461191474690402870903)
      ·
        refine ⟨50946691787212035604306355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33964461191474690402870903 50946691787212035604306355)
        ·
          refine ⟨76420037680818053406459533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50946691787212035604306355 76420037680818053406459533)
          ·
            refine ⟨28657514130306770027422325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76420037680818053406459533 28657514130306770027422325)
            ·
              refine ⟨2686641949716259690070843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28657514130306770027422325 2686641949716259690070843)
              ·
                refine ⟨4029962924574389535106265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686641949716259690070843 4029962924574389535106265)
                ·
                  refine ⟨3022472193430792151329699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4029962924574389535106265 3022472193430792151329699)
                  ·
                    refine ⟨4533708290146188226994549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3022472193430792151329699 4533708290146188226994549)
                    ·
                      refine ⟨425035152201205146280739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4533708290146188226994549 425035152201205146280739)
                      ·
                        rfl

theorem cell23_827753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_827753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827753 prefixEnd_827753 := by exact prefixLift 827753
  have htrace : WordTrace (prefixWord ++ tailWord_827753) baseStart_827753 baseEnd_827753 := by
    simpa [prefixWord, tailWord_827753, baseEnd_827753] using wordTrace_append hprefix tailTrace_827753
  have hstable : (prefixWord ++ tailWord_827753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827753).length < 2 ^ (prefixWord ++ tailWord_827753).sum := by decide
  have hdescent : baseEnd_827753 < baseStart_827753 := by decide
  rcases family_descends (prefixWord ++ tailWord_827753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827754 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_827754 : Nat := 118140960795 + 827754 * 2 ^ 59
def prefixEnd_827754 : Nat := 4983230072969 + 3 ^ 40 * 827754 * 2
def baseEnd_827754 : Nat := 425035665681859642368235

theorem tailTrace_827754 : CollatzResearch.WordTrace tailWord_827754 prefixEnd_827754 425035665681859642368235 := by
  unfold tailWord_827754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547667160799025493334579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20127112428797401315558877 7547667160799025493334579)
  ·
    refine ⟨11321500741198538240001869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7547667160799025493334579 11321500741198538240001869)
    ·
      refine ⟨4245562777949451840000701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11321500741198538240001869 4245562777949451840000701)
      ·
        refine ⟨1592086041731044440000263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4245562777949451840000701 1592086041731044440000263)
        ·
          refine ⟨2388129062596566660000395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592086041731044440000263 2388129062596566660000395)
          ·
            refine ⟨3582193593894849990000593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388129062596566660000395 3582193593894849990000593)
            ·
              refine ⟨2686645195421137492500445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582193593894849990000593 2686645195421137492500445)
              ·
                refine ⟨1007491948282926559687667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686645195421137492500445 1007491948282926559687667)
                ·
                  refine ⟨1511237922424389839531501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007491948282926559687667 1511237922424389839531501)
                  ·
                    refine ⟨566714220909146189824313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1511237922424389839531501 566714220909146189824313)
                    ·
                      refine ⟨425035665681859642368235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566714220909146189824313 425035665681859642368235)
                      ·
                        rfl

theorem cell23_827754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_827754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827754 prefixEnd_827754 := by exact prefixLift 827754
  have htrace : WordTrace (prefixWord ++ tailWord_827754) baseStart_827754 baseEnd_827754 := by
    simpa [prefixWord, tailWord_827754, baseEnd_827754] using wordTrace_append hprefix tailTrace_827754
  have hstable : (prefixWord ++ tailWord_827754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827754).length < 2 ^ (prefixWord ++ tailWord_827754).sum := by decide
  have hdescent : baseEnd_827754 < baseStart_827754 := by decide
  rcases family_descends (prefixWord ++ tailWord_827754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827784 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_827784 : Nat := 118140960795 + 827784 * 2 ^ 59
def prefixEnd_827784 : Nat := 4983230072969 + 3 ^ 40 * 827784 * 2
def baseEnd_827784 : Nat := 425051070101494524993097

theorem tailTrace_827784 : CollatzResearch.WordTrace tailWord_827784 prefixEnd_827784 425051070101494524993097 := by
  unfold tailWord_827784
  simp only [CollatzResearch.WordTrace]
  refine ⟨15095881416543708548465203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20127841888724944731286937 15095881416543708548465203)
  ·
    refine ⟨22643822124815562822697805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15095881416543708548465203 22643822124815562822697805)
    ·
      refine ⟨8491433296805836058511677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22643822124815562822697805 8491433296805836058511677)
      ·
        refine ⟨3184287486302188521941879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8491433296805836058511677 3184287486302188521941879)
        ·
          refine ⟨4776431229453282782912819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184287486302188521941879 4776431229453282782912819)
          ·
            refine ⟨7164646844179924174369229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776431229453282782912819 7164646844179924174369229)
            ·
              refine ⟨2686742566567471565388461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7164646844179924174369229 2686742566567471565388461)
              ·
                refine ⟨1007528462462801837020673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686742566567471565388461 1007528462462801837020673)
                ·
                  refine ⟨755646346847101377765505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007528462462801837020673 755646346847101377765505)
                  ·
                    refine ⟨566734760135326033324129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 755646346847101377765505 566734760135326033324129)
                    ·
                      refine ⟨425051070101494524993097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 566734760135326033324129 425051070101494524993097)
                      ·
                        rfl

theorem cell23_827784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_827784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827784 prefixEnd_827784 := by exact prefixLift 827784
  have htrace : WordTrace (prefixWord ++ tailWord_827784) baseStart_827784 baseEnd_827784 := by
    simpa [prefixWord, tailWord_827784, baseEnd_827784] using wordTrace_append hprefix tailTrace_827784
  have hstable : (prefixWord ++ tailWord_827784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827784).length < 2 ^ (prefixWord ++ tailWord_827784).sum := by decide
  have hdescent : baseEnd_827784 < baseStart_827784 := by decide
  rcases family_descends (prefixWord ++ tailWord_827784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827813 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_827813 : Nat := 118140960795 + 827813 * 2 ^ 59
def prefixEnd_827813 : Nat := 4983230072969 + 3 ^ 40 * 827813 * 2
def baseEnd_827813 : Nat := 425065961040474911530463

theorem tailTrace_827813 : CollatzResearch.WordTrace tailWord_827813 prefixEnd_827813 425065961040474911530463 := by
  unfold tailWord_827813
  simp only [CollatzResearch.WordTrace]
  refine ⟨30192820549982355049736093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20128547033321570033157395 30192820549982355049736093)
  ·
    refine ⟨11322307706243383143651035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30192820549982355049736093 11322307706243383143651035)
    ·
      refine ⟨16983461559365074715476553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11322307706243383143651035 16983461559365074715476553)
      ·
        refine ⟨12737596169523806036607415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16983461559365074715476553 12737596169523806036607415)
        ·
          refine ⟨19106394254285709054911123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737596169523806036607415 19106394254285709054911123)
          ·
            refine ⟨28659591381428563582366685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19106394254285709054911123 28659591381428563582366685)
            ·
              refine ⟨10747346768035711343387507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28659591381428563582366685 10747346768035711343387507)
              ·
                refine ⟨16121020152053567015081261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10747346768035711343387507 16121020152053567015081261)
                ·
                  refine ⟨6045382557020087630655473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16121020152053567015081261 6045382557020087630655473)
                  ·
                    refine ⟨4534036917765065722991605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6045382557020087630655473 4534036917765065722991605)
                    ·
                      refine ⟨425065961040474911530463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4534036917765065722991605 425065961040474911530463)
                      ·
                        rfl

theorem cell23_827813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_827813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827813 prefixEnd_827813 := by exact prefixLift 827813
  have htrace : WordTrace (prefixWord ++ tailWord_827813) baseStart_827813 baseEnd_827813 := by
    simpa [prefixWord, tailWord_827813, baseEnd_827813] using wordTrace_append hprefix tailTrace_827813
  have hstable : (prefixWord ++ tailWord_827813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827813).length < 2 ^ (prefixWord ++ tailWord_827813).sum := by decide
  have hdescent : baseEnd_827813 < baseStart_827813 := by decide
  rcases family_descends (prefixWord ++ tailWord_827813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827823 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_827823 : Nat := 118140960795 + 827823 * 2 ^ 59
def prefixEnd_827823 : Nat := 4983230072969 + 3 ^ 40 * 827823 * 2
def baseEnd_827823 : Nat := 425071095847019872405417

theorem tailTrace_827823 : CollatzResearch.WordTrace tailWord_827823 prefixEnd_827823 425071095847019872405417 := by
  unfold tailWord_827823
  simp only [CollatzResearch.WordTrace]
  refine ⟨30193185279946126757600123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20128790186630751171733415 30193185279946126757600123)
  ·
    refine ⟨45289777919919190136400185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30193185279946126757600123 45289777919919190136400185)
    ·
      refine ⟨33967333439939392602300139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45289777919919190136400185 33967333439939392602300139)
      ·
        refine ⟨50951000159909088903450209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33967333439939392602300139 50951000159909088903450209)
        ·
          refine ⟨38213250119931816677587657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50951000159909088903450209 38213250119931816677587657)
          ·
            refine ⟨28659937589948862508190743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38213250119931816677587657 28659937589948862508190743)
            ·
              refine ⟨42989906384923293762286115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28659937589948862508190743 42989906384923293762286115)
              ·
                refine ⟨64484859577384940643429173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42989906384923293762286115 64484859577384940643429173)
                ·
                  refine ⟨6045455585379838185321485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64484859577384940643429173 6045455585379838185321485)
                  ·
                    refine ⟨2267045844517439319495557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6045455585379838185321485 2267045844517439319495557)
                    ·
                      refine ⟨425071095847019872405417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2267045844517439319495557 425071095847019872405417)
                      ·
                        rfl

theorem cell23_827823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_827823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827823 prefixEnd_827823 := by exact prefixLift 827823
  have htrace : WordTrace (prefixWord ++ tailWord_827823) baseStart_827823 baseEnd_827823 := by
    simpa [prefixWord, tailWord_827823, baseEnd_827823] using wordTrace_append hprefix tailTrace_827823
  have hstable : (prefixWord ++ tailWord_827823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827823).length < 2 ^ (prefixWord ++ tailWord_827823).sum := by decide
  have hdescent : baseEnd_827823 < baseStart_827823 := by decide
  rcases family_descends (prefixWord ++ tailWord_827823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827880 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 8]
def baseStart_827880 : Nat := 118140960795 + 827880 * 2 ^ 59
def prefixEnd_827880 : Nat := 4983230072969 + 3 ^ 40 * 827880 * 2
def baseEnd_827880 : Nat := 47233373804925127710295

theorem tailTrace_827880 : CollatzResearch.WordTrace tailWord_827880 prefixEnd_827880 47233373804925127710295 := by
  unfold tailWord_827880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15097632120369812746212547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20130176160493083661616729 15097632120369812746212547)
  ·
    refine ⟨22646448180554719119318821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15097632120369812746212547 22646448180554719119318821)
    ·
      refine ⟨4246209033854009834872279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22646448180554719119318821 4246209033854009834872279)
      ·
        refine ⟨6369313550781014752308419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246209033854009834872279 6369313550781014752308419)
        ·
          refine ⟨9553970326171522128462629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369313550781014752308419 9553970326171522128462629)
          ·
            refine ⟨1791369436157160399086743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9553970326171522128462629 1791369436157160399086743)
            ·
              refine ⟨2687054154235740598630115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791369436157160399086743 2687054154235740598630115)
              ·
                refine ⟨4030581231353610897945173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687054154235740598630115 4030581231353610897945173)
                ·
                  refine ⟨47233373804925127710295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4030581231353610897945173 47233373804925127710295)
                  ·
                    rfl

theorem cell23_827880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_827880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827880 prefixEnd_827880 := by exact prefixLift 827880
  have htrace : WordTrace (prefixWord ++ tailWord_827880) baseStart_827880 baseEnd_827880 := by
    simpa [prefixWord, tailWord_827880, baseEnd_827880] using wordTrace_append hprefix tailTrace_827880
  have hstable : (prefixWord ++ tailWord_827880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827880).length < 2 ^ (prefixWord ++ tailWord_827880).sum := by decide
  have hdescent : baseEnd_827880 < baseStart_827880 := by decide
  rcases family_descends (prefixWord ++ tailWord_827880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827883 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_827883 : Nat := 118140960795 + 827883 * 2 ^ 59
def prefixEnd_827883 : Nat := 4983230072969 + 3 ^ 40 * 827883 * 2
def baseEnd_827883 : Nat := 425101904686289637655141

theorem tailTrace_827883 : CollatzResearch.WordTrace tailWord_827883 prefixEnd_827883 425101904686289637655141 := by
  unfold tailWord_827883
  simp only [CollatzResearch.WordTrace]
  refine ⟨30195373659728757004784303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20130249106485838003189535 30195373659728757004784303)
  ·
    refine ⟨45293060489593135507176455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30195373659728757004784303 45293060489593135507176455)
    ·
      refine ⟨67939590734389703260764683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45293060489593135507176455 67939590734389703260764683)
      ·
        refine ⟨101909386101584554891147025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67939590734389703260764683 101909386101584554891147025)
        ·
          refine ⟨76432039576188416168360269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101909386101584554891147025 76432039576188416168360269)
          ·
            refine ⟨28662014841070656063135101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76432039576188416168360269 28662014841070656063135101)
            ·
              refine ⟨10748255565401496023675663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28662014841070656063135101 10748255565401496023675663)
              ·
                refine ⟨16122383348102244035513495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10748255565401496023675663 16122383348102244035513495)
                ·
                  refine ⟨24183575022153366053270243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16122383348102244035513495 24183575022153366053270243)
                  ·
                    refine ⟨36275362533230049079905365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24183575022153366053270243 36275362533230049079905365)
                    ·
                      refine ⟨425101904686289637655141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36275362533230049079905365 425101904686289637655141)
                      ·
                        rfl

theorem cell23_827883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_827883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827883 prefixEnd_827883 := by exact prefixLift 827883
  have htrace : WordTrace (prefixWord ++ tailWord_827883) baseStart_827883 baseEnd_827883 := by
    simpa [prefixWord, tailWord_827883, baseEnd_827883] using wordTrace_append hprefix tailTrace_827883
  have hstable : (prefixWord ++ tailWord_827883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827883).length < 2 ^ (prefixWord ++ tailWord_827883).sum := by decide
  have hdescent : baseEnd_827883 < baseStart_827883 := by decide
  rcases family_descends (prefixWord ++ tailWord_827883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827907 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 3]
def baseStart_827907 : Nat := 118140960795 + 827907 * 2 ^ 59
def prefixEnd_827907 : Nat := 4983230072969 + 3 ^ 40 * 827907 * 2
def baseEnd_827907 : Nat := 425114228221997543755031

theorem tailTrace_827907 : CollatzResearch.WordTrace tailWord_827907 prefixEnd_827907 425114228221997543755031 := by
  unfold tailWord_827907
  simp only [CollatzResearch.WordTrace]
  refine ⟨30196249011641809103657975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20130832674427872735771983 30196249011641809103657975)
  ·
    refine ⟨45294373517462713655486963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30196249011641809103657975 45294373517462713655486963)
    ·
      refine ⟨67941560276194070483230445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45294373517462713655486963 67941560276194070483230445)
      ·
        refine ⟨25478085103572776431211417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67941560276194070483230445 25478085103572776431211417)
        ·
          refine ⟨19108563827679582323408563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25478085103572776431211417 19108563827679582323408563)
          ·
            refine ⟨28662845741519373485112845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19108563827679582323408563 28662845741519373485112845)
            ·
              refine ⟨10748567153069765056917317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28662845741519373485112845 10748567153069765056917317)
              ·
                refine ⟨2015356341200580948171997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10748567153069765056917317 2015356341200580948171997)
                ·
                  refine ⟨755758627950217855564499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2015356341200580948171997 755758627950217855564499)
                  ·
                    refine ⟨1133637941925326783346749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 755758627950217855564499 1133637941925326783346749)
                    ·
                      refine ⟨425114228221997543755031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1133637941925326783346749 425114228221997543755031)
                      ·
                        rfl

theorem cell23_827907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_827907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827907 prefixEnd_827907 := by exact prefixLift 827907
  have htrace : WordTrace (prefixWord ++ tailWord_827907) baseStart_827907 baseEnd_827907 := by
    simpa [prefixWord, tailWord_827907, baseEnd_827907] using wordTrace_append hprefix tailTrace_827907
  have hstable : (prefixWord ++ tailWord_827907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827907).length < 2 ^ (prefixWord ++ tailWord_827907).sum := by decide
  have hdescent : baseEnd_827907 < baseStart_827907 := by decide
  rcases family_descends (prefixWord ++ tailWord_827907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827960 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_827960 : Nat := 118140960795 + 827960 * 2 ^ 59
def prefixEnd_827960 : Nat := 4983230072969 + 3 ^ 40 * 827960 * 2
def baseEnd_827960 : Nat := 425141442696685836392287

theorem tailTrace_827960 : CollatzResearch.WordTrace tailWord_827960 prefixEnd_827960 425141442696685836392287 := by
  unfold tailWord_827960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099091040224899577668667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20132121386966532770224889 15099091040224899577668667)
  ·
    refine ⟨22648636560337349366503001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15099091040224899577668667 22648636560337349366503001)
    ·
      refine ⟨16986477420253012024877251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22648636560337349366503001 16986477420253012024877251)
      ·
        refine ⟨25479716130379518037315877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16986477420253012024877251 25479716130379518037315877)
        ·
          refine ⟨4777446774446159631996727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25479716130379518037315877 4777446774446159631996727)
          ·
            refine ⟨7166170161669239447995091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777446774446159631996727 7166170161669239447995091)
            ·
              refine ⟨10749255242503859171992637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166170161669239447995091 10749255242503859171992637)
              ·
                refine ⟨4030970715938947189497239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10749255242503859171992637 4030970715938947189497239)
                ·
                  refine ⟨6046456073908420784245859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030970715938947189497239 6046456073908420784245859)
                  ·
                    refine ⟨9069684110862631176368789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6046456073908420784245859 9069684110862631176368789)
                    ·
                      refine ⟨425141442696685836392287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9069684110862631176368789 425141442696685836392287)
                      ·
                        rfl

theorem cell23_827960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_827960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827960 prefixEnd_827960 := by exact prefixLift 827960
  have htrace : WordTrace (prefixWord ++ tailWord_827960) baseStart_827960 baseEnd_827960 := by
    simpa [prefixWord, tailWord_827960, baseEnd_827960] using wordTrace_append hprefix tailTrace_827960
  have hstable : (prefixWord ++ tailWord_827960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827960).length < 2 ^ (prefixWord ++ tailWord_827960).sum := by decide
  have hdescent : baseEnd_827960 < baseStart_827960 := by decide
  rcases family_descends (prefixWord ++ tailWord_827960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827964 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_827964 : Nat := 118140960795 + 827964 * 2 ^ 59
def prefixEnd_827964 : Nat := 4983230072969 + 3 ^ 40 * 827964 * 2
def baseEnd_827964 : Nat := 425143496619303820742269

theorem tailTrace_827964 : CollatzResearch.WordTrace tailWord_827964 prefixEnd_827964 425143496619303820742269 := by
  unfold tailWord_827964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099163986217653919241473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20132218648290205225655297 15099163986217653919241473)
  ·
    refine ⟨11324372989663240439431105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15099163986217653919241473 11324372989663240439431105)
    ·
      refine ⟨8493279742247430329573329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11324372989663240439431105 8493279742247430329573329)
      ·
        refine ⟨6369959806685572747179997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8493279742247430329573329 6369959806685572747179997)
        ·
          refine ⟨2388734927507089780192499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6369959806685572747179997 2388734927507089780192499)
          ·
            refine ⟨3583102391260634670288749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388734927507089780192499 3583102391260634670288749)
            ·
              refine ⟨1343663396722738001358281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3583102391260634670288749 1343663396722738001358281)
              ·
                refine ⟨1007747547542053501018711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1343663396722738001358281 1007747547542053501018711)
                ·
                  refine ⟨1511621321313080251528067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007747547542053501018711 1511621321313080251528067)
                  ·
                    refine ⟨2267431981969620377292101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511621321313080251528067 2267431981969620377292101)
                    ·
                      refine ⟨425143496619303820742269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2267431981969620377292101 425143496619303820742269)
                      ·
                        rfl

theorem cell23_827964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_827964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827964 prefixEnd_827964 := by exact prefixLift 827964
  have htrace : WordTrace (prefixWord ++ tailWord_827964) baseStart_827964 baseEnd_827964 := by
    simpa [prefixWord, tailWord_827964, baseEnd_827964] using wordTrace_append hprefix tailTrace_827964
  have hstable : (prefixWord ++ tailWord_827964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827964).length < 2 ^ (prefixWord ++ tailWord_827964).sum := by decide
  have hdescent : baseEnd_827964 < baseStart_827964 := by decide
  rcases family_descends (prefixWord ++ tailWord_827964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827967 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_827967 : Nat := 118140960795 + 827967 * 2 ^ 59
def prefixEnd_827967 : Nat := 4983230072969 + 3 ^ 40 * 827967 * 2
def baseEnd_827967 : Nat := 425145037061267309004755

theorem tailTrace_827967 : CollatzResearch.WordTrace tailWord_827967 prefixEnd_827967 425145037061267309004755 := by
  unfold tailWord_827967
  simp only [CollatzResearch.WordTrace]
  refine ⟨30198437391424439350842155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20132291594282959567228103 30198437391424439350842155)
  ·
    refine ⟨45297656087136659026263233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30198437391424439350842155 45297656087136659026263233)
    ·
      refine ⟨33973242065352494269697425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45297656087136659026263233 33973242065352494269697425)
      ·
        refine ⟨25479931549014370702273069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33973242065352494269697425 25479931549014370702273069)
        ·
          refine ⟨9554974330880389013352401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25479931549014370702273069 9554974330880389013352401)
          ·
            refine ⟨7166230748160291760014301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9554974330880389013352401 7166230748160291760014301)
            ·
              refine ⟨2687336530560109410005363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7166230748160291760014301 2687336530560109410005363)
              ·
                refine ⟨4031004795840164115008045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687336530560109410005363 4031004795840164115008045)
                ·
                  refine ⟨1511626798440061543128017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4031004795840164115008045 1511626798440061543128017)
                  ·
                    refine ⟨1133720098830046157346013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511626798440061543128017 1133720098830046157346013)
                    ·
                      refine ⟨425145037061267309004755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1133720098830046157346013 425145037061267309004755)
                      ·
                        rfl

theorem cell23_827967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_827967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827967 prefixEnd_827967 := by exact prefixLift 827967
  have htrace : WordTrace (prefixWord ++ tailWord_827967) baseStart_827967 baseEnd_827967 := by
    simpa [prefixWord, tailWord_827967, baseEnd_827967] using wordTrace_append hprefix tailTrace_827967
  have hstable : (prefixWord ++ tailWord_827967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827967).length < 2 ^ (prefixWord ++ tailWord_827967).sum := by decide
  have hdescent : baseEnd_827967 < baseStart_827967 := by decide
  rcases family_descends (prefixWord ++ tailWord_827967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827974 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_827974 : Nat := 118140960795 + 827974 * 2 ^ 59
def prefixEnd_827974 : Nat := 4983230072969 + 3 ^ 40 * 827974 * 2
def baseEnd_827974 : Nat := 141716210475282927205741

theorem tailTrace_827974 : CollatzResearch.WordTrace tailWord_827974 prefixEnd_827974 141716210475282927205741 := by
  unfold tailWord_827974
  simp only [CollatzResearch.WordTrace]
  refine ⟨943709146949971235823343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20132461801599386364231317 943709146949971235823343)
  ·
    refine ⟨1415563720424956853735015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 943709146949971235823343 1415563720424956853735015)
    ·
      refine ⟨2123345580637435280602523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415563720424956853735015 2123345580637435280602523)
      ·
        refine ⟨3185018370956152920903785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123345580637435280602523 3185018370956152920903785)
        ·
          refine ⟨2388763778217114690677839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185018370956152920903785 2388763778217114690677839)
          ·
            refine ⟨3583145667325672036016759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388763778217114690677839 3583145667325672036016759)
            ·
              refine ⟨5374718500988508054025139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583145667325672036016759 5374718500988508054025139)
              ·
                refine ⟨8062077751482762081037709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374718500988508054025139 8062077751482762081037709)
                ·
                  refine ⟨3023279156806035780389141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8062077751482762081037709 3023279156806035780389141)
                  ·
                    refine ⟨141716210475282927205741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3023279156806035780389141 141716210475282927205741)
                    ·
                      rfl

theorem cell23_827974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_827974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_827974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_827974 prefixEnd_827974 := by exact prefixLift 827974
  have htrace : WordTrace (prefixWord ++ tailWord_827974) baseStart_827974 baseEnd_827974 := by
    simpa [prefixWord, tailWord_827974, baseEnd_827974] using wordTrace_append hprefix tailTrace_827974
  have hstable : (prefixWord ++ tailWord_827974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827974).length < 2 ^ (prefixWord ++ tailWord_827974).sum := by decide
  have hdescent : baseEnd_827974 < baseStart_827974 := by decide
  rcases family_descends (prefixWord ++ tailWord_827974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828000 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_828000 : Nat := 118140960795 + 828000 * 2 ^ 59
def prefixEnd_828000 : Nat := 4983230072969 + 3 ^ 40 * 828000 * 2
def baseEnd_828000 : Nat := 141720660640955226630701

theorem tailTrace_828000 : CollatzResearch.WordTrace tailWord_828000 prefixEnd_828000 141720660640955226630701 := by
  unfold tailWord_828000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099820500152442993396727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20133094000203257324528969 15099820500152442993396727)
  ·
    refine ⟨22649730750228664490095091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15099820500152442993396727 22649730750228664490095091)
    ·
      refine ⟨33974596125342996735142637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22649730750228664490095091 33974596125342996735142637)
      ·
        refine ⟨12740473547003623775678489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33974596125342996735142637 12740473547003623775678489)
        ·
          refine ⟨9555355160252717831758867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12740473547003623775678489 9555355160252717831758867)
          ·
            refine ⟨14333032740379076747638301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9555355160252717831758867 14333032740379076747638301)
            ·
              refine ⟨5374887277642153780364363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14333032740379076747638301 5374887277642153780364363)
              ·
                refine ⟨8062330916463230670546545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374887277642153780364363 8062330916463230670546545)
                ·
                  refine ⟨6046748187347423002909909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8062330916463230670546545 6046748187347423002909909)
                  ·
                    refine ⟨141720660640955226630701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6046748187347423002909909 141720660640955226630701)
                    ·
                      rfl

theorem cell23_828000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_828000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828000 prefixEnd_828000 := by exact prefixLift 828000
  have htrace : WordTrace (prefixWord ++ tailWord_828000) baseStart_828000 baseEnd_828000 := by
    simpa [prefixWord, tailWord_828000, baseEnd_828000] using wordTrace_append hprefix tailTrace_828000
  have hstable : (prefixWord ++ tailWord_828000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828000).length < 2 ^ (prefixWord ++ tailWord_828000).sum := by decide
  have hdescent : baseEnd_828000 < baseStart_828000 := by decide
  rcases family_descends (prefixWord ++ tailWord_828000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828014 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_828014 : Nat := 118140960795 + 828014 * 2 ^ 59
def prefixEnd_828014 : Nat := 4983230072969 + 3 ^ 40 * 828014 * 2
def baseEnd_828014 : Nat := 425169170652028625117039

theorem tailTrace_828014 : CollatzResearch.WordTrace tailWord_828014 prefixEnd_828014 425169170652028625117039 := by
  unfold tailWord_828014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775018952781770797225387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20133434414836110918535397 3775018952781770797225387)
  ·
    refine ⟨5662528429172656195838081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775018952781770797225387 5662528429172656195838081)
    ·
      refine ⟨4246896321879492146878561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5662528429172656195838081 4246896321879492146878561)
      ·
        refine ⟨3185172241409619110158921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4246896321879492146878561 3185172241409619110158921)
        ·
          refine ⟨2388879181057214332619191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185172241409619110158921 2388879181057214332619191)
          ·
            refine ⟨3583318771585821498928787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388879181057214332619191 3583318771585821498928787)
            ·
              refine ⟨5374978157378732248393181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583318771585821498928787 5374978157378732248393181)
              ·
                refine ⟨2015616809017024593147443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5374978157378732248393181 2015616809017024593147443)
                ·
                  refine ⟨3023425213525536889721165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015616809017024593147443 3023425213525536889721165)
                  ·
                    refine ⟨1133784455072076333645437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023425213525536889721165 1133784455072076333645437)
                    ·
                      refine ⟨425169170652028625117039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1133784455072076333645437 425169170652028625117039)
                      ·
                        rfl

theorem cell23_828014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_828014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828014 prefixEnd_828014 := by exact prefixLift 828014
  have htrace : WordTrace (prefixWord ++ tailWord_828014) baseStart_828014 baseEnd_828014 := by
    simpa [prefixWord, tailWord_828014, baseEnd_828014] using wordTrace_append hprefix tailTrace_828014
  have hstable : (prefixWord ++ tailWord_828014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828014).length < 2 ^ (prefixWord ++ tailWord_828014).sum := by decide
  have hdescent : baseEnd_828014 < baseStart_828014 := by decide
  rcases family_descends (prefixWord ++ tailWord_828014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828144 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_828144 : Nat := 118140960795 + 828144 * 2 ^ 59
def prefixEnd_828144 : Nat := 4983230072969 + 3 ^ 40 * 828144 * 2
def baseEnd_828144 : Nat := 425235923137113116491441

theorem tailTrace_828144 : CollatzResearch.WordTrace tailWord_828144 prefixEnd_828144 425235923137113116491441 := by
  unfold tailWord_828144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15102446555891599290017743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20136595407855465720023657 15102446555891599290017743)
  ·
    refine ⟨22653669833837398935026615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15102446555891599290017743 22653669833837398935026615)
    ·
      refine ⟨33980504750756098402539923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22653669833837398935026615 33980504750756098402539923)
      ·
        refine ⟨50970757126134147603809885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33980504750756098402539923 50970757126134147603809885)
        ·
          refine ⟨19114033922300305351428707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50970757126134147603809885 19114033922300305351428707)
          ·
            refine ⟨28671050883450458027143061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19114033922300305351428707 28671050883450458027143061)
            ·
              refine ⟨1343955510161740220022331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28671050883450458027143061 1343955510161740220022331)
              ·
                refine ⟨2015933265242610330033497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343955510161740220022331 2015933265242610330033497)
                ·
                  refine ⟨1511949948931957747525123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2015933265242610330033497 1511949948931957747525123)
                  ·
                    refine ⟨2267924923397936621287685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511949948931957747525123 2267924923397936621287685)
                    ·
                      refine ⟨425235923137113116491441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2267924923397936621287685 425235923137113116491441)
                      ·
                        rfl

theorem cell23_828144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_828144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828144 prefixEnd_828144 := by exact prefixLift 828144
  have htrace : WordTrace (prefixWord ++ tailWord_828144) baseStart_828144 baseEnd_828144 := by
    simpa [prefixWord, tailWord_828144, baseEnd_828144] using wordTrace_append hprefix tailTrace_828144
  have hstable : (prefixWord ++ tailWord_828144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828144).length < 2 ^ (prefixWord ++ tailWord_828144).sum := by decide
  have hdescent : baseEnd_828144 < baseStart_828144 := by decide
  rcases family_descends (prefixWord ++ tailWord_828144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828157 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_828157 : Nat := 118140960795 + 828157 * 2 ^ 59
def prefixEnd_828157 : Nat := 4983230072969 + 3 ^ 40 * 828157 * 2
def baseEnd_828157 : Nat := 425242598385621565628881

theorem tailTrace_828157 : CollatzResearch.WordTrace tailWord_828157 prefixEnd_828157 425242598385621565628881 := by
  unfold tailWord_828157
  simp only [CollatzResearch.WordTrace]
  refine ⟨30205367260736101800258725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20136911507157401200172483 30205367260736101800258725)
  ·
    refine ⟨5663506361388019087548511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30205367260736101800258725 5663506361388019087548511)
    ·
      refine ⟨8495259542082028631322767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5663506361388019087548511 8495259542082028631322767)
      ·
        refine ⟨12742889313123042946984151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8495259542082028631322767 12742889313123042946984151)
        ·
          refine ⟨19114333969684564420476227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12742889313123042946984151 19114333969684564420476227)
          ·
            refine ⟨28671500954526846630714341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19114333969684564420476227 28671500954526846630714341)
            ·
              refine ⟨5375906428973783743258939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28671500954526846630714341 5375906428973783743258939)
              ·
                refine ⟨8063859643460675614888409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375906428973783743258939 8063859643460675614888409)
                ·
                  refine ⟨6047894732595506711166307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8063859643460675614888409 6047894732595506711166307)
                  ·
                    refine ⟨9071842098893260066749461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6047894732595506711166307 9071842098893260066749461)
                    ·
                      refine ⟨425242598385621565628881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9071842098893260066749461 425242598385621565628881)
                      ·
                        rfl

theorem cell23_828157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_828157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828157 prefixEnd_828157 := by exact prefixLift 828157
  have htrace : WordTrace (prefixWord ++ tailWord_828157) baseStart_828157 baseEnd_828157 := by
    simpa [prefixWord, tailWord_828157, baseEnd_828157] using wordTrace_append hprefix tailTrace_828157
  have hstable : (prefixWord ++ tailWord_828157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828157).length < 2 ^ (prefixWord ++ tailWord_828157).sum := by decide
  have hdescent : baseEnd_828157 < baseStart_828157 := by decide
  rcases family_descends (prefixWord ++ tailWord_828157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828218 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_828218 : Nat := 118140960795 + 828218 * 2 ^ 59
def prefixEnd_828218 : Nat := 4983230072969 + 3 ^ 40 * 828218 * 2
def baseEnd_828218 : Nat := 47252657856171758551789

theorem tailTrace_828218 : CollatzResearch.WordTrace tailWord_828218 prefixEnd_828218 47252657856171758551789 := by
  unfold tailWord_828218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7551898028378777304557327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20138394742343406145486205 7551898028378777304557327)
  ·
    refine ⟨11327847042568165956835991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7551898028378777304557327 11327847042568165956835991)
    ·
      refine ⟨16991770563852248935253987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11327847042568165956835991 16991770563852248935253987)
      ·
        refine ⟨25487655845778373402880981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16991770563852248935253987 25487655845778373402880981)
        ·
          refine ⟨597366933885430626630023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25487655845778373402880981 597366933885430626630023)
          ·
            refine ⟨896050400828145939945035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597366933885430626630023 896050400828145939945035)
            ·
              refine ⟨1344075601242218909917553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896050400828145939945035 1344075601242218909917553)
              ·
                refine ⟨1008056700931664182438165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344075601242218909917553 1008056700931664182438165)
                ·
                  refine ⟨47252657856171758551789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1008056700931664182438165 47252657856171758551789)
                  ·
                    rfl

theorem cell23_828218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_828218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828218 prefixEnd_828218 := by exact prefixLift 828218
  have htrace : WordTrace (prefixWord ++ tailWord_828218) baseStart_828218 baseEnd_828218 := by
    simpa [prefixWord, tailWord_828218, baseEnd_828218] using wordTrace_append hprefix tailTrace_828218
  have hstable : (prefixWord ++ tailWord_828218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828218).length < 2 ^ (prefixWord ++ tailWord_828218).sum := by decide
  have hdescent : baseEnd_828218 < baseStart_828218 := by decide
  rcases family_descends (prefixWord ++ tailWord_828218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828234 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_828234 : Nat := 118140960795 + 828234 * 2 ^ 59
def prefixEnd_828234 : Nat := 4983230072969 + 3 ^ 40 * 828234 * 2
def baseEnd_828234 : Nat := 425282136396017764366027

theorem tailTrace_828234 : CollatzResearch.WordTrace tailWord_828234 prefixEnd_828234 425282136396017764366027 := by
  unfold tailWord_828234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7552043920364285987702939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20138783787638095967207837 7552043920364285987702939)
  ·
    refine ⟨11328065880546428981554409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7552043920364285987702939 11328065880546428981554409)
    ·
      refine ⟨8496049410409821736165807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11328065880546428981554409 8496049410409821736165807)
      ·
        refine ⟨12744074115614732604248711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8496049410409821736165807 12744074115614732604248711)
        ·
          refine ⟨19116111173422098906373067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12744074115614732604248711 19116111173422098906373067)
          ·
            refine ⟨28674166760133148359559601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19116111173422098906373067 28674166760133148359559601)
            ·
              refine ⟨21505625070099861269669701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28674166760133148359559601 21505625070099861269669701)
              ·
                refine ⟨4032304700643723988063069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21505625070099861269669701 4032304700643723988063069)
                ·
                  refine ⟨1512114262741396495523651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4032304700643723988063069 1512114262741396495523651)
                  ·
                    refine ⟨2268171394112094743285477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1512114262741396495523651 2268171394112094743285477)
                    ·
                      refine ⟨425282136396017764366027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2268171394112094743285477 425282136396017764366027)
                      ·
                        rfl

theorem cell23_828234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_828234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828234 prefixEnd_828234 := by exact prefixLift 828234
  have htrace : WordTrace (prefixWord ++ tailWord_828234) baseStart_828234 baseEnd_828234 := by
    simpa [prefixWord, tailWord_828234, baseEnd_828234] using wordTrace_append hprefix tailTrace_828234
  have hstable : (prefixWord ++ tailWord_828234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828234).length < 2 ^ (prefixWord ++ tailWord_828234).sum := by decide
  have hdescent : baseEnd_828234 < baseStart_828234 := by decide
  rcases family_descends (prefixWord ++ tailWord_828234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828251 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 11, 2, 2]
def baseStart_828251 : Nat := 118140960795 + 828251 * 2 ^ 59
def prefixEnd_828251 : Nat := 4983230072969 + 3 ^ 40 * 828251 * 2
def baseEnd_828251 : Nat := 425290865567144197853449

theorem tailTrace_828251 : CollatzResearch.WordTrace tailWord_828251 prefixEnd_828251 425290865567144197853449 := by
  unfold tailWord_828251
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208795722395555854180607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20139197148263703902787071 30208795722395555854180607)
  ·
    refine ⟨45313193583593333781270911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30208795722395555854180607 45313193583593333781270911)
    ·
      refine ⟨67969790375390000671906367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45313193583593333781270911 67969790375390000671906367)
      ·
        refine ⟨101954685563085001007859551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67969790375390000671906367 101954685563085001007859551)
        ·
          refine ⟨152932028344627501511789327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101954685563085001007859551 152932028344627501511789327)
          ·
            refine ⟨229398042516941252267683991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152932028344627501511789327 229398042516941252267683991)
            ·
              refine ⟨344097063775411878401525987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229398042516941252267683991 344097063775411878401525987)
              ·
                refine ⟨516145595663117817602288981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344097063775411878401525987 516145595663117817602288981)
                ·
                  refine ⟨756072649897145240628353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 516145595663117817602288981 756072649897145240628353)
                  ·
                    refine ⟨567054487422858930471265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756072649897145240628353 567054487422858930471265)
                    ·
                      refine ⟨425290865567144197853449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567054487422858930471265 425290865567144197853449)
                      ·
                        rfl

theorem cell23_828251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 2, 2].length) (baseStart_828251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828251 prefixEnd_828251 := by exact prefixLift 828251
  have htrace : WordTrace (prefixWord ++ tailWord_828251) baseStart_828251 baseEnd_828251 := by
    simpa [prefixWord, tailWord_828251, baseEnd_828251] using wordTrace_append hprefix tailTrace_828251
  have hstable : (prefixWord ++ tailWord_828251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828251).length < 2 ^ (prefixWord ++ tailWord_828251).sum := by decide
  have hdescent : baseEnd_828251 < baseStart_828251 := by decide
  rcases family_descends (prefixWord ++ tailWord_828251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828278 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_828278 : Nat := 118140960795 + 828278 * 2 ^ 59
def prefixEnd_828278 : Nat := 4983230072969 + 3 ^ 40 * 828278 * 2
def baseEnd_828278 : Nat := 141768243181605197405275

theorem tailTrace_828278 : CollatzResearch.WordTrace tailWord_828278 prefixEnd_828278 141768243181605197405275 := by
  unfold tailWord_828278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888111280831108716588343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20139853662198492976942325 1888111280831108716588343)
  ·
    refine ⟨2832166921246663074882515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888111280831108716588343 2832166921246663074882515)
    ·
      refine ⟨4248250381869994612323773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832166921246663074882515 4248250381869994612323773)
      ·
        refine ⟨1593093893201247979621415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4248250381869994612323773 1593093893201247979621415)
        ·
          refine ⟨2389640839801871969432123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593093893201247979621415 2389640839801871969432123)
          ·
            refine ⟨3584461259702807954148185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389640839801871969432123 3584461259702807954148185)
            ·
              refine ⟨2688345944777105965611139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584461259702807954148185 2688345944777105965611139)
              ·
                refine ⟨4032518917165658948416709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688345944777105965611139 4032518917165658948416709)
                ·
                  refine ⟨756097296968561052828133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4032518917165658948416709 756097296968561052828133)
                  ·
                    refine ⟨141768243181605197405275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756097296968561052828133 141768243181605197405275)
                    ·
                      rfl

theorem cell23_828278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_828278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828278 prefixEnd_828278 := by exact prefixLift 828278
  have htrace : WordTrace (prefixWord ++ tailWord_828278) baseStart_828278 baseEnd_828278 := by
    simpa [prefixWord, tailWord_828278, baseEnd_828278] using wordTrace_append hprefix tailTrace_828278
  have hstable : (prefixWord ++ tailWord_828278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828278).length < 2 ^ (prefixWord ++ tailWord_828278).sum := by decide
  have hdescent : baseEnd_828278 < baseStart_828278 := by decide
  rcases family_descends (prefixWord ++ tailWord_828278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828285 : List Nat := [1, 4, 1, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_828285 : Nat := 118140960795 + 828285 * 2 ^ 59
def prefixEnd_828285 : Nat := 4983230072969 + 3 ^ 40 * 828285 * 2
def baseEnd_828285 : Nat := 425308323909397064828293

theorem tailTrace_828285 : CollatzResearch.WordTrace tailWord_828285 prefixEnd_828285 425308323909397064828293 := by
  unfold tailWord_828285
  simp only [CollatzResearch.WordTrace]
  refine ⟨30210035804272379660918309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20140023869514919773945539 30210035804272379660918309)
  ·
    refine ⟨5664381713301071186422183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30210035804272379660918309 5664381713301071186422183)
    ·
      refine ⟨8496572569951606779633275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5664381713301071186422183 8496572569951606779633275)
      ·
        refine ⟨12744858854927410169449913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8496572569951606779633275 12744858854927410169449913)
        ·
          refine ⟨9558644141195557627087435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12744858854927410169449913 9558644141195557627087435)
          ·
            refine ⟨14337966211793336440631153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558644141195557627087435 14337966211793336440631153)
            ·
              refine ⟨10753474658845002330473365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14337966211793336440631153 10753474658845002330473365)
              ·
                refine ⟨504069124633359484240939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10753474658845002330473365 504069124633359484240939)
                ·
                  refine ⟨756103686950039226361409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504069124633359484240939 756103686950039226361409)
                  ·
                    refine ⟨567077765212529419771057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756103686950039226361409 567077765212529419771057)
                    ·
                      refine ⟨425308323909397064828293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567077765212529419771057 425308323909397064828293)
                      ·
                        rfl

theorem cell23_828285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_828285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828285 prefixEnd_828285 := by exact prefixLift 828285
  have htrace : WordTrace (prefixWord ++ tailWord_828285) baseStart_828285 baseEnd_828285 := by
    simpa [prefixWord, tailWord_828285, baseEnd_828285] using wordTrace_append hprefix tailTrace_828285
  have hstable : (prefixWord ++ tailWord_828285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828285).length < 2 ^ (prefixWord ++ tailWord_828285).sum := by decide
  have hdescent : baseEnd_828285 < baseStart_828285 := by decide
  rcases family_descends (prefixWord ++ tailWord_828285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828295 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 2, 4]
def baseStart_828295 : Nat := 118140960795 + 828295 * 2 ^ 59
def prefixEnd_828295 : Nat := 4983230072969 + 3 ^ 40 * 828295 * 2
def baseEnd_828295 : Nat := 141771152905314008567749

theorem tailTrace_828295 : CollatzResearch.WordTrace tailWord_828295 prefixEnd_828295 141771152905314008567749 := by
  unfold tailWord_828295
  simp only [CollatzResearch.WordTrace]
  refine ⟨30210400534236151368782339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20140267022824100912521559 30210400534236151368782339)
  ·
    refine ⟨45315600801354227053173509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30210400534236151368782339 45315600801354227053173509)
    ·
      refine ⟨8496675150253917572470033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45315600801354227053173509 8496675150253917572470033)
      ·
        refine ⟨6372506362690438179352525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8496675150253917572470033 6372506362690438179352525)
        ·
          refine ⟨2389689886008914317257197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6372506362690438179352525 2389689886008914317257197)
          ·
            refine ⟨896133707253342868971449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2389689886008914317257197 896133707253342868971449)
            ·
              refine ⟨672100280440007151728587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896133707253342868971449 672100280440007151728587)
              ·
                refine ⟨1008150420660010727592881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672100280440007151728587 1008150420660010727592881)
                ·
                  refine ⟨756112815495008045694661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1008150420660010727592881 756112815495008045694661)
                  ·
                    refine ⟨141771152905314008567749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756112815495008045694661 141771152905314008567749)
                    ·
                      rfl

theorem cell23_828295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_828295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828295 prefixEnd_828295 := by exact prefixLift 828295
  have htrace : WordTrace (prefixWord ++ tailWord_828295) baseStart_828295 baseEnd_828295 := by
    simpa [prefixWord, tailWord_828295, baseEnd_828295] using wordTrace_append hprefix tailTrace_828295
  have hstable : (prefixWord ++ tailWord_828295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828295).length < 2 ^ (prefixWord ++ tailWord_828295).sum := by decide
  have hdescent : baseEnd_828295 < baseStart_828295 := by decide
  rcases family_descends (prefixWord ++ tailWord_828295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828342 : List Nat := [5, 1, 4, 1, 1, 2, 1, 8]
def baseStart_828342 : Nat := 118140960795 + 828342 * 2 ^ 59
def prefixEnd_828342 : Nat := 4983230072969 + 3 ^ 40 * 828342 * 2
def baseEnd_828342 : Nat := 15753244159507531178353

theorem tailTrace_828342 : CollatzResearch.WordTrace tailWord_828342 prefixEnd_828342 15753244159507531178353 := by
  unfold tailWord_828342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888257172816617399733955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20141409843377252263828853 1888257172816617399733955)
  ·
    refine ⟨2832385759224926099600933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888257172816617399733955 2832385759224926099600933)
    ·
      refine ⟨531072329854673643675175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2832385759224926099600933 531072329854673643675175)
      ·
        refine ⟨796608494782010465512763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531072329854673643675175 796608494782010465512763)
        ·
          refine ⟨1194912742173015698269145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796608494782010465512763 1194912742173015698269145)
          ·
            refine ⟨896184556629761773701859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194912742173015698269145 896184556629761773701859)
            ·
              refine ⟨1344276834944642660552789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896184556629761773701859 1344276834944642660552789)
              ·
                refine ⟨15753244159507531178353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1344276834944642660552789 15753244159507531178353)
                ·
                  rfl

theorem cell23_828342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_828342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828342 prefixEnd_828342 := by exact prefixLift 828342
  have htrace : WordTrace (prefixWord ++ tailWord_828342) baseStart_828342 baseEnd_828342 := by
    simpa [prefixWord, tailWord_828342, baseEnd_828342] using wordTrace_append hprefix tailTrace_828342
  have hstable : (prefixWord ++ tailWord_828342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828342).length < 2 ^ (prefixWord ++ tailWord_828342).sum := by decide
  have hdescent : baseEnd_828342 < baseStart_828342 := by decide
  rcases family_descends (prefixWord ++ tailWord_828342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828398 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_828398 : Nat := 118140960795 + 828398 * 2 ^ 59
def prefixEnd_828398 : Nat := 4983230072969 + 3 ^ 40 * 828398 * 2
def baseEnd_828398 : Nat := 47262927469261680301697

theorem tailTrace_828398 : CollatzResearch.WordTrace tailWord_828398 prefixEnd_828398 47262927469261680301697 := by
  unfold tailWord_828398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776769656607874994972731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20142771501908666639854565 3776769656607874994972731)
  ·
    refine ⟨5665154484911812492459097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3776769656607874994972731 5665154484911812492459097)
    ·
      refine ⟨4248865863683859369344323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5665154484911812492459097 4248865863683859369344323)
      ·
        refine ⟨6373298795525789054016485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248865863683859369344323 6373298795525789054016485)
        ·
          refine ⟨1194993524161085447628091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6373298795525789054016485 1194993524161085447628091)
          ·
            refine ⟨1792490286241628171442137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194993524161085447628091 1792490286241628171442137)
            ·
              refine ⟨1344367714681221128581603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792490286241628171442137 1344367714681221128581603)
              ·
                refine ⟨2016551572021831692872405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344367714681221128581603 2016551572021831692872405)
                ·
                  refine ⟨47262927469261680301697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2016551572021831692872405 47262927469261680301697)
                  ·
                    rfl

theorem cell23_828398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_828398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828398 prefixEnd_828398 := by exact prefixLift 828398
  have htrace : WordTrace (prefixWord ++ tailWord_828398) baseStart_828398 baseEnd_828398 := by
    simpa [prefixWord, tailWord_828398, baseEnd_828398] using wordTrace_append hprefix tailTrace_828398
  have hstable : (prefixWord ++ tailWord_828398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828398).length < 2 ^ (prefixWord ++ tailWord_828398).sum := by decide
  have hdescent : baseEnd_828398 < baseStart_828398 := by decide
  rcases family_descends (prefixWord ++ tailWord_828398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828441 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 5, 4]
def baseStart_828441 : Nat := 118140960795 + 828441 * 2 ^ 59
def prefixEnd_828441 : Nat := 4983230072969 + 3 ^ 40 * 828441 * 2
def baseEnd_828441 : Nat := 141796142297166151492525

theorem tailTrace_828441 : CollatzResearch.WordTrace tailWord_828441 prefixEnd_828441 141796142297166151492525 := by
  unfold tailWord_828441
  simp only [CollatzResearch.WordTrace]
  refine ⟨30215725591707218303597177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20143817061138145535731451 30215725591707218303597177)
  ·
    refine ⟨22661794193780413727697883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30215725591707218303597177 22661794193780413727697883)
    ·
      refine ⟨33992691290670620591546825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22661794193780413727697883 33992691290670620591546825)
      ·
        refine ⟨25494518468002965443660119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33992691290670620591546825 25494518468002965443660119)
        ·
          refine ⟨38241777702004448165490179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25494518468002965443660119 38241777702004448165490179)
          ·
            refine ⟨57362666553006672248235269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38241777702004448165490179 57362666553006672248235269)
            ·
              refine ⟨10755499978688751046544113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57362666553006672248235269 10755499978688751046544113)
              ·
                refine ⟨8066624984016563284908085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10755499978688751046544113 8066624984016563284908085)
                ·
                  refine ⟨756246092251552807960133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8066624984016563284908085 756246092251552807960133)
                  ·
                    refine ⟨141796142297166151492525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756246092251552807960133 141796142297166151492525)
                    ·
                      rfl

theorem cell23_828441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 4].length) (baseStart_828441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828441 prefixEnd_828441 := by exact prefixLift 828441
  have htrace : WordTrace (prefixWord ++ tailWord_828441) baseStart_828441 baseEnd_828441 := by
    simpa [prefixWord, tailWord_828441, baseEnd_828441] using wordTrace_append hprefix tailTrace_828441
  have hstable : (prefixWord ++ tailWord_828441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828441).length < 2 ^ (prefixWord ++ tailWord_828441).sum := by decide
  have hdescent : baseEnd_828441 < baseStart_828441 := by decide
  rcases family_descends (prefixWord ++ tailWord_828441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828509 : List Nat := [1, 4, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_828509 : Nat := 118140960795 + 828509 * 2 ^ 59
def prefixEnd_828509 : Nat := 4983230072969 + 3 ^ 40 * 828509 * 2
def baseEnd_828509 : Nat := 141807781192001396142421

theorem tailTrace_828509 : CollatzResearch.WordTrace tailWord_828509 prefixEnd_828509 141807781192001396142421 := by
  unfold tailWord_828509
  simp only [CollatzResearch.WordTrace]
  refine ⟨30218205755460865917072581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20145470503640577278048387 30218205755460865917072581)
  ·
    refine ⟨5665913579148912359451109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30218205755460865917072581 5665913579148912359451109)
    ·
      refine ⟨1062358796090421067397083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5665913579148912359451109 1062358796090421067397083)
      ·
        refine ⟨1593538194135631601095625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062358796090421067397083 1593538194135631601095625)
        ·
          refine ⟨1195153645601723700821719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1593538194135631601095625 1195153645601723700821719)
          ·
            refine ⟨1792730468402585551232579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195153645601723700821719 1792730468402585551232579)
            ·
              refine ⟨2689095702603878326848869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792730468402585551232579 2689095702603878326848869)
              ·
                refine ⟨504205444238227186284163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2689095702603878326848869 504205444238227186284163)
                ·
                  refine ⟨756308166357340779426245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504205444238227186284163 756308166357340779426245)
                  ·
                    refine ⟨141807781192001396142421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756308166357340779426245 141807781192001396142421)
                    ·
                      rfl

theorem cell23_828509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_828509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828509 prefixEnd_828509 := by exact prefixLift 828509
  have htrace : WordTrace (prefixWord ++ tailWord_828509) baseStart_828509 baseEnd_828509 := by
    simpa [prefixWord, tailWord_828509, baseEnd_828509] using wordTrace_append hprefix tailTrace_828509
  have hstable : (prefixWord ++ tailWord_828509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828509).length < 2 ^ (prefixWord ++ tailWord_828509).sum := by decide
  have hdescent : baseEnd_828509 < baseStart_828509 := by decide
  rcases family_descends (prefixWord ++ tailWord_828509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828548 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_828548 : Nat := 118140960795 + 828548 * 2 ^ 59
def prefixEnd_828548 : Nat := 4983230072969 + 3 ^ 40 * 828548 * 2
def baseEnd_828548 : Nat := 141814456440509845279861

theorem tailTrace_828548 : CollatzResearch.WordTrace tailWord_828548 prefixEnd_828548 141814456440509845279861 := by
  unfold tailWord_828548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109814101159787788871149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20146418801546383718494865 15109814101159787788871149)
  ·
    refine ⟨5666180287934920420826681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15109814101159787788871149 5666180287934920420826681)
    ·
      refine ⟨4249635215951190315620011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5666180287934920420826681 4249635215951190315620011)
      ·
        refine ⟨6374452823926785473430017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249635215951190315620011 6374452823926785473430017)
        ·
          refine ⟨4780839617945089105072513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6374452823926785473430017 4780839617945089105072513)
          ·
            refine ⟨3585629713458816828804385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780839617945089105072513 3585629713458816828804385)
            ·
              refine ⟨2689222285094112621603289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585629713458816828804385 2689222285094112621603289)
              ·
                refine ⟨2016916713820584466202467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689222285094112621603289 2016916713820584466202467)
                ·
                  refine ⟨3025375070730876699303701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016916713820584466202467 3025375070730876699303701)
                  ·
                    refine ⟨141814456440509845279861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3025375070730876699303701 141814456440509845279861)
                    ·
                      rfl

theorem cell23_828548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_828548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828548 prefixEnd_828548 := by exact prefixLift 828548
  have htrace : WordTrace (prefixWord ++ tailWord_828548) baseStart_828548 baseEnd_828548 := by
    simpa [prefixWord, tailWord_828548, baseEnd_828548] using wordTrace_append hprefix tailTrace_828548
  have hstable : (prefixWord ++ tailWord_828548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828548).length < 2 ^ (prefixWord ++ tailWord_828548).sum := by decide
  have hdescent : baseEnd_828548 < baseStart_828548 := by decide
  rcases family_descends (prefixWord ++ tailWord_828548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828549 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 1, 1, 3]
def baseStart_828549 : Nat := 118140960795 + 828549 * 2 ^ 59
def prefixEnd_828549 : Nat := 4983230072969 + 3 ^ 40 * 828549 * 2
def baseEnd_828549 : Nat := 425443882802184031927079

theorem tailTrace_828549 : CollatzResearch.WordTrace tailWord_828549 prefixEnd_828549 425443882802184031927079 := by
  unfold tailWord_828549
  simp only [CollatzResearch.WordTrace]
  refine ⟨30219664675315952748528701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20146443116877301832352467 30219664675315952748528701)
  ·
    refine ⟨11332374253243482280698263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30219664675315952748528701 11332374253243482280698263)
    ·
      refine ⟨16998561379865223421047395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11332374253243482280698263 16998561379865223421047395)
      ·
        refine ⟨25497842069797835131571093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16998561379865223421047395 25497842069797835131571093)
        ·
          refine ⟨1195211347021773521792395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25497842069797835131571093 1195211347021773521792395)
          ·
            refine ⟨1792817020532660282688593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195211347021773521792395 1792817020532660282688593)
            ·
              refine ⟨1344612765399495212016445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792817020532660282688593 1344612765399495212016445)
              ·
                refine ⟨504229787024810704506167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1344612765399495212016445 504229787024810704506167)
                ·
                  refine ⟨756344680537216056759251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504229787024810704506167 756344680537216056759251)
                  ·
                    refine ⟨1134517020805824085138877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756344680537216056759251 1134517020805824085138877)
                    ·
                      refine ⟨425443882802184031927079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1134517020805824085138877 425443882802184031927079)
                      ·
                        rfl

theorem cell23_828549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_828549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828549 prefixEnd_828549 := by exact prefixLift 828549
  have htrace : WordTrace (prefixWord ++ tailWord_828549) baseStart_828549 baseEnd_828549 := by
    simpa [prefixWord, tailWord_828549, baseEnd_828549] using wordTrace_append hprefix tailTrace_828549
  have hstable : (prefixWord ++ tailWord_828549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828549).length < 2 ^ (prefixWord ++ tailWord_828549).sum := by decide
  have hdescent : baseEnd_828549 < baseStart_828549 := by decide
  rcases family_descends (prefixWord ++ tailWord_828549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828551 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_828551 : Nat := 118140960795 + 828551 * 2 ^ 59
def prefixEnd_828551 : Nat := 4983230072969 + 3 ^ 40 * 828551 * 2
def baseEnd_828551 : Nat := 425444909763493024102069

theorem tailTrace_828551 : CollatzResearch.WordTrace tailWord_828551 prefixEnd_828551 425444909763493024102069 := by
  unfold tailWord_828551
  simp only [CollatzResearch.WordTrace]
  refine ⟨30219737621308707090101507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20146491747539138060067671 30219737621308707090101507)
  ·
    refine ⟨45329606431963060635152261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30219737621308707090101507 45329606431963060635152261)
    ·
      refine ⟨8499301205993073869091049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45329606431963060635152261 8499301205993073869091049)
      ·
        refine ⟨6374475904494805401818287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8499301205993073869091049 6374475904494805401818287)
        ·
          refine ⟨9561713856742208102727431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374475904494805401818287 9561713856742208102727431)
          ·
            refine ⟨14342570785113312154091147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561713856742208102727431 14342570785113312154091147)
            ·
              refine ⟨21513856177669968231136721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14342570785113312154091147 21513856177669968231136721)
              ·
                refine ⟨16135392133252476173352541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21513856177669968231136721 16135392133252476173352541)
                ·
                  refine ⟨6050772049969678565007203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16135392133252476173352541 6050772049969678565007203)
                  ·
                    refine ⟨9076158074954517847510805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6050772049969678565007203 9076158074954517847510805)
                    ·
                      refine ⟨425444909763493024102069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9076158074954517847510805 425444909763493024102069)
                      ·
                        rfl

theorem cell23_828551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_828551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828551 prefixEnd_828551 := by exact prefixLift 828551
  have htrace : WordTrace (prefixWord ++ tailWord_828551) baseStart_828551 baseEnd_828551 := by
    simpa [prefixWord, tailWord_828551, baseEnd_828551] using wordTrace_append hprefix tailTrace_828551
  have hstable : (prefixWord ++ tailWord_828551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828551).length < 2 ^ (prefixWord ++ tailWord_828551).sum := by decide
  have hdescent : baseEnd_828551 < baseStart_828551 := by decide
  rcases family_descends (prefixWord ++ tailWord_828551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828572 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_828572 : Nat := 118140960795 + 828572 * 2 ^ 59
def prefixEnd_828572 : Nat := 4983230072969 + 3 ^ 40 * 828572 * 2
def baseEnd_828572 : Nat := 425455692857237441939473

theorem tailTrace_828572 : CollatzResearch.WordTrace tailWord_828572 prefixEnd_828572 425455692857237441939473 := by
  unfold tailWord_828572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110251777116313838307985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20147002369488418451077313 15110251777116313838307985)
  ·
    refine ⟨11332688832837235378730989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15110251777116313838307985 11332688832837235378730989)
    ·
      refine ⟨4249758312313963267024121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11332688832837235378730989 4249758312313963267024121)
      ·
        refine ⟨3187318734235472450268091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4249758312313963267024121 3187318734235472450268091)
        ·
          refine ⟨4780978101353208675402137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187318734235472450268091 4780978101353208675402137)
          ·
            refine ⟨3585733576014906506551603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780978101353208675402137 3585733576014906506551603)
            ·
              refine ⟨5378600364022359759827405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585733576014906506551603 5378600364022359759827405)
              ·
                refine ⟨2016975136508384909935277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5378600364022359759827405 2016975136508384909935277)
                ·
                  refine ⟨756365676190644341225729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2016975136508384909935277 756365676190644341225729)
                  ·
                    refine ⟨567274257142983255919297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756365676190644341225729 567274257142983255919297)
                    ·
                      refine ⟨425455692857237441939473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567274257142983255919297 425455692857237441939473)
                      ·
                        rfl

theorem cell23_828572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_828572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828572 prefixEnd_828572 := by exact prefixLift 828572
  have htrace : WordTrace (prefixWord ++ tailWord_828572) baseStart_828572 baseEnd_828572 := by
    simpa [prefixWord, tailWord_828572, baseEnd_828572] using wordTrace_append hprefix tailTrace_828572
  have hstable : (prefixWord ++ tailWord_828572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828572).length < 2 ^ (prefixWord ++ tailWord_828572).sum := by decide
  have hdescent : baseEnd_828572 < baseStart_828572 := by decide
  rcases family_descends (prefixWord ++ tailWord_828572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828575 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_828575 : Nat := 118140960795 + 828575 * 2 ^ 59
def prefixEnd_828575 : Nat := 4983230072969 + 3 ^ 40 * 828575 * 2
def baseEnd_828575 : Nat := 425457233299200930201959

theorem tailTrace_828575 : CollatzResearch.WordTrace tailWord_828575 prefixEnd_828575 425457233299200930201959 := by
  unfold tailWord_828575
  simp only [CollatzResearch.WordTrace]
  refine ⟨30220612973221759188975179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20147075315481172792650119 30220612973221759188975179)
  ·
    refine ⟨45330919459832638783462769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30220612973221759188975179 45330919459832638783462769)
    ·
      refine ⟨33998189594874479087597077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45330919459832638783462769 33998189594874479087597077)
      ·
        refine ⟨1593665137259741207231113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33998189594874479087597077 1593665137259741207231113)
        ·
          refine ⟨1195248852944805905423335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1593665137259741207231113 1195248852944805905423335)
          ·
            refine ⟨1792873279417208858135003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195248852944805905423335 1792873279417208858135003)
            ·
              refine ⟨2689309919125813287202505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792873279417208858135003 2689309919125813287202505)
              ·
                refine ⟨2016982439344359965401879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689309919125813287202505 2016982439344359965401879)
                ·
                  refine ⟨3025473659016539948102819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016982439344359965401879 3025473659016539948102819)
                  ·
                    refine ⟨4538210488524809922154229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025473659016539948102819 4538210488524809922154229)
                    ·
                      refine ⟨425457233299200930201959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4538210488524809922154229 425457233299200930201959)
                      ·
                        rfl

theorem cell23_828575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_828575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828575 prefixEnd_828575 := by exact prefixLift 828575
  have htrace : WordTrace (prefixWord ++ tailWord_828575) baseStart_828575 baseEnd_828575 := by
    simpa [prefixWord, tailWord_828575, baseEnd_828575] using wordTrace_append hprefix tailTrace_828575
  have hstable : (prefixWord ++ tailWord_828575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828575).length < 2 ^ (prefixWord ++ tailWord_828575).sum := by decide
  have hdescent : baseEnd_828575 < baseStart_828575 := by decide
  rcases family_descends (prefixWord ++ tailWord_828575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828588 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_828588 : Nat := 118140960795 + 828588 * 2 ^ 59
def prefixEnd_828588 : Nat := 4983230072969 + 3 ^ 40 * 828588 * 2
def baseEnd_828588 : Nat := 425463908547709379339399

theorem tailTrace_828588 : CollatzResearch.WordTrace tailWord_828588 prefixEnd_828588 425463908547709379339399 := by
  unfold tailWord_828588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110543561087331204599209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20147391414783108272798945 15110543561087331204599209)
  ·
    refine ⟨11332907670815498403449407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15110543561087331204599209 11332907670815498403449407)
    ·
      refine ⟨16999361506223247605174111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11332907670815498403449407 16999361506223247605174111)
      ·
        refine ⟨25499042259334871407761167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16999361506223247605174111 25499042259334871407761167)
        ·
          refine ⟨38248563389002307111641751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25499042259334871407761167 38248563389002307111641751)
          ·
            refine ⟨57372845083503460667462627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38248563389002307111641751 57372845083503460667462627)
            ·
              refine ⟨86059267625255191001193941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57372845083503460667462627 86059267625255191001193941)
              ·
                refine ⟨2017014084966918539090483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86059267625255191001193941 2017014084966918539090483)
                ·
                  refine ⟨3025521127450377808635725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017014084966918539090483 3025521127450377808635725)
                  ·
                    refine ⟨1134570422793891678238397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025521127450377808635725 1134570422793891678238397)
                    ·
                      refine ⟨425463908547709379339399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1134570422793891678238397 425463908547709379339399)
                      ·
                        rfl

theorem cell23_828588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_828588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828588 prefixEnd_828588 := by exact prefixLift 828588
  have htrace : WordTrace (prefixWord ++ tailWord_828588) baseStart_828588 baseEnd_828588 := by
    simpa [prefixWord, tailWord_828588, baseEnd_828588] using wordTrace_append hprefix tailTrace_828588
  have hstable : (prefixWord ++ tailWord_828588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828588).length < 2 ^ (prefixWord ++ tailWord_828588).sum := by decide
  have hdescent : baseEnd_828588 < baseStart_828588 := by decide
  rcases family_descends (prefixWord ++ tailWord_828588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828591 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 2, 7]
def baseStart_828591 : Nat := 118140960795 + 828591 * 2 ^ 59
def prefixEnd_828591 : Nat := 4983230072969 + 3 ^ 40 * 828591 * 2
def baseEnd_828591 : Nat := 141821816329890955867295

theorem tailTrace_828591 : CollatzResearch.WordTrace tailWord_828591 prefixEnd_828591 141821816329890955867295 := by
  unfold tailWord_828591
  simp only [CollatzResearch.WordTrace]
  refine ⟨30221196541163793921557627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20147464360775862614371751 30221196541163793921557627)
  ·
    refine ⟨45331794811745690882336441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30221196541163793921557627 45331794811745690882336441)
    ·
      refine ⟨33998846108809268161752331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45331794811745690882336441 33998846108809268161752331)
      ·
        refine ⟨50998269163213902242628497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33998846108809268161752331 50998269163213902242628497)
        ·
          refine ⟨38248701872410426681971373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50998269163213902242628497 38248701872410426681971373)
          ·
            refine ⟨14343263202153910005739265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38248701872410426681971373 14343263202153910005739265)
            ·
              refine ⟨10757447401615432504304449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14343263202153910005739265 10757447401615432504304449)
              ·
                refine ⟨8068085551211574378228337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10757447401615432504304449 8068085551211574378228337)
                ·
                  refine ⟨6051064163408680783671253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8068085551211574378228337 6051064163408680783671253)
                  ·
                    refine ⟨141821816329890955867295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6051064163408680783671253 141821816329890955867295)
                    ·
                      rfl

theorem cell23_828591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_828591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828591 prefixEnd_828591 := by exact prefixLift 828591
  have htrace : WordTrace (prefixWord ++ tailWord_828591) baseStart_828591 baseEnd_828591 := by
    simpa [prefixWord, tailWord_828591, baseEnd_828591] using wordTrace_append hprefix tailTrace_828591
  have hstable : (prefixWord ++ tailWord_828591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828591).length < 2 ^ (prefixWord ++ tailWord_828591).sum := by decide
  have hdescent : baseEnd_828591 < baseStart_828591 := by decide
  rcases family_descends (prefixWord ++ tailWord_828591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828605 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_828605 : Nat := 118140960795 + 828605 * 2 ^ 59
def prefixEnd_828605 : Nat := 4983230072969 + 3 ^ 40 * 828605 * 2
def baseEnd_828605 : Nat := 425472637718835812826821

theorem tailTrace_828605 : CollatzResearch.WordTrace tailWord_828605 prefixEnd_828605 425472637718835812826821 := by
  unfold tailWord_828605
  simp only [CollatzResearch.WordTrace]
  refine ⟨30221707163113074312567269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20147804775408716208378179 30221707163113074312567269)
  ·
    refine ⟨5666570093083701433606363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30221707163113074312567269 5666570093083701433606363)
    ·
      refine ⟨8499855139625552150409545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5666570093083701433606363 8499855139625552150409545)
      ·
        refine ⟨6374891354719164112807159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8499855139625552150409545 6374891354719164112807159)
        ·
          refine ⟨9562337032078746169210739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374891354719164112807159 9562337032078746169210739)
          ·
            refine ⟨14343505548118119253816109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9562337032078746169210739 14343505548118119253816109)
            ·
              refine ⟨5378814580544294720181041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14343505548118119253816109 5378814580544294720181041)
              ·
                refine ⟨4034110935408221040135781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5378814580544294720181041 4034110935408221040135781)
                ·
                  refine ⟨756395800389041445025459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4034110935408221040135781 756395800389041445025459)
                  ·
                    refine ⟨1134593700583562167538189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 756395800389041445025459 1134593700583562167538189)
                    ·
                      refine ⟨425472637718835812826821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1134593700583562167538189 425472637718835812826821)
                      ·
                        rfl

theorem cell23_828605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_828605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828605 prefixEnd_828605 := by exact prefixLift 828605
  have htrace : WordTrace (prefixWord ++ tailWord_828605) baseStart_828605 baseEnd_828605 := by
    simpa [prefixWord, tailWord_828605, baseEnd_828605] using wordTrace_append hprefix tailTrace_828605
  have hstable : (prefixWord ++ tailWord_828605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828605).length < 2 ^ (prefixWord ++ tailWord_828605).sum := by decide
  have hdescent : baseEnd_828605 < baseStart_828605 := by decide
  rcases family_descends (prefixWord ++ tailWord_828605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828606 : List Nat := [4, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_828606 : Nat := 118140960795 + 828606 * 2 ^ 59
def prefixEnd_828606 : Nat := 4983230072969 + 3 ^ 40 * 828606 * 2
def baseEnd_828606 : Nat := 425473151199490308914317

theorem tailTrace_828606 : CollatzResearch.WordTrace tailWord_828606 prefixEnd_828606 425473151199490308914317 := by
  unfold tailWord_828606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777717954513681435419209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20147829090739634322235781 3777717954513681435419209)
  ·
    refine ⟨2833288465885261076564407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3777717954513681435419209 2833288465885261076564407)
    ·
      refine ⟨4249932698827891614846611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2833288465885261076564407 4249932698827891614846611)
      ·
        refine ⟨6374899048241837422269917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249932698827891614846611 6374899048241837422269917)
        ·
          refine ⟨2390587143090689033351219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6374899048241837422269917 2390587143090689033351219)
          ·
            refine ⟨3585880714636033550026829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390587143090689033351219 3585880714636033550026829)
            ·
              refine ⟨1344705267988512581260061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3585880714636033550026829 1344705267988512581260061)
              ·
                refine ⟨504264475495692217972523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1344705267988512581260061 504264475495692217972523)
                ·
                  refine ⟨756396713243538326958785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504264475495692217972523 756396713243538326958785)
                  ·
                    refine ⟨567297534932653745219089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 756396713243538326958785 567297534932653745219089)
                    ·
                      refine ⟨425473151199490308914317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 567297534932653745219089 425473151199490308914317)
                      ·
                        rfl

theorem cell23_828606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_828606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828606 prefixEnd_828606 := by exact prefixLift 828606
  have htrace : WordTrace (prefixWord ++ tailWord_828606) baseStart_828606 baseEnd_828606 := by
    simpa [prefixWord, tailWord_828606, baseEnd_828606] using wordTrace_append hprefix tailTrace_828606
  have hstable : (prefixWord ++ tailWord_828606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828606).length < 2 ^ (prefixWord ++ tailWord_828606).sum := by decide
  have hdescent : baseEnd_828606 < baseStart_828606 := by decide
  rcases family_descends (prefixWord ++ tailWord_828606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828648 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_828648 : Nat := 118140960795 + 828648 * 2 ^ 59
def prefixEnd_828648 : Nat := 4983230072969 + 3 ^ 40 * 828648 * 2
def baseEnd_828648 : Nat := 425494717386979144589123

theorem tailTrace_828648 : CollatzResearch.WordTrace tailWord_828648 prefixEnd_828648 425494717386979144589123 := by
  unfold tailWord_828648
  simp only [CollatzResearch.WordTrace]
  refine ⟨15111637750978646328191299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20148850334638195104255065 15111637750978646328191299)
  ·
    refine ⟨22667456626467969492286949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15111637750978646328191299 22667456626467969492286949)
    ·
      refine ⟨4250148117462744279803803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22667456626467969492286949 4250148117462744279803803)
      ·
        refine ⟨6375222176194116419705705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4250148117462744279803803 6375222176194116419705705)
        ·
          refine ⟨4781416632145587314779279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6375222176194116419705705 4781416632145587314779279)
          ·
            refine ⟨7172124948218380972168919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781416632145587314779279 7172124948218380972168919)
            ·
              refine ⟨10758187422327571458253379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172124948218380972168919 10758187422327571458253379)
              ·
                refine ⟨16137281133491357187380069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10758187422327571458253379 16137281133491357187380069)
                ·
                  refine ⟨3025740212529629472633763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16137281133491357187380069 3025740212529629472633763)
                  ·
                    refine ⟨4538610318794444208950645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3025740212529629472633763 4538610318794444208950645)
                    ·
                      refine ⟨425494717386979144589123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4538610318794444208950645 425494717386979144589123)
                      ·
                        rfl

theorem cell23_828648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_828648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_828648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_828648 prefixEnd_828648 := by exact prefixLift 828648
  have htrace : WordTrace (prefixWord ++ tailWord_828648) baseStart_828648 baseEnd_828648 := by
    simpa [prefixWord, tailWord_828648, baseEnd_828648] using wordTrace_append hprefix tailTrace_828648
  have hstable : (prefixWord ++ tailWord_828648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828648).length < 2 ^ (prefixWord ++ tailWord_828648).sum := by decide
  have hdescent : baseEnd_828648 < baseStart_828648 := by decide
  rcases family_descends (prefixWord ++ tailWord_828648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
