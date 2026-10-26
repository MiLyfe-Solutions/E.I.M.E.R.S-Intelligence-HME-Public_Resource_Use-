import V185TrunkScan23Chunk1124

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6663030 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_6663030 : Nat := 118140960795 + 6663030 * 2 ^ 59
def prefixEnd_6663030 : Nat := 4983230072969 + 3 ^ 40 * 6663030 * 2
def baseEnd_6663030 : Nat := 1140445668442390366060763

theorem tailTrace_6663030 : CollatzResearch.WordTrace tailWord_6663030 prefixEnd_6663030 1140445668442390366060763 := by
  unfold tailWord_6663030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188791815686733735743159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162013779367325159847927029 15188791815686733735743159)
  ·
    refine ⟨22783187723530100603614739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15188791815686733735743159 22783187723530100603614739)
    ·
      refine ⟨34174781585295150905422109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22783187723530100603614739 34174781585295150905422109)
      ·
        refine ⟨12815543094485681589533291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34174781585295150905422109 12815543094485681589533291)
        ·
          refine ⟨19223314641728522384299937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12815543094485681589533291 19223314641728522384299937)
          ·
            refine ⟨14417485981296391788224953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19223314641728522384299937 14417485981296391788224953)
            ·
              refine ⟨10813114485972293841168715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14417485981296391788224953 10813114485972293841168715)
              ·
                refine ⟨16219671728958440761753073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10813114485972293841168715 16219671728958440761753073)
                ·
                  refine ⟨12164753796718830571314805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16219671728958440761753073 12164753796718830571314805)
                  ·
                    refine ⟨1140445668442390366060763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12164753796718830571314805 1140445668442390366060763)
                    ·
                      rfl

theorem cell23_6663030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_6663030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663030 prefixEnd_6663030 := by exact prefixLift 6663030
  have htrace : WordTrace (prefixWord ++ tailWord_6663030) baseStart_6663030 baseEnd_6663030 := by
    simpa [prefixWord, tailWord_6663030, baseEnd_6663030] using wordTrace_append hprefix tailTrace_6663030
  have hstable : (prefixWord ++ tailWord_6663030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663030).length < 2 ^ (prefixWord ++ tailWord_6663030).sum := by decide
  have hdescent : baseEnd_6663030 < baseStart_6663030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663033 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_6663033 : Nat := 118140960795 + 6663033 * 2 ^ 59
def prefixEnd_6663033 : Nat := 4983230072969 + 3 ^ 40 * 6663033 * 2
def baseEnd_6663033 : Nat := 3421338545769134586444775

theorem tailTrace_6663033 : CollatzResearch.WordTrace tailWord_6663033 prefixEnd_6663033 3421338545769134586444775 := by
  unfold tailWord_6663033
  simp only [CollatzResearch.WordTrace]
  refine ⟨243020778469976871284249753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162013852313317914189499835 243020778469976871284249753)
  ·
    refine ⟨182265583852482653463187315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243020778469976871284249753 182265583852482653463187315)
    ·
      refine ⟨273398375778723980194780973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182265583852482653463187315 273398375778723980194780973)
      ·
        refine ⟨102524390917021492573042865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273398375778723980194780973 102524390917021492573042865)
        ·
          refine ⟨76893293187766119429782149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102524390917021492573042865 76893293187766119429782149)
          ·
            refine ⟨14417492472706147393084153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76893293187766119429782149 14417492472706147393084153)
            ·
              refine ⟨10813119354529610544813115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14417492472706147393084153 10813119354529610544813115)
              ·
                refine ⟨16219679031794415817219673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10813119354529610544813115 16219679031794415817219673)
                ·
                  refine ⟨12164759273845811862914755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16219679031794415817219673 12164759273845811862914755)
                  ·
                    refine ⟨18247138910768717794372133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12164759273845811862914755 18247138910768717794372133)
                    ·
                      refine ⟨3421338545769134586444775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18247138910768717794372133 3421338545769134586444775)
                      ·
                        rfl

theorem cell23_6663033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_6663033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663033 prefixEnd_6663033 := by exact prefixLift 6663033
  have htrace : WordTrace (prefixWord ++ tailWord_6663033) baseStart_6663033 baseEnd_6663033 := by
    simpa [prefixWord, tailWord_6663033, baseEnd_6663033] using wordTrace_append hprefix tailTrace_6663033
  have hstable : (prefixWord ++ tailWord_6663033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663033).length < 2 ^ (prefixWord ++ tailWord_6663033).sum := by decide
  have hdescent : baseEnd_6663033 < baseStart_6663033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663036 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_6663036 : Nat := 118140960795 + 6663036 * 2 ^ 59
def prefixEnd_6663036 : Nat := 4983230072969 + 3 ^ 40 * 6663036 * 2
def baseEnd_6663036 : Nat := 3421340086211098074707261

theorem tailTrace_6663036 : CollatzResearch.WordTrace tailWord_6663036 prefixEnd_6663036 3421340086211098074707261 := by
  unfold tailWord_6663036
  simp only [CollatzResearch.WordTrace]
  refine ⟨121510443944483001398304481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162013925259310668531072641 121510443944483001398304481)
  ·
    refine ⟨91132832958362251048728361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121510443944483001398304481 91132832958362251048728361)
    ·
      refine ⟨68349624718771688286546271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91132832958362251048728361 68349624718771688286546271)
      ·
        refine ⟨102524437078157532429819407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68349624718771688286546271 102524437078157532429819407)
        ·
          refine ⟨153786655617236298644729111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102524437078157532429819407 153786655617236298644729111)
          ·
            refine ⟨230679983425854447967093667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153786655617236298644729111 230679983425854447967093667)
            ·
              refine ⟨346019975138781671950640501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230679983425854447967093667 346019975138781671950640501)
              ·
                refine ⟨32439372669260781745372547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346019975138781671950640501 32439372669260781745372547)
                ·
                  refine ⟨48659059003891172618058821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32439372669260781745372547 48659059003891172618058821)
                  ·
                    refine ⟨9123573563229594865886029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48659059003891172618058821 9123573563229594865886029)
                    ·
                      refine ⟨3421340086211098074707261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123573563229594865886029 3421340086211098074707261)
                      ·
                        rfl

theorem cell23_6663036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_6663036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663036 prefixEnd_6663036 := by exact prefixLift 6663036
  have htrace : WordTrace (prefixWord ++ tailWord_6663036) baseStart_6663036 baseEnd_6663036 := by
    simpa [prefixWord, tailWord_6663036, baseEnd_6663036] using wordTrace_append hprefix tailTrace_6663036
  have hstable : (prefixWord ++ tailWord_6663036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663036).length < 2 ^ (prefixWord ++ tailWord_6663036).sum := by decide
  have hdescent : baseEnd_6663036 < baseStart_6663036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663039 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 10]
def baseStart_6663039 : Nat := 118140960795 + 6663039 * 2 ^ 59
def prefixEnd_6663039 : Nat := 4983230072969 + 3 ^ 40 * 6663039 * 2
def baseEnd_6663039 : Nat := 380149069628117951441083

theorem tailTrace_6663039 : CollatzResearch.WordTrace tailWord_6663039 prefixEnd_6663039 380149069628117951441083 := by
  unfold tailWord_6663039
  simp only [CollatzResearch.WordTrace]
  refine ⟨243020997307955134308968171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162013998205303422872645447 243020997307955134308968171)
  ·
    refine ⟨364531495961932701463452257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243020997307955134308968171 364531495961932701463452257)
    ·
      refine ⟨273398621971449526097589193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364531495961932701463452257 273398621971449526097589193)
      ·
        refine ⟨205048966478587144573191895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273398621971449526097589193 205048966478587144573191895)
        ·
          refine ⟨307573449717880716859787843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205048966478587144573191895 307573449717880716859787843)
          ·
            refine ⟨461360174576821075289681765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307573449717880716859787843 461360174576821075289681765)
            ·
              refine ⟨86505032733153951616815331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461360174576821075289681765 86505032733153951616815331)
              ·
                refine ⟨129757549099730927425222997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86505032733153951616815331 129757549099730927425222997)
                ·
                  refine ⟨380149069628117951441083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129757549099730927425222997 380149069628117951441083)
                  ·
                    rfl

theorem cell23_6663039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 10].length) (baseStart_6663039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663039 prefixEnd_6663039 := by exact prefixLift 6663039
  have htrace : WordTrace (prefixWord ++ tailWord_6663039) baseStart_6663039 baseEnd_6663039 := by
    simpa [prefixWord, tailWord_6663039, baseEnd_6663039] using wordTrace_append hprefix tailTrace_6663039
  have hstable : (prefixWord ++ tailWord_6663039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663039).length < 2 ^ (prefixWord ++ tailWord_6663039).sum := by decide
  have hdescent : baseEnd_6663039 < baseStart_6663039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663073 : List Nat := [1, 2, 3, 4, 1, 1, 2, 3, 6]
def baseStart_6663073 : Nat := 118140960795 + 6663073 * 2 ^ 59
def prefixEnd_6663073 : Nat := 4983230072969 + 3 ^ 40 * 6663073 * 2
def baseEnd_6663073 : Nat := 380151009443923825549399

theorem tailTrace_6663073 : CollatzResearch.WordTrace tailWord_6663073 prefixEnd_6663073 380151009443923825549399 := by
  unfold tailWord_6663073
  simp only [CollatzResearch.WordTrace]
  refine ⟨243022237389831958115705873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162014824926554638743803915 243022237389831958115705873)
  ·
    refine ⟨182266678042373968586779405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243022237389831958115705873 182266678042373968586779405)
    ·
      refine ⟨68350004265890238220042277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182266678042373968586779405 68350004265890238220042277)
      ·
        refine ⟨12815625799854419666257927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68350004265890238220042277 12815625799854419666257927)
        ·
          refine ⟨19223438699781629499386891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12815625799854419666257927 19223438699781629499386891)
          ·
            refine ⟨28835158049672444249080337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19223438699781629499386891 28835158049672444249080337)
            ·
              refine ⟨21626368537254333186810253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28835158049672444249080337 21626368537254333186810253)
              ·
                refine ⟨8109888201470374945053845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21626368537254333186810253 8109888201470374945053845)
                ·
                  refine ⟨380151009443923825549399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8109888201470374945053845 380151009443923825549399)
                  ·
                    rfl

theorem cell23_6663073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 6].length) (baseStart_6663073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663073 prefixEnd_6663073 := by exact prefixLift 6663073
  have htrace : WordTrace (prefixWord ++ tailWord_6663073) baseStart_6663073 baseEnd_6663073 := by
    simpa [prefixWord, tailWord_6663073, baseEnd_6663073] using wordTrace_append hprefix tailTrace_6663073
  have hstable : (prefixWord ++ tailWord_6663073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663073).length < 2 ^ (prefixWord ++ tailWord_6663073).sum := by decide
  have hdescent : baseEnd_6663073 < baseStart_6663073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663083 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 3]
def baseStart_6663083 : Nat := 118140960795 + 6663083 * 2 ^ 59
def prefixEnd_6663083 : Nat := 4983230072969 + 3 ^ 40 * 6663083 * 2
def baseEnd_6663083 : Nat := 3421364219801859390819545

theorem tailTrace_6663083 : CollatzResearch.WordTrace tailWord_6663083 prefixEnd_6663083 3421364219801859390819545 := by
  unfold tailWord_6663083
  simp only [CollatzResearch.WordTrace]
  refine ⟨243022602119795729823569903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162015068079863819882379935 243022602119795729823569903)
  ·
    refine ⟨364533903179693594735354855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243022602119795729823569903 364533903179693594735354855)
    ·
      refine ⟨546800854769540392103032283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364533903179693594735354855 546800854769540392103032283)
      ·
        refine ⟨820201282154310588154548425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546800854769540392103032283 820201282154310588154548425)
        ·
          refine ⟨615150961615732941115911319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820201282154310588154548425 615150961615732941115911319)
          ·
            refine ⟨922726442423599411673866979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615150961615732941115911319 922726442423599411673866979)
            ·
              refine ⟨1384089663635399117510800469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922726442423599411673866979 1384089663635399117510800469)
              ·
                refine ⟨16219800745727333408329693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1384089663635399117510800469 16219800745727333408329693)
                ·
                  refine ⟨6082425279647750028123635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16219800745727333408329693 6082425279647750028123635)
                  ·
                    refine ⟨9123637919471625042185453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6082425279647750028123635 9123637919471625042185453)
                    ·
                      refine ⟨3421364219801859390819545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123637919471625042185453 3421364219801859390819545)
                      ·
                        rfl

theorem cell23_6663083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 3].length) (baseStart_6663083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663083 prefixEnd_6663083 := by exact prefixLift 6663083
  have htrace : WordTrace (prefixWord ++ tailWord_6663083) baseStart_6663083 baseEnd_6663083 := by
    simpa [prefixWord, tailWord_6663083, baseEnd_6663083] using wordTrace_append hprefix tailTrace_6663083
  have hstable : (prefixWord ++ tailWord_6663083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663083).length < 2 ^ (prefixWord ++ tailWord_6663083).sum := by decide
  have hdescent : baseEnd_6663083 < baseStart_6663083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663140 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_6663140 : Nat := 118140960795 + 6663140 * 2 ^ 59
def prefixEnd_6663140 : Nat := 4983230072969 + 3 ^ 40 * 6663140 * 2
def baseEnd_6663140 : Nat := 3421393488199165667806783

theorem tailTrace_6663140 : CollatzResearch.WordTrace tailWord_6663140 prefixEnd_6663140 3421393488199165667806783 := by
  unfold tailWord_6663140
  simp only [CollatzResearch.WordTrace]
  refine ⟨121512340540294614279197437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162016454053726152372263249 121512340540294614279197437)
  ·
    refine ⟨45567127702610480354699039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121512340540294614279197437 45567127702610480354699039)
    ·
      refine ⟨68350691553915720532048559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45567127702610480354699039 68350691553915720532048559)
      ·
        refine ⟨102526037330873580798072839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68350691553915720532048559 102526037330873580798072839)
        ·
          refine ⟨153789055996310371197109259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102526037330873580798072839 153789055996310371197109259)
          ·
            refine ⟨230683583994465556795663889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153789055996310371197109259 230683583994465556795663889)
            ·
              refine ⟨173012687995849167596747917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230683583994465556795663889 173012687995849167596747917)
              ·
                refine ⟨64879757998443437848780469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173012687995849167596747917 64879757998443437848780469)
                ·
                  refine ⟨6082477312354072298323169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64879757998443437848780469 6082477312354072298323169)
                  ·
                    refine ⟨4561857984265554223742377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6082477312354072298323169 4561857984265554223742377)
                    ·
                      refine ⟨3421393488199165667806783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561857984265554223742377 3421393488199165667806783)
                      ·
                        rfl

theorem cell23_6663140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_6663140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663140 prefixEnd_6663140 := by exact prefixLift 6663140
  have htrace : WordTrace (prefixWord ++ tailWord_6663140) baseStart_6663140 baseEnd_6663140 := by
    simpa [prefixWord, tailWord_6663140, baseEnd_6663140] using wordTrace_append hprefix tailTrace_6663140
  have hstable : (prefixWord ++ tailWord_6663140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663140).length < 2 ^ (prefixWord ++ tailWord_6663140).sum := by decide
  have hdescent : baseEnd_6663140 < baseStart_6663140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663207 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6663207 : Nat := 118140960795 + 6663207 * 2 ^ 59
def prefixEnd_6663207 : Nat := 4983230072969 + 3 ^ 40 * 6663207 * 2
def baseEnd_6663207 : Nat := 3421427891403016905668975

theorem tailTrace_6663207 : CollatzResearch.WordTrace tailWord_6663207 prefixEnd_6663207 3421427891403016905668975 := by
  unfold tailWord_6663207
  simp only [CollatzResearch.WordTrace]
  refine ⟨243027124771346499001083875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162018083180897666000722583 243027124771346499001083875)
  ·
    refine ⟨364540687157019748501625813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243027124771346499001083875 364540687157019748501625813)
    ·
      refine ⟨8543922355242650355506855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 364540687157019748501625813 8543922355242650355506855)
      ·
        refine ⟨12815883532863975533260283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8543922355242650355506855 12815883532863975533260283)
        ·
          refine ⟨19223825299295963299890425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12815883532863975533260283 19223825299295963299890425)
          ·
            refine ⟨14417868974471972474917819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19223825299295963299890425 14417868974471972474917819)
            ·
              refine ⟨21626803461707958712376729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14417868974471972474917819 21626803461707958712376729)
              ·
                refine ⟨16220102596280969034282547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21626803461707958712376729 16220102596280969034282547)
                ·
                  refine ⟨24330153894421453551423821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16220102596280969034282547 24330153894421453551423821)
                  ·
                    refine ⟨9123807710408045081783933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24330153894421453551423821 9123807710408045081783933)
                    ·
                      refine ⟨3421427891403016905668975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123807710408045081783933 3421427891403016905668975)
                      ·
                        rfl

theorem cell23_6663207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6663207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663207 prefixEnd_6663207 := by exact prefixLift 6663207
  have htrace : WordTrace (prefixWord ++ tailWord_6663207) baseStart_6663207 baseEnd_6663207 := by
    simpa [prefixWord, tailWord_6663207, baseEnd_6663207] using wordTrace_append hprefix tailTrace_6663207
  have hstable : (prefixWord ++ tailWord_6663207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663207).length < 2 ^ (prefixWord ++ tailWord_6663207).sum := by decide
  have hdescent : baseEnd_6663207 < baseStart_6663207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663230 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6663230 : Nat := 118140960795 + 6663230 * 2 ^ 59
def prefixEnd_6663230 : Nat := 4983230072969 + 3 ^ 40 * 6663230 * 2
def baseEnd_6663230 : Nat := 3421439701458070315681369

theorem tailTrace_6663230 : CollatzResearch.WordTrace tailWord_6663230 prefixEnd_6663230 3421439701458070315681369 := by
  unfold tailWord_6663230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378495456282896741146393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162018642433508782619447429 30378495456282896741146393)
  ·
    refine ⟨22783871592212172555859795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30378495456282896741146393 22783871592212172555859795)
    ·
      refine ⟨34175807388318258833789693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22783871592212172555859795 34175807388318258833789693)
      ·
        refine ⟨12815927770619347062671135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34175807388318258833789693 12815927770619347062671135)
        ·
          refine ⟨19223891655929020594006703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12815927770619347062671135 19223891655929020594006703)
          ·
            refine ⟨28835837483893530891010055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19223891655929020594006703 28835837483893530891010055)
            ·
              refine ⟨43253756225840296336515083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28835837483893530891010055 43253756225840296336515083)
              ·
                refine ⟨64880634338760444504772625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43253756225840296336515083 64880634338760444504772625)
                ·
                  refine ⟨48660475754070333378579469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64880634338760444504772625 48660475754070333378579469)
                  ·
                    refine ⟨18247678407776375016967301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48660475754070333378579469 18247678407776375016967301)
                    ·
                      refine ⟨3421439701458070315681369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18247678407776375016967301 3421439701458070315681369)
                      ·
                        rfl

theorem cell23_6663230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6663230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663230 prefixEnd_6663230 := by exact prefixLift 6663230
  have htrace : WordTrace (prefixWord ++ tailWord_6663230) baseStart_6663230 baseEnd_6663230 := by
    simpa [prefixWord, tailWord_6663230, baseEnd_6663230] using wordTrace_append hprefix tailTrace_6663230
  have hstable : (prefixWord ++ tailWord_6663230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663230).length < 2 ^ (prefixWord ++ tailWord_6663230).sum := by decide
  have hdescent : baseEnd_6663230 < baseStart_6663230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663253 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 7]
def baseStart_6663253 : Nat := 118140960795 + 6663253 * 2 ^ 59
def prefixEnd_6663253 : Nat := 4983230072969 + 3 ^ 40 * 6663253 * 2
def baseEnd_6663253 : Nat := 380161279057013747299307

theorem tailTrace_6663253 : CollatzResearch.WordTrace tailWord_6663253 prefixEnd_6663253 380161279057013747299307 := by
  unfold tailWord_6663253
  simp only [CollatzResearch.WordTrace]
  refine ⟨243028802529179848857258413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162019201686119899238172275 243028802529179848857258413)
  ·
    refine ⟨91135800948442443321471905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243028802529179848857258413 91135800948442443321471905)
    ·
      refine ⟨68351850711331832491103929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91135800948442443321471905 68351850711331832491103929)
      ·
        refine ⟨51263888033498874368327947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68351850711331832491103929 51263888033498874368327947)
        ·
          refine ⟨76895832050248311552491921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51263888033498874368327947 76895832050248311552491921)
          ·
            refine ⟨57671874037686233664368941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76895832050248311552491921 57671874037686233664368941)
            ·
              refine ⟨21626952764132337624138353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57671874037686233664368941 21626952764132337624138353)
              ·
                refine ⟨16220214573099253218103765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21626952764132337624138353 16220214573099253218103765)
                ·
                  refine ⟨380161279057013747299307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16220214573099253218103765 380161279057013747299307)
                  ·
                    rfl

theorem cell23_6663253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_6663253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663253 prefixEnd_6663253 := by exact prefixLift 6663253
  have htrace : WordTrace (prefixWord ++ tailWord_6663253) baseStart_6663253 baseEnd_6663253 := by
    simpa [prefixWord, tailWord_6663253, baseEnd_6663253] using wordTrace_append hprefix tailTrace_6663253
  have hstable : (prefixWord ++ tailWord_6663253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663253).length < 2 ^ (prefixWord ++ tailWord_6663253).sum := by decide
  have hdescent : baseEnd_6663253 < baseStart_6663253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663263 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_6663263 : Nat := 118140960795 + 6663263 * 2 ^ 59
def prefixEnd_6663263 : Nat := 4983230072969 + 3 ^ 40 * 6663263 * 2
def baseEnd_6663263 : Nat := 3421456646319668686568717

theorem tailTrace_6663263 : CollatzResearch.WordTrace tailWord_6663263 prefixEnd_6663263 3421456646319668686568717 := by
  unfold tailWord_6663263
  simp only [CollatzResearch.WordTrace]
  refine ⟨243029167259143620565122443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162019444839429080376748295 243029167259143620565122443)
  ·
    refine ⟨364543750888715430847683665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243029167259143620565122443 364543750888715430847683665)
    ·
      refine ⟨273407813166536573135762749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364543750888715430847683665 273407813166536573135762749)
      ·
        refine ⟨102527929937451214925911031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273407813166536573135762749 102527929937451214925911031)
        ·
          refine ⟨153791894906176822388866547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102527929937451214925911031 153791894906176822388866547)
          ·
            refine ⟨230687842359265233583299821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153791894906176822388866547 230687842359265233583299821)
            ·
              refine ⟨86507940884724462593737433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230687842359265233583299821 86507940884724462593737433)
              ·
                refine ⟨64880955663543346945303075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86507940884724462593737433 64880955663543346945303075)
                ·
                  refine ⟨97321433495315020417954613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64880955663543346945303075 97321433495315020417954613)
                  ·
                    refine ⟨9123884390185783164183245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97321433495315020417954613 9123884390185783164183245)
                    ·
                      refine ⟨3421456646319668686568717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123884390185783164183245 3421456646319668686568717)
                      ·
                        rfl

theorem cell23_6663263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_6663263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663263 prefixEnd_6663263 := by exact prefixLift 6663263
  have htrace : WordTrace (prefixWord ++ tailWord_6663263) baseStart_6663263 baseEnd_6663263 := by
    simpa [prefixWord, tailWord_6663263, baseEnd_6663263] using wordTrace_append hprefix tailTrace_6663263
  have hstable : (prefixWord ++ tailWord_6663263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663263).length < 2 ^ (prefixWord ++ tailWord_6663263).sum := by decide
  have hdescent : baseEnd_6663263 < baseStart_6663263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663293 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_6663293 : Nat := 118140960795 + 6663293 * 2 ^ 59
def prefixEnd_6663293 : Nat := 4983230072969 + 3 ^ 40 * 6663293 * 2
def baseEnd_6663293 : Nat := 3421472050739303569193579

theorem tailTrace_6663293 : CollatzResearch.WordTrace tailWord_6663293 prefixEnd_6663293 3421472050739303569193579 := by
  unfold tailWord_6663293
  simp only [CollatzResearch.WordTrace]
  refine ⟨243030261449034935688714533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162020174299356623792476355 243030261449034935688714533)
  ·
    refine ⟨45568174021694050441633975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243030261449034935688714533 45568174021694050441633975)
    ·
      refine ⟨68352261032541075662450963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45568174021694050441633975 68352261032541075662450963)
      ·
        refine ⟨102528391548811613493676445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68352261032541075662450963 102528391548811613493676445)
        ·
          refine ⟨38448146830804355060128667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102528391548811613493676445 38448146830804355060128667)
          ·
            refine ⟨57672220246206532590193001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38448146830804355060128667 57672220246206532590193001)
            ·
              refine ⟨43254165184654899442644751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57672220246206532590193001 43254165184654899442644751)
              ·
                refine ⟨64881247776982349163967127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43254165184654899442644751 64881247776982349163967127)
                ·
                  refine ⟨97321871665473523745950691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64881247776982349163967127 97321871665473523745950691)
                  ·
                    refine ⟨145982807498210285618926037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97321871665473523745950691 145982807498210285618926037)
                    ·
                      refine ⟨3421472050739303569193579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145982807498210285618926037 3421472050739303569193579)
                      ·
                        rfl

theorem cell23_6663293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_6663293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663293 prefixEnd_6663293 := by exact prefixLift 6663293
  have htrace : WordTrace (prefixWord ++ tailWord_6663293) baseStart_6663293 baseEnd_6663293 := by
    simpa [prefixWord, tailWord_6663293, baseEnd_6663293] using wordTrace_append hprefix tailTrace_6663293
  have hstable : (prefixWord ++ tailWord_6663293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663293).length < 2 ^ (prefixWord ++ tailWord_6663293).sum := by decide
  have hdescent : baseEnd_6663293 < baseStart_6663293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663320 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6663320 : Nat := 118140960795 + 6663320 * 2 ^ 59
def prefixEnd_6663320 : Nat := 4983230072969 + 3 ^ 40 * 6663320 * 2
def baseEnd_6663320 : Nat := 3421485914716974963555955

theorem tailTrace_6663320 : CollatzResearch.WordTrace tailWord_6663320 prefixEnd_6663320 3421485914716974963555955 := by
  unfold tailWord_6663320
  simp only [CollatzResearch.WordTrace]
  refine ⟨121515623109968559649973707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162020830813291412866631609 121515623109968559649973707)
  ·
    refine ⟨182273434664952839474960561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121515623109968559649973707 182273434664952839474960561)
    ·
      refine ⟨136705075998714629606220421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182273434664952839474960561 136705075998714629606220421)
      ·
        refine ⟨25632201749758993051166329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136705075998714629606220421 25632201749758993051166329)
        ·
          refine ⟨19224151312319244788374747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25632201749758993051166329 19224151312319244788374747)
          ·
            refine ⟨28836226968478867182562121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19224151312319244788374747 28836226968478867182562121)
            ·
              refine ⟨21627170226359150386921591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28836226968478867182562121 21627170226359150386921591)
              ·
                refine ⟨32440755339538725580382387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21627170226359150386921591 32440755339538725580382387)
                ·
                  refine ⟨48661133009308088370573581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32440755339538725580382387 48661133009308088370573581)
                  ·
                    refine ⟨18247924878490533138965093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48661133009308088370573581 18247924878490533138965093)
                    ·
                      refine ⟨3421485914716974963555955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18247924878490533138965093 3421485914716974963555955)
                      ·
                        rfl

theorem cell23_6663320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6663320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663320 prefixEnd_6663320 := by exact prefixLift 6663320
  have htrace : WordTrace (prefixWord ++ tailWord_6663320) baseStart_6663320 baseEnd_6663320 := by
    simpa [prefixWord, tailWord_6663320, baseEnd_6663320] using wordTrace_append hprefix tailTrace_6663320
  have hstable : (prefixWord ++ tailWord_6663320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663320).length < 2 ^ (prefixWord ++ tailWord_6663320).sum := by decide
  have hdescent : baseEnd_6663320 < baseStart_6663320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663343 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 8]
def baseStart_6663343 : Nat := 118140960795 + 6663343 * 2 ^ 59
def prefixEnd_6663343 : Nat := 4983230072969 + 3 ^ 40 * 6663343 * 2
def baseEnd_6663343 : Nat := 380166413863558708174261

theorem tailTrace_6663343 : CollatzResearch.WordTrace tailWord_6663343 prefixEnd_6663343 380166413863558708174261 := by
  unfold tailWord_6663343
  simp only [CollatzResearch.WordTrace]
  refine ⟨243032085098853794228034683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162021390065902529485356455 243032085098853794228034683)
  ·
    refine ⟨364548127648280691342052025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243032085098853794228034683 364548127648280691342052025)
    ·
      refine ⟨273411095736210518506539019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364548127648280691342052025 273411095736210518506539019)
      ·
        refine ⟨410116643604315777759808529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273411095736210518506539019 410116643604315777759808529)
        ·
          refine ⟨307587482703236833319856397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410116643604315777759808529 307587482703236833319856397)
          ·
            refine ⟨115345306013713812494946149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307587482703236833319856397 115345306013713812494946149)
            ·
              refine ⟨21627244877571339842802403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115345306013713812494946149 21627244877571339842802403)
              ·
                refine ⟨32440867316357009764203605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21627244877571339842802403 32440867316357009764203605)
                ·
                  refine ⟨380166413863558708174261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32440867316357009764203605 380166413863558708174261)
                  ·
                    rfl

theorem cell23_6663343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 8].length) (baseStart_6663343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663343 prefixEnd_6663343 := by exact prefixLift 6663343
  have htrace : WordTrace (prefixWord ++ tailWord_6663343) baseStart_6663343 baseEnd_6663343 := by
    simpa [prefixWord, tailWord_6663343, baseEnd_6663343] using wordTrace_append hprefix tailTrace_6663343
  have hstable : (prefixWord ++ tailWord_6663343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663343).length < 2 ^ (prefixWord ++ tailWord_6663343).sum := by decide
  have hdescent : baseEnd_6663343 < baseStart_6663343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663347 : List Nat := [1, 1, 1, 2, 3, 2, 2, 6, 1, 4]
def baseStart_6663347 : Nat := 118140960795 + 6663347 * 2 ^ 59
def prefixEnd_6663347 : Nat := 4983230072969 + 3 ^ 40 * 6663347 * 2
def baseEnd_6663347 : Nat := 1140499926231548785972777

theorem tailTrace_6663347 : CollatzResearch.WordTrace tailWord_6663347 prefixEnd_6663347 1140499926231548785972777 := by
  unfold tailWord_6663347
  simp only [CollatzResearch.WordTrace]
  refine ⟨243032230990839302911180295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162021487327226201940786863 243032230990839302911180295)
  ·
    refine ⟨364548346486258954366770443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243032230990839302911180295 364548346486258954366770443)
    ·
      refine ⟨546822519729388431550155665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364548346486258954366770443 546822519729388431550155665)
      ·
        refine ⟨410116889797041323662616749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546822519729388431550155665 410116889797041323662616749)
        ·
          refine ⟨153793833673890496373481281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410116889797041323662616749 153793833673890496373481281)
          ·
            refine ⟨115345375255417872280110961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153793833673890496373481281 115345375255417872280110961)
            ·
              refine ⟨86509031441563404210083221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115345375255417872280110961 86509031441563404210083221)
              ·
                refine ⟨4055110848823284572347651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86509031441563404210083221 4055110848823284572347651)
                ·
                  refine ⟨6082666273234926858521477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055110848823284572347651 6082666273234926858521477)
                  ·
                    refine ⟨1140499926231548785972777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6082666273234926858521477 1140499926231548785972777)
                    ·
                      rfl

theorem cell23_6663347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 1, 4].length) (baseStart_6663347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663347 prefixEnd_6663347 := by exact prefixLift 6663347
  have htrace : WordTrace (prefixWord ++ tailWord_6663347) baseStart_6663347 baseEnd_6663347 := by
    simpa [prefixWord, tailWord_6663347, baseEnd_6663347] using wordTrace_append hprefix tailTrace_6663347
  have hstable : (prefixWord ++ tailWord_6663347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663347).length < 2 ^ (prefixWord ++ tailWord_6663347).sum := by decide
  have hdescent : baseEnd_6663347 < baseStart_6663347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663374 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_6663374 : Nat := 118140960795 + 6663374 * 2 ^ 59
def prefixEnd_6663374 : Nat := 4983230072969 + 3 ^ 40 * 6663374 * 2
def baseEnd_6663374 : Nat := 3421513642672317752280707

theorem tailTrace_6663374 : CollatzResearch.WordTrace tailWord_6663374 prefixEnd_6663374 3421513642672317752280707 := by
  unfold tailWord_6663374
  simp only [CollatzResearch.WordTrace]
  refine ⟨30379151970217685815301647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162022143841160991014942117 30379151970217685815301647)
  ·
    refine ⟨45568727955326528722952471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30379151970217685815301647 45568727955326528722952471)
    ·
      refine ⟨68353091932989793084428707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45568727955326528722952471 68353091932989793084428707)
      ·
        refine ⟨102529637899484689626643061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68353091932989793084428707 102529637899484689626643061)
        ·
          refine ⟨9612153553076689652497787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102529637899484689626643061 9612153553076689652497787)
          ·
            refine ⟨14418230329615034478746681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612153553076689652497787 14418230329615034478746681)
            ·
              refine ⟨10813672747211275859060011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14418230329615034478746681 10813672747211275859060011)
              ·
                refine ⟨16220509120816913788590017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10813672747211275859060011 16220509120816913788590017)
                ·
                  refine ⟨12165381840612685341442513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16220509120816913788590017 12165381840612685341442513)
                  ·
                    refine ⟨9124036380459514006081885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12165381840612685341442513 9124036380459514006081885)
                    ·
                      refine ⟨3421513642672317752280707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9124036380459514006081885 3421513642672317752280707)
                      ·
                        rfl

theorem cell23_6663374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_6663374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663374 prefixEnd_6663374 := by exact prefixLift 6663374
  have htrace : WordTrace (prefixWord ++ tailWord_6663374) baseStart_6663374 baseEnd_6663374 := by
    simpa [prefixWord, tailWord_6663374, baseEnd_6663374] using wordTrace_append hprefix tailTrace_6663374
  have hstable : (prefixWord ++ tailWord_6663374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663374).length < 2 ^ (prefixWord ++ tailWord_6663374).sum := by decide
  have hdescent : baseEnd_6663374 < baseStart_6663374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663450 : List Nat := [3, 1, 1, 3, 3, 2, 10]
def baseStart_6663450 : Nat := 118140960795 + 6663450 * 2 ^ 59
def prefixEnd_6663450 : Nat := 4983230072969 + 3 ^ 40 * 6663450 * 2
def baseEnd_6663450 : Nat := 42241390953111845122597

theorem tailTrace_6663450 : CollatzResearch.WordTrace tailWord_6663450 prefixEnd_6663450 42241390953111845122597 := by
  unfold tailWord_6663450
  simp only [CollatzResearch.WordTrace]
  refine ⟨60758996927366537875544951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162023991806310767668119869 60758996927366537875544951)
  ·
    refine ⟨91138495391049806813317427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60758996927366537875544951 91138495391049806813317427)
    ·
      refine ⟨136707743086574710219976141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91138495391049806813317427 136707743086574710219976141)
      ·
        refine ⟨51265403657465516332491053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136707743086574710219976141 51265403657465516332491053)
        ·
          refine ⟨19224526371549568624684145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51265403657465516332491053 19224526371549568624684145)
          ·
            refine ⟨14418394778662176468513109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19224526371549568624684145 14418394778662176468513109)
            ·
              refine ⟨42241390953111845122597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14418394778662176468513109 42241390953111845122597)
              ·
                rfl

theorem cell23_6663450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 10].length) (baseStart_6663450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663450 prefixEnd_6663450 := by exact prefixLift 6663450
  have htrace : WordTrace (prefixWord ++ tailWord_6663450) baseStart_6663450 baseEnd_6663450 := by
    simpa [prefixWord, tailWord_6663450, baseEnd_6663450] using wordTrace_append hprefix tailTrace_6663450
  have hstable : (prefixWord ++ tailWord_6663450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663450).length < 2 ^ (prefixWord ++ tailWord_6663450).sum := by decide
  have hdescent : baseEnd_6663450 < baseStart_6663450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663461 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 3, 2, 2]
def baseStart_6663461 : Nat := 118140960795 + 6663461 * 2 ^ 59
def prefixEnd_6663461 : Nat := 4983230072969 + 3 ^ 40 * 6663461 * 2
def baseEnd_6663461 : Nat := 3421558315489258911892807

theorem tailTrace_6663461 : CollatzResearch.WordTrace tailWord_6663461 prefixEnd_6663461 3421558315489258911892807 := by
  unfold tailWord_6663461
  simp only [CollatzResearch.WordTrace]
  refine ⟨243036388912426300380830237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162024259274950866920553491 243036388912426300380830237)
  ·
    refine ⟨91138645842159862642811339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243036388912426300380830237 91138645842159862642811339)
    ·
      refine ⟨136707968763239793964217009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91138645842159862642811339 136707968763239793964217009)
      ·
        refine ⟨102530976572429845473162757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136707968763239793964217009 102530976572429845473162757)
        ·
          refine ⟨19224558107330596026218017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102530976572429845473162757 19224558107330596026218017)
          ·
            refine ⟨14418418580497947019663513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19224558107330596026218017 14418418580497947019663513)
            ·
              refine ⟨10813813935373460264747635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14418418580497947019663513 10813813935373460264747635)
              ·
                refine ⟨16220720903060190397121453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10813813935373460264747635 16220720903060190397121453)
                ·
                  refine ⟨6082770338647571398920545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16220720903060190397121453 6082770338647571398920545)
                  ·
                    refine ⟨4562077753985678549190409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6082770338647571398920545 4562077753985678549190409)
                    ·
                      refine ⟨3421558315489258911892807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562077753985678549190409 3421558315489258911892807)
                      ·
                        rfl

theorem cell23_6663461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_6663461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663461 prefixEnd_6663461 := by exact prefixLift 6663461
  have htrace : WordTrace (prefixWord ++ tailWord_6663461) baseStart_6663461 baseEnd_6663461 := by
    simpa [prefixWord, tailWord_6663461, baseEnd_6663461] using wordTrace_append hprefix tailTrace_6663461
  have hstable : (prefixWord ++ tailWord_6663461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663461).length < 2 ^ (prefixWord ++ tailWord_6663461).sum := by decide
  have hdescent : baseEnd_6663461 < baseStart_6663461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663474 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_6663474 : Nat := 118140960795 + 6663474 * 2 ^ 59
def prefixEnd_6663474 : Nat := 4983230072969 + 3 ^ 40 * 6663474 * 2
def baseEnd_6663474 : Nat := 3421564990737767361030247

theorem tailTrace_6663474 : CollatzResearch.WordTrace tailWord_6663474 prefixEnd_6663474 3421564990737767361030247 := by
  unfold tailWord_6663474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60759215765344800900263369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162024575374252802400702317 60759215765344800900263369)
  ·
    refine ⟨45569411824008600675197527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60759215765344800900263369 45569411824008600675197527)
    ·
      refine ⟨68354117736012901012796291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45569411824008600675197527 68354117736012901012796291)
      ·
        refine ⟨102531176604019351519194437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68354117736012901012796291 102531176604019351519194437)
        ·
          refine ⟨19224595613253628409848957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102531176604019351519194437 19224595613253628409848957)
          ·
            refine ⟨7209223354970110653693359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19224595613253628409848957 7209223354970110653693359)
            ·
              refine ⟨10813835032455165980540039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209223354970110653693359 10813835032455165980540039)
              ·
                refine ⟨16220752548682748970810059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10813835032455165980540039 16220752548682748970810059)
                ·
                  refine ⟨24331128823024123456215089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16220752548682748970810059 24331128823024123456215089)
                  ·
                    refine ⟨18248346617268092592161317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24331128823024123456215089 18248346617268092592161317)
                    ·
                      refine ⟨3421564990737767361030247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18248346617268092592161317 3421564990737767361030247)
                      ·
                        rfl

theorem cell23_6663474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_6663474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663474 prefixEnd_6663474 := by exact prefixLift 6663474
  have htrace : WordTrace (prefixWord ++ tailWord_6663474) baseStart_6663474 baseEnd_6663474 := by
    simpa [prefixWord, tailWord_6663474, baseEnd_6663474] using wordTrace_append hprefix tailTrace_6663474
  have hstable : (prefixWord ++ tailWord_6663474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663474).length < 2 ^ (prefixWord ++ tailWord_6663474).sum := by decide
  have hdescent : baseEnd_6663474 < baseStart_6663474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663478 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6663478 : Nat := 118140960795 + 6663478 * 2 ^ 59
def prefixEnd_6663478 : Nat := 4983230072969 + 3 ^ 40 * 6663478 * 2
def baseEnd_6663478 : Nat := 3421567044660385345380229

theorem tailTrace_6663478 : CollatzResearch.WordTrace tailWord_6663478 prefixEnd_6663478 3421567044660385345380229 := by
  unfold tailWord_6663478
  simp only [CollatzResearch.WordTrace]
  refine ⟨15189813059585294517762443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162024672635576474856132725 15189813059585294517762443)
  ·
    refine ⟨22784719589377941776643665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15189813059585294517762443 22784719589377941776643665)
    ·
      refine ⟨17088539692033456332482749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22784719589377941776643665 17088539692033456332482749)
      ·
        refine ⟨6408202384512546124681031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17088539692033456332482749 6408202384512546124681031)
        ·
          refine ⟨9612303576768819187021547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6408202384512546124681031 9612303576768819187021547)
          ·
            refine ⟨14418455365153228780532321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612303576768819187021547 14418455365153228780532321)
            ·
              refine ⟨10813841523864921585399241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14418455365153228780532321 10813841523864921585399241)
              ·
                refine ⟨8110381142898691189049431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10813841523864921585399241 8110381142898691189049431)
                ·
                  refine ⟨12165571714348036783574147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8110381142898691189049431 12165571714348036783574147)
                  ·
                    refine ⟨18248357571522055175361221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12165571714348036783574147 18248357571522055175361221)
                    ·
                      refine ⟨3421567044660385345380229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18248357571522055175361221 3421567044660385345380229)
                      ·
                        rfl

theorem cell23_6663478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6663478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663478 prefixEnd_6663478 := by exact prefixLift 6663478
  have htrace : WordTrace (prefixWord ++ tailWord_6663478) baseStart_6663478 baseEnd_6663478 := by
    simpa [prefixWord, tailWord_6663478, baseEnd_6663478] using wordTrace_append hprefix tailTrace_6663478
  have hstable : (prefixWord ++ tailWord_6663478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663478).length < 2 ^ (prefixWord ++ tailWord_6663478).sum := by decide
  have hdescent : baseEnd_6663478 < baseStart_6663478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663481 : List Nat := [1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6663481 : Nat := 118140960795 + 6663481 * 2 ^ 59
def prefixEnd_6663481 : Nat := 4983230072969 + 3 ^ 40 * 6663481 * 2
def baseEnd_6663481 : Nat := 3421568585102348833642715

theorem tailTrace_6663481 : CollatzResearch.WordTrace tailWord_6663481 prefixEnd_6663481 3421568585102348833642715 := by
  unfold tailWord_6663481
  simp only [CollatzResearch.WordTrace]
  refine ⟨243037118372353843796558297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162024745581569229197705531 243037118372353843796558297)
  ·
    refine ⟨182277838779265382847418723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243037118372353843796558297 182277838779265382847418723)
    ·
      refine ⟨273416758168898074271128085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182277838779265382847418723 273416758168898074271128085)
      ·
        refine ⟨12816410539167097231459129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 273416758168898074271128085 12816410539167097231459129)
        ·
          refine ⟨9612307904375322923594347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12816410539167097231459129 9612307904375322923594347)
          ·
            refine ⟨14418461856562984385391521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9612307904375322923594347 14418461856562984385391521)
            ·
              refine ⟨10813846392422238289043641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14418461856562984385391521 10813846392422238289043641)
              ·
                refine ⟨8110384794316678716782731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10813846392422238289043641 8110384794316678716782731)
                ·
                  refine ⟨12165577191475018075174097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8110384794316678716782731 12165577191475018075174097)
                  ·
                    refine ⟨9124182893606263556380573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12165577191475018075174097 9124182893606263556380573)
                    ·
                      refine ⟨3421568585102348833642715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9124182893606263556380573 3421568585102348833642715)
                      ·
                        rfl

theorem cell23_6663481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6663481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663481 prefixEnd_6663481 := by exact prefixLift 6663481
  have htrace : WordTrace (prefixWord ++ tailWord_6663481) baseStart_6663481 baseEnd_6663481 := by
    simpa [prefixWord, tailWord_6663481, baseEnd_6663481] using wordTrace_append hprefix tailTrace_6663481
  have hstable : (prefixWord ++ tailWord_6663481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663481).length < 2 ^ (prefixWord ++ tailWord_6663481).sum := by decide
  have hdescent : baseEnd_6663481 < baseStart_6663481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663501 : List Nat := [1, 6, 1, 3, 2, 1, 9]
def baseStart_6663501 : Nat := 118140960795 + 6663501 * 2 ^ 59
def prefixEnd_6663501 : Nat := 4983230072969 + 3 ^ 40 * 6663501 * 2
def baseEnd_6663501 : Nat := 42241714255746157473983

theorem tailTrace_6663501 : CollatzResearch.WordTrace tailWord_6663501 prefixEnd_6663501 42241714255746157473983 := by
  unfold tailWord_6663501
  simp only [CollatzResearch.WordTrace]
  refine ⟨243037847832281387212286357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162025231888187591474857571 243037847832281387212286357)
  ·
    refine ⟨11392399117138190025575923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 243037847832281387212286357 11392399117138190025575923)
    ·
      refine ⟨17088598675707285038363885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11392399117138190025575923 17088598675707285038363885)
      ·
        refine ⟨6408224503390231889386457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17088598675707285038363885 6408224503390231889386457)
        ·
          refine ⟨4806168377542673917039843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6408224503390231889386457 4806168377542673917039843)
          ·
            refine ⟨7209252566314010875559765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806168377542673917039843 7209252566314010875559765)
            ·
              refine ⟨42241714255746157473983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7209252566314010875559765 42241714255746157473983)
              ·
                rfl

theorem cell23_6663501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 9].length) (baseStart_6663501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663501 prefixEnd_6663501 := by exact prefixLift 6663501
  have htrace : WordTrace (prefixWord ++ tailWord_6663501) baseStart_6663501 baseEnd_6663501 := by
    simpa [prefixWord, tailWord_6663501, baseEnd_6663501] using wordTrace_append hprefix tailTrace_6663501
  have hstable : (prefixWord ++ tailWord_6663501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663501).length < 2 ^ (prefixWord ++ tailWord_6663501).sum := by decide
  have hdescent : baseEnd_6663501 < baseStart_6663501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663504 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 1, 3, 2]
def baseStart_6663504 : Nat := 118140960795 + 6663504 * 2 ^ 59
def prefixEnd_6663504 : Nat := 4983230072969 + 3 ^ 40 * 6663504 * 2
def baseEnd_6663504 : Nat := 3421580395157402243655109

theorem tailTrace_6663504 : CollatzResearch.WordTrace tailWord_6663504 prefixEnd_6663504 3421580395157402243655109 := by
  unfold tailWord_6663504
  simp only [CollatzResearch.WordTrace]
  refine ⟨121518978625635259362322783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162025304834180345816430377 121518978625635259362322783)
  ·
    refine ⟨182278467938452889043484175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121518978625635259362322783 182278467938452889043484175)
    ·
      refine ⟨273417701907679333565226263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182278467938452889043484175 273417701907679333565226263)
      ·
        refine ⟨410126552861519000347839395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273417701907679333565226263 410126552861519000347839395)
        ·
          refine ⟨615189829292278500521759093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410126552861519000347839395 615189829292278500521759093)
          ·
            refine ⟨57674046496151109423914915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 615189829292278500521759093 57674046496151109423914915)
            ·
              refine ⟨86511069744226664135872373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57674046496151109423914915 86511069744226664135872373)
              ·
                refine ⟨8110412788521249762738035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86511069744226664135872373 8110412788521249762738035)
                ·
                  refine ⟨12165619182781874644107053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8110412788521249762738035 12165619182781874644107053)
                  ·
                    refine ⟨4562107193543202991540145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12165619182781874644107053 4562107193543202991540145)
                    ·
                      refine ⟨3421580395157402243655109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562107193543202991540145 3421580395157402243655109)
                      ·
                        rfl

theorem cell23_6663504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 3, 2].length) (baseStart_6663504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663504 prefixEnd_6663504 := by exact prefixLift 6663504
  have htrace : WordTrace (prefixWord ++ tailWord_6663504) baseStart_6663504 baseEnd_6663504 := by
    simpa [prefixWord, tailWord_6663504, baseEnd_6663504] using wordTrace_append hprefix tailTrace_6663504
  have hstable : (prefixWord ++ tailWord_6663504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663504).length < 2 ^ (prefixWord ++ tailWord_6663504).sum := by decide
  have hdescent : baseEnd_6663504 < baseStart_6663504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663600 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_6663600 : Nat := 118140960795 + 6663600 * 2 ^ 59
def prefixEnd_6663600 : Nat := 4983230072969 + 3 ^ 40 * 6663600 * 2
def baseEnd_6663600 : Nat := 1140543229766744622684889

theorem tailTrace_6663600 : CollatzResearch.WordTrace tailWord_6663600 prefixEnd_6663600 1140543229766744622684889 := by
  unfold tailWord_6663600
  simp only [CollatzResearch.WordTrace]
  refine ⟨121520729329461363560070127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162027639105948484746760169 121520729329461363560070127)
  ·
    refine ⟨182281093994192045340105191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121520729329461363560070127 182281093994192045340105191)
    ·
      refine ⟨273421640991288068010157787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182281093994192045340105191 273421640991288068010157787)
      ·
        refine ⟨410132461486932102015236681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273421640991288068010157787 410132461486932102015236681)
        ·
          refine ⟨307599346115199076511427511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410132461486932102015236681 307599346115199076511427511)
          ·
            refine ⟨461399019172798614767141267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307599346115199076511427511 461399019172798614767141267)
            ·
              refine ⟨692098528759197922150711901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461399019172798614767141267 692098528759197922150711901)
              ·
                refine ⟨259536948284699220806516963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692098528759197922150711901 259536948284699220806516963)
                ·
                  refine ⟨389305422427048831209775445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259536948284699220806516963 389305422427048831209775445)
                  ·
                    refine ⟨1140543229766744622684889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 389305422427048831209775445 1140543229766744622684889)
                    ·
                      rfl

theorem cell23_6663600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_6663600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663600 prefixEnd_6663600 := by exact prefixLift 6663600
  have htrace : WordTrace (prefixWord ++ tailWord_6663600) baseStart_6663600 baseEnd_6663600 := by
    simpa [prefixWord, tailWord_6663600, baseEnd_6663600] using wordTrace_append hprefix tailTrace_6663600
  have hstable : (prefixWord ++ tailWord_6663600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663600).length < 2 ^ (prefixWord ++ tailWord_6663600).sum := by decide
  have hdescent : baseEnd_6663600 < baseStart_6663600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663607 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_6663607 : Nat := 118140960795 + 6663607 * 2 ^ 59
def prefixEnd_6663607 : Nat := 4983230072969 + 3 ^ 40 * 6663607 * 2
def baseEnd_6663607 : Nat := 3421633283664815340667135

theorem tailTrace_6663607 : CollatzResearch.WordTrace tailWord_6663607 prefixEnd_6663607 3421633283664815340667135 := by
  unfold tailWord_6663607
  simp only [CollatzResearch.WordTrace]
  refine ⟨243041713969897367315645075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162027809313264911543763383 243041713969897367315645075)
  ·
    refine ⟨364562570954846050973467613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243041713969897367315645075 364562570954846050973467613)
    ·
      refine ⟨136710964108067269115050355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364562570954846050973467613 136710964108067269115050355)
      ·
        refine ⟨205066446162100903672575533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136710964108067269115050355 205066446162100903672575533)
        ·
          refine ⟨76899917310787838877215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205066446162100903672575533 76899917310787838877215825)
          ·
            refine ⟨57674937983090879157911869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76899917310787838877215825 57674937983090879157911869)
            ·
              refine ⟨21628101743659079684216951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57674937983090879157911869 21628101743659079684216951)
              ·
                refine ⟨32442152615488619526325427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21628101743659079684216951 32442152615488619526325427)
                ·
                  refine ⟨48663228923232929289488141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32442152615488619526325427 48663228923232929289488141)
                  ·
                    refine ⟨18248710846212348483558053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48663228923232929289488141 18248710846212348483558053)
                    ·
                      refine ⟨3421633283664815340667135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18248710846212348483558053 3421633283664815340667135)
                      ·
                        rfl

theorem cell23_6663607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_6663607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663607 prefixEnd_6663607 := by exact prefixLift 6663607
  have htrace : WordTrace (prefixWord ++ tailWord_6663607) baseStart_6663607 baseEnd_6663607 := by
    simpa [prefixWord, tailWord_6663607, baseEnd_6663607] using wordTrace_append hprefix tailTrace_6663607
  have hstable : (prefixWord ++ tailWord_6663607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663607).length < 2 ^ (prefixWord ++ tailWord_6663607).sum := by decide
  have hdescent : baseEnd_6663607 < baseStart_6663607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663624 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_6663624 : Nat := 118140960795 + 6663624 * 2 ^ 59
def prefixEnd_6663624 : Nat := 4983230072969 + 3 ^ 40 * 6663624 * 2
def baseEnd_6663624 : Nat := 3421642012835941774154557

theorem tailTrace_6663624 : CollatzResearch.WordTrace tailWord_6663624 prefixEnd_6663624 3421642012835941774154557 := by
  unfold tailWord_6663624
  simp only [CollatzResearch.WordTrace]
  refine ⟨121521167005417889609506963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162028222673890519479342617 121521167005417889609506963)
  ·
    refine ⟨182281750508126834414260445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121521167005417889609506963 182281750508126834414260445)
    ·
      refine ⟨68355656440547562905347667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182281750508126834414260445 68355656440547562905347667)
      ·
        refine ⟨102533484660821344358021501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68355656440547562905347667 102533484660821344358021501)
        ·
          refine ⟨38450056747808004134258063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102533484660821344358021501 38450056747808004134258063)
          ·
            refine ⟨57675085121712006201387095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38450056747808004134258063 57675085121712006201387095)
            ·
              refine ⟨86512627682568009302080643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57675085121712006201387095 86512627682568009302080643)
              ·
                refine ⟨129768941523852013953120965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86512627682568009302080643 129768941523852013953120965)
                ·
                  refine ⟨24331676535722252616210181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129768941523852013953120965 24331676535722252616210181)
                  ·
                    refine ⟨4562189350447922365539409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24331676535722252616210181 4562189350447922365539409)
                    ·
                      refine ⟨3421642012835941774154557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562189350447922365539409 3421642012835941774154557)
                      ·
                        rfl

theorem cell23_6663624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_6663624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663624 prefixEnd_6663624 := by exact prefixLift 6663624
  have htrace : WordTrace (prefixWord ++ tailWord_6663624) baseStart_6663624 baseEnd_6663624 := by
    simpa [prefixWord, tailWord_6663624, baseEnd_6663624] using wordTrace_append hprefix tailTrace_6663624
  have hstable : (prefixWord ++ tailWord_6663624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663624).length < 2 ^ (prefixWord ++ tailWord_6663624).sum := by decide
  have hdescent : baseEnd_6663624 < baseStart_6663624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663637 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6663637 : Nat := 118140960795 + 6663637 * 2 ^ 59
def prefixEnd_6663637 : Nat := 4983230072969 + 3 ^ 40 * 6663637 * 2
def baseEnd_6663637 : Nat := 3421648688084450223291997

theorem tailTrace_6663637 : CollatzResearch.WordTrace tailWord_6663637 prefixEnd_6663637 3421648688084450223291997 := by
  unfold tailWord_6663637
  simp only [CollatzResearch.WordTrace]
  refine ⟨243042808159788682439237165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162028538773192454959491443 243042808159788682439237165)
  ·
    refine ⟨91141053059920755914713937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243042808159788682439237165 91141053059920755914713937)
    ·
      refine ⟨68355789794940566936035453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91141053059920755914713937 68355789794940566936035453)
      ·
        refine ⟨25633421173102712601013295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68355789794940566936035453 25633421173102712601013295)
        ·
          refine ⟨38450131759654068901519943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25633421173102712601013295 38450131759654068901519943)
          ·
            refine ⟨57675197639481103352279915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38450131759654068901519943 57675197639481103352279915)
            ·
              refine ⟨86512796459221655028419873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57675197639481103352279915 86512796459221655028419873)
              ·
                refine ⟨64884597344416241271314905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86512796459221655028419873 64884597344416241271314905)
                ·
                  refine ⟨48663448008312180953486179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64884597344416241271314905 48663448008312180953486179)
                  ·
                    refine ⟨72995172012468271430229269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48663448008312180953486179 72995172012468271430229269)
                    ·
                      refine ⟨3421648688084450223291997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72995172012468271430229269 3421648688084450223291997)
                      ·
                        rfl

theorem cell23_6663637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6663637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663637 prefixEnd_6663637 := by exact prefixLift 6663637
  have htrace : WordTrace (prefixWord ++ tailWord_6663637) baseStart_6663637 baseEnd_6663637 := by
    simpa [prefixWord, tailWord_6663637, baseEnd_6663637] using wordTrace_append hprefix tailTrace_6663637
  have hstable : (prefixWord ++ tailWord_6663637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663637).length < 2 ^ (prefixWord ++ tailWord_6663637).sum := by decide
  have hdescent : baseEnd_6663637 < baseStart_6663637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663737 : List Nat := [1, 2, 1, 5, 1, 13]
def baseStart_6663737 : Nat := 118140960795 + 6663737 * 2 ^ 59
def prefixEnd_6663737 : Nat := 4983230072969 + 3 ^ 40 * 6663737 * 2
def baseEnd_6663737 : Nat := 14081070107612756510459

theorem tailTrace_6663737 : CollatzResearch.WordTrace tailWord_6663737 prefixEnd_6663737 14081070107612756510459 := by
  unfold tailWord_6663737
  simp only [CollatzResearch.WordTrace]
  refine ⟨243046455459426399517877465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162030970306284266345251643 243046455459426399517877465)
  ·
    refine ⟨182284841594569799638408099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243046455459426399517877465 182284841594569799638408099)
    ·
      refine ⟨273427262391854699457612149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182284841594569799638408099 273427262391854699457612149)
      ·
        refine ⟨25633805849236378074151139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273427262391854699457612149 25633805849236378074151139)
        ·
          refine ⟨38450708773854567111226709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25633805849236378074151139 38450708773854567111226709)
          ·
            refine ⟨14081070107612756510459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38450708773854567111226709 14081070107612756510459)
            ·
              rfl

theorem cell23_6663737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 13].length) (baseStart_6663737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663737 prefixEnd_6663737 := by exact prefixLift 6663737
  have htrace : WordTrace (prefixWord ++ tailWord_6663737) baseStart_6663737 baseEnd_6663737 := by
    simpa [prefixWord, tailWord_6663737, baseEnd_6663737] using wordTrace_append hprefix tailTrace_6663737
  have hstable : (prefixWord ++ tailWord_6663737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663737).length < 2 ^ (prefixWord ++ tailWord_6663737).sum := by decide
  have hdescent : baseEnd_6663737 < baseStart_6663737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663781 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_6663781 : Nat := 118140960795 + 6663781 * 2 ^ 59
def prefixEnd_6663781 : Nat := 4983230072969 + 3 ^ 40 * 6663781 * 2
def baseEnd_6663781 : Nat := 3421722629298697659891335

theorem tailTrace_6663781 : CollatzResearch.WordTrace tailWord_6663781 prefixEnd_6663781 3421722629298697659891335 := by
  unfold tailWord_6663781
  simp only [CollatzResearch.WordTrace]
  refine ⟨243048060271266995032479197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162032040180844663354986131 243048060271266995032479197)
  ·
    refine ⟨91143022601725123137179699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243048060271266995032479197 91143022601725123137179699)
    ·
      refine ⟨136714533902587684705769549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91143022601725123137179699 136714533902587684705769549)
      ·
        refine ⟨51267950213470381764663581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136714533902587684705769549 51267950213470381764663581)
        ·
          refine ⟨19225481330051393161748843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51267950213470381764663581 19225481330051393161748843)
          ·
            refine ⟨28838221995077089742623265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19225481330051393161748843 28838221995077089742623265)
            ·
              refine ⟨21628666496307817306967449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28838221995077089742623265 21628666496307817306967449)
              ·
                refine ⟨16221499872230862980225587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21628666496307817306967449 16221499872230862980225587)
                ·
                  refine ⟨24332249808346294470338381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16221499872230862980225587 24332249808346294470338381)
                  ·
                    refine ⟨9124593678129860426376893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24332249808346294470338381 9124593678129860426376893)
                    ·
                      refine ⟨3421722629298697659891335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9124593678129860426376893 3421722629298697659891335)
                      ·
                        rfl

theorem cell23_6663781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_6663781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663781 prefixEnd_6663781 := by exact prefixLift 6663781
  have htrace : WordTrace (prefixWord ++ tailWord_6663781) baseStart_6663781 baseEnd_6663781 := by
    simpa [prefixWord, tailWord_6663781, baseEnd_6663781] using wordTrace_append hprefix tailTrace_6663781
  have hstable : (prefixWord ++ tailWord_6663781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663781).length < 2 ^ (prefixWord ++ tailWord_6663781).sum := by decide
  have hdescent : baseEnd_6663781 < baseStart_6663781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663815 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 2, 1, 3]
def baseStart_6663815 : Nat := 118140960795 + 6663815 * 2 ^ 59
def prefixEnd_6663815 : Nat := 4983230072969 + 3 ^ 40 * 6663815 * 2
def baseEnd_6663815 : Nat := 3421740087640950526866179

theorem tailTrace_6663815 : CollatzResearch.WordTrace tailWord_6663815 prefixEnd_6663815 3421740087640950526866179 := by
  unfold tailWord_6663815
  simp only [CollatzResearch.WordTrace]
  refine ⟨243049300353143818839216899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162032866902095879226144599 243049300353143818839216899)
  ·
    refine ⟨364573950529715728258825349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243049300353143818839216899 364573950529715728258825349)
    ·
      refine ⟨68357615724321699048529753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364573950529715728258825349 68357615724321699048529753)
      ·
        refine ⟨51268211793241274286397315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68357615724321699048529753 51268211793241274286397315)
        ·
          refine ⟨76902317689861911429595973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51268211793241274286397315 76902317689861911429595973)
          ·
            refine ⟨14419184566849108393049245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76902317689861911429595973 14419184566849108393049245)
            ·
              refine ⟨5407194212568415647393467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14419184566849108393049245 5407194212568415647393467)
              ·
                refine ⟨8110791318852623471090201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407194212568415647393467 8110791318852623471090201)
                ·
                  refine ⟨6083093489139467603317651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8110791318852623471090201 6083093489139467603317651)
                  ·
                    refine ⟨9124640233709201404976477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6083093489139467603317651 9124640233709201404976477)
                    ·
                      refine ⟨3421740087640950526866179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9124640233709201404976477 3421740087640950526866179)
                      ·
                        rfl

theorem cell23_6663815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_6663815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663815 prefixEnd_6663815 := by exact prefixLift 6663815
  have htrace : WordTrace (prefixWord ++ tailWord_6663815) baseStart_6663815 baseEnd_6663815 := by
    simpa [prefixWord, tailWord_6663815, baseEnd_6663815] using wordTrace_append hprefix tailTrace_6663815
  have hstable : (prefixWord ++ tailWord_6663815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663815).length < 2 ^ (prefixWord ++ tailWord_6663815).sum := by decide
  have hdescent : baseEnd_6663815 < baseStart_6663815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663824 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_6663824 : Nat := 118140960795 + 6663824 * 2 ^ 59
def prefixEnd_6663824 : Nat := 4983230072969 + 3 ^ 40 * 6663824 * 2
def baseEnd_6663824 : Nat := 3421744708966840991653637

theorem tailTrace_6663824 : CollatzResearch.WordTrace tailWord_6663824 prefixEnd_6663824 3421744708966840991653637 := by
  unfold tailWord_6663824
  simp only [CollatzResearch.WordTrace]
  refine ⟨121524814305055606688147263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162033085740074142250863017 121524814305055606688147263)
  ·
    refine ⟨182287221457583410032220895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121524814305055606688147263 182287221457583410032220895)
    ·
      refine ⟨273430832186375115048331343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182287221457583410032220895 273430832186375115048331343)
      ·
        refine ⟨410146248279562672572497015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273430832186375115048331343 410146248279562672572497015)
        ·
          refine ⟨615219372419344008858745523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410146248279562672572497015 615219372419344008858745523)
          ·
            refine ⟨922829058629016013288118285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615219372419344008858745523 922829058629016013288118285)
            ·
              refine ⟨346060896985881004983044357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 922829058629016013288118285 346060896985881004983044357)
              ·
                refine ⟨64886418184852688434320817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346060896985881004983044357 64886418184852688434320817)
                ·
                  refine ⟨48664813638639516325740613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64886418184852688434320817 48664813638639516325740613)
                  ·
                    refine ⟨9124652557244909311076365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48664813638639516325740613 9124652557244909311076365)
                    ·
                      refine ⟨3421744708966840991653637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9124652557244909311076365 3421744708966840991653637)
                      ·
                        rfl

theorem cell23_6663824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_6663824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663824 prefixEnd_6663824 := by exact prefixLift 6663824
  have htrace : WordTrace (prefixWord ++ tailWord_6663824) baseStart_6663824 baseEnd_6663824 := by
    simpa [prefixWord, tailWord_6663824, baseEnd_6663824] using wordTrace_append hprefix tailTrace_6663824
  have hstable : (prefixWord ++ tailWord_6663824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663824).length < 2 ^ (prefixWord ++ tailWord_6663824).sum := by decide
  have hdescent : baseEnd_6663824 < baseStart_6663824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663841 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6663841 : Nat := 118140960795 + 6663841 * 2 ^ 59
def prefixEnd_6663841 : Nat := 4983230072969 + 3 ^ 40 * 6663841 * 2
def baseEnd_6663841 : Nat := 3421753438137967425141059

theorem tailTrace_6663841 : CollatzResearch.WordTrace tailWord_6663841 prefixEnd_6663841 3421753438137967425141059 := by
  unfold tailWord_6663841
  simp only [CollatzResearch.WordTrace]
  refine ⟨243050248651049625279663377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162033499100699750186442251 243050248651049625279663377)
  ·
    refine ⟨182287686488287218959747533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243050248651049625279663377 182287686488287218959747533)
    ·
      refine ⟨68357882433107707109905325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182287686488287218959747533 68357882433107707109905325)
      ·
        refine ⟨25634205912415390166214497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68357882433107707109905325 25634205912415390166214497)
        ·
          refine ⟨19225654434311542624660873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25634205912415390166214497 19225654434311542624660873)
          ·
            refine ⟨14419240825733656968495655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19225654434311542624660873 14419240825733656968495655)
            ·
              refine ⟨21628861238600485452743483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14419240825733656968495655 21628861238600485452743483)
              ·
                refine ⟨32443291857900728179115225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21628861238600485452743483 32443291857900728179115225)
                ·
                  refine ⟨24332468893425546134336419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32443291857900728179115225 24332468893425546134336419)
                  ·
                    refine ⟨36498703340138319201504629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24332468893425546134336419 36498703340138319201504629)
                    ·
                      refine ⟨3421753438137967425141059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36498703340138319201504629 3421753438137967425141059)
                      ·
                        rfl

theorem cell23_6663841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6663841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663841 prefixEnd_6663841 := by exact prefixLift 6663841
  have htrace : WordTrace (prefixWord ++ tailWord_6663841) baseStart_6663841 baseEnd_6663841 := by
    simpa [prefixWord, tailWord_6663841, baseEnd_6663841] using wordTrace_append hprefix tailTrace_6663841
  have hstable : (prefixWord ++ tailWord_6663841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663841).length < 2 ^ (prefixWord ++ tailWord_6663841).sum := by decide
  have hdescent : baseEnd_6663841 < baseStart_6663841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663948 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_6663948 : Nat := 118140960795 + 6663948 * 2 ^ 59
def prefixEnd_6663948 : Nat := 4983230072969 + 3 ^ 40 * 6663948 * 2
def baseEnd_6663948 : Nat := 3421808380567998506503067

theorem tailTrace_6663948 : CollatzResearch.WordTrace tailWord_6663948 prefixEnd_6663948 3421808380567998506503067 := by
  unfold tailWord_6663948
  simp only [CollatzResearch.WordTrace]
  refine ⟨121527075630830991276904249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162036100841107988369205665 121527075630830991276904249)
  ·
    refine ⟨91145306723123243457678187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121527075630830991276904249 91145306723123243457678187)
    ·
      refine ⟨136717960084684865186517281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91145306723123243457678187 136717960084684865186517281)
      ·
        refine ⟨102538470063513648889887961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136717960084684865186517281 102538470063513648889887961)
        ·
          refine ⟨76903852547635236667415971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102538470063513648889887961 76903852547635236667415971)
          ·
            refine ⟨115355778821452855001123957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76903852547635236667415971 115355778821452855001123957)
            ·
              refine ⟨10814604264511205156355371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115355778821452855001123957 10814604264511205156355371)
              ·
                refine ⟨16221906396766807734533057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10814604264511205156355371 16221906396766807734533057)
                ·
                  refine ⟨12166429797575105800899793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16221906396766807734533057 12166429797575105800899793)
                  ·
                    refine ⟨9124822348181329350674845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12166429797575105800899793 9124822348181329350674845)
                    ·
                      refine ⟨3421808380567998506503067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9124822348181329350674845 3421808380567998506503067)
                      ·
                        rfl

theorem cell23_6663948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_6663948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663948 prefixEnd_6663948 := by exact prefixLift 6663948
  have htrace : WordTrace (prefixWord ++ tailWord_6663948) baseStart_6663948 baseEnd_6663948 := by
    simpa [prefixWord, tailWord_6663948, baseEnd_6663948] using wordTrace_append hprefix tailTrace_6663948
  have hstable : (prefixWord ++ tailWord_6663948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663948).length < 2 ^ (prefixWord ++ tailWord_6663948).sum := by decide
  have hdescent : baseEnd_6663948 < baseStart_6663948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664006 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_6664006 : Nat := 118140960795 + 6664006 * 2 ^ 59
def prefixEnd_6664006 : Nat := 4983230072969 + 3 ^ 40 * 6664006 * 2
def baseEnd_6664006 : Nat := 1140612720815319759859267

theorem tailTrace_6664006 : CollatzResearch.WordTrace tailWord_6664006 prefixEnd_6664006 1140612720815319759859267 := by
  unfold tailWord_6664006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595508334232870576856871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162037511130301238972946581 7595508334232870576856871)
  ·
    refine ⟨11393262501349305865285307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7595508334232870576856871 11393262501349305865285307)
    ·
      refine ⟨17089893752023958797927961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11393262501349305865285307 17089893752023958797927961)
      ·
        refine ⟨12817420314017969098445971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17089893752023958797927961 12817420314017969098445971)
        ·
          refine ⟨19226130471026953647668957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12817420314017969098445971 19226130471026953647668957)
          ·
            refine ⟨7209798926635107617875859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19226130471026953647668957 7209798926635107617875859)
            ·
              refine ⟨10814698389952661426813789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209798926635107617875859 10814698389952661426813789)
              ·
                refine ⟨4055511896232248035055171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10814698389952661426813789 4055511896232248035055171)
                ·
                  refine ⟨6083267844348372052582757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055511896232248035055171 6083267844348372052582757)
                  ·
                    refine ⟨1140612720815319759859267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083267844348372052582757 1140612720815319759859267)
                    ·
                      rfl

theorem cell23_6664006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_6664006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664006 prefixEnd_6664006 := by exact prefixLift 6664006
  have htrace : WordTrace (prefixWord ++ tailWord_6664006) baseStart_6664006 baseEnd_6664006 := by
    simpa [prefixWord, tailWord_6664006, baseEnd_6664006] using wordTrace_append hprefix tailTrace_6664006
  have hstable : (prefixWord ++ tailWord_6664006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664006).length < 2 ^ (prefixWord ++ tailWord_6664006).sum := by decide
  have hdescent : baseEnd_6664006 < baseStart_6664006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664031 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_6664031 : Nat := 118140960795 + 6664031 * 2 ^ 59
def prefixEnd_6664031 : Nat := 4983230072969 + 3 ^ 40 * 6664031 * 2
def baseEnd_6664031 : Nat := 3421850999462321681765185

theorem tailTrace_6664031 : CollatzResearch.WordTrace tailWord_6664031 prefixEnd_6664031 3421850999462321681765185 := by
  unfold tailWord_6664031
  simp only [CollatzResearch.WordTrace]
  refine ⟨243057178520361287729079947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162038119013574191819386631 243057178520361287729079947)
  ·
    refine ⟨364585767780541931593619921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243057178520361287729079947 364585767780541931593619921)
    ·
      refine ⟨273439325835406448695214941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364585767780541931593619921 273439325835406448695214941)
      ·
        refine ⟨102539747188277418260705603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273439325835406448695214941 102539747188277418260705603)
        ·
          refine ⟨153809620782416127391058405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102539747188277418260705603 153809620782416127391058405)
          ·
            refine ⟨28839303896703023885823451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153809620782416127391058405 28839303896703023885823451)
            ·
              refine ⟨43258955845054535828735177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28839303896703023885823451 43258955845054535828735177)
              ·
                refine ⟨32444216883790901871551383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43258955845054535828735177 32444216883790901871551383)
                ·
                  refine ⟨48666325325686352807327075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32444216883790901871551383 48666325325686352807327075)
                  ·
                    refine ⟨72999487988529529210990613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48666325325686352807327075 72999487988529529210990613)
                    ·
                      refine ⟨3421850999462321681765185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72999487988529529210990613 3421850999462321681765185)
                      ·
                        rfl

theorem cell23_6664031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_6664031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664031 prefixEnd_6664031 := by exact prefixLift 6664031
  have htrace : WordTrace (prefixWord ++ tailWord_6664031) baseStart_6664031 baseEnd_6664031 := by
    simpa [prefixWord, tailWord_6664031, baseEnd_6664031] using wordTrace_append hprefix tailTrace_6664031
  have hstable : (prefixWord ++ tailWord_6664031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664031).length < 2 ^ (prefixWord ++ tailWord_6664031).sum := by decide
  have hdescent : baseEnd_6664031 < baseStart_6664031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664068 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_6664068 : Nat := 118140960795 + 6664068 * 2 ^ 59
def prefixEnd_6664068 : Nat := 4983230072969 + 3 ^ 40 * 6664068 * 2
def baseEnd_6664068 : Nat := 3421869998246538037002515

theorem tailTrace_6664068 : CollatzResearch.WordTrace tailWord_6664068 prefixEnd_6664068 3421869998246538037002515 := by
  unfold tailWord_6664068
  simp only [CollatzResearch.WordTrace]
  refine ⟨121529264010613621524088429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162039018680818162032117905 121529264010613621524088429)
  ·
    refine ⟨45573474003980108071533161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121529264010613621524088429 45573474003980108071533161)
    ·
      refine ⟨34180105502985081053649871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45573474003980108071533161 34180105502985081053649871)
      ·
        refine ⟨51270158254477621580474807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34180105502985081053649871 51270158254477621580474807)
        ·
          refine ⟨76905237381716432370712211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51270158254477621580474807 76905237381716432370712211)
          ·
            refine ⟨115357856072574648556068317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76905237381716432370712211 115357856072574648556068317)
            ·
              refine ⟨43259196027215493208525619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115357856072574648556068317 43259196027215493208525619)
              ·
                refine ⟨64888794040823239812788429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43259196027215493208525619 64888794040823239812788429)
                ·
                  refine ⟨24333297765308714929795661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64888794040823239812788429 24333297765308714929795661)
                  ·
                    refine ⟨9124986661990768098673373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24333297765308714929795661 9124986661990768098673373)
                    ·
                      refine ⟨3421869998246538037002515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9124986661990768098673373 3421869998246538037002515)
                      ·
                        rfl

theorem cell23_6664068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_6664068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664068 prefixEnd_6664068 := by exact prefixLift 6664068
  have htrace : WordTrace (prefixWord ++ tailWord_6664068) baseStart_6664068 baseEnd_6664068 := by
    simpa [prefixWord, tailWord_6664068, baseEnd_6664068] using wordTrace_append hprefix tailTrace_6664068
  have hstable : (prefixWord ++ tailWord_6664068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664068).length < 2 ^ (prefixWord ++ tailWord_6664068).sum := by decide
  have hdescent : baseEnd_6664068 < baseStart_6664068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664072 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6664072 : Nat := 118140960795 + 6664072 * 2 ^ 59
def prefixEnd_6664072 : Nat := 4983230072969 + 3 ^ 40 * 6664072 * 2
def baseEnd_6664072 : Nat := 3421872052169156021352497

theorem tailTrace_6664072 : CollatzResearch.WordTrace tailWord_6664072 prefixEnd_6664072 3421872052169156021352497 := by
  unfold tailWord_6664072
  simp only [CollatzResearch.WordTrace]
  refine ⟨121529336956606375865661235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162039115942141834487548313 121529336956606375865661235)
  ·
    refine ⟨182294005434909563798491853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121529336956606375865661235 182294005434909563798491853)
    ·
      refine ⟨68360252038091086424434445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182294005434909563798491853 68360252038091086424434445)
      ·
        refine ⟨25635094514284157409162917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68360252038091086424434445 25635094514284157409162917)
        ·
          refine ⟨4806580221428279514218047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25635094514284157409162917 4806580221428279514218047)
          ·
            refine ⟨7209870332142419271327071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806580221428279514218047 7209870332142419271327071)
            ·
              refine ⟨10814805498213628906990607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7209870332142419271327071 10814805498213628906990607)
              ·
                refine ⟨16222208247320443360485911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10814805498213628906990607 16222208247320443360485911)
                ·
                  refine ⟨24333312370980665040728867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16222208247320443360485911 24333312370980665040728867)
                  ·
                    refine ⟨36499968556470997561093301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24333312370980665040728867 36499968556470997561093301)
                    ·
                      refine ⟨3421872052169156021352497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36499968556470997561093301 3421872052169156021352497)
                      ·
                        rfl

theorem cell23_6664072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6664072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664072 prefixEnd_6664072 := by exact prefixLift 6664072
  have htrace : WordTrace (prefixWord ++ tailWord_6664072) baseStart_6664072 baseEnd_6664072 := by
    simpa [prefixWord, tailWord_6664072, baseEnd_6664072] using wordTrace_append hprefix tailTrace_6664072
  have hstable : (prefixWord ++ tailWord_6664072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664072).length < 2 ^ (prefixWord ++ tailWord_6664072).sum := by decide
  have hdescent : baseEnd_6664072 < baseStart_6664072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664081 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_6664081 : Nat := 118140960795 + 6664081 * 2 ^ 59
def prefixEnd_6664081 : Nat := 4983230072969 + 3 ^ 40 * 6664081 * 2
def baseEnd_6664081 : Nat := 3421876673495046486139955

theorem tailTrace_6664081 : CollatzResearch.WordTrace tailWord_6664081 prefixEnd_6664081 3421876673495046486139955 := by
  unfold tailWord_6664081
  simp only [CollatzResearch.WordTrace]
  refine ⟨243059002170180146268400097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162039334780120097512266731 243059002170180146268400097)
  ·
    refine ⟨182294251627635109701300073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243059002170180146268400097 182294251627635109701300073)
    ·
      refine ⟨136720688720726332275975055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182294251627635109701300073 136720688720726332275975055)
      ·
        refine ⟨205081033081089498413962583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136720688720726332275975055 205081033081089498413962583)
        ·
          refine ⟨307621549621634247620943875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205081033081089498413962583 307621549621634247620943875)
          ·
            refine ⟨461432324432451371431415813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307621549621634247620943875 461432324432451371431415813)
            ·
              refine ⟨86518560831084632143390465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461432324432451371431415813 86518560831084632143390465)
              ·
                refine ⟨64888920623313474107542849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86518560831084632143390465 64888920623313474107542849)
                ·
                  refine ⟨48666690467485105580657137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64888920623313474107542849 48666690467485105580657137)
                  ·
                    refine ⟨36500017850613829185492853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48666690467485105580657137 36500017850613829185492853)
                    ·
                      refine ⟨3421876673495046486139955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36500017850613829185492853 3421876673495046486139955)
                      ·
                        rfl

theorem cell23_6664081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_6664081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664081 prefixEnd_6664081 := by exact prefixLift 6664081
  have htrace : WordTrace (prefixWord ++ tailWord_6664081) baseStart_6664081 baseEnd_6664081 := by
    simpa [prefixWord, tailWord_6664081, baseEnd_6664081] using wordTrace_append hprefix tailTrace_6664081
  have hstable : (prefixWord ++ tailWord_6664081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664081).length < 2 ^ (prefixWord ++ tailWord_6664081).sum := by decide
  have hdescent : baseEnd_6664081 < baseStart_6664081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664138 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_6664138 : Nat := 118140960795 + 6664138 * 2 ^ 59
def prefixEnd_6664138 : Nat := 4983230072969 + 3 ^ 40 * 6664138 * 2
def baseEnd_6664138 : Nat := 3421905941892352763127193

theorem tailTrace_6664138 : CollatzResearch.WordTrace tailWord_6664138 prefixEnd_6664138 3421905941892352763127193 := by
  unfold tailWord_6664138
  simp only [CollatzResearch.WordTrace]
  refine ⟨60765270282743411250806267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162040720753982430002150045 60765270282743411250806267)
  ·
    refine ⟨91147905424115116876209401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60765270282743411250806267 91147905424115116876209401)
    ·
      refine ⟨68360929068086337657157051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91147905424115116876209401 68360929068086337657157051)
      ·
        refine ⟨102541393602129506485735577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68360929068086337657157051 102541393602129506485735577)
        ·
          refine ⟨76906045201597129864301683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102541393602129506485735577 76906045201597129864301683)
          ·
            refine ⟨115359067802395694796452525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76906045201597129864301683 115359067802395694796452525)
            ·
              refine ⟨43259650425898385548669697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115359067802395694796452525 43259650425898385548669697)
              ·
                refine ⟨32444737819423789161502273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43259650425898385548669697 32444737819423789161502273)
                ·
                  refine ⟨24333553364567841871126705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32444737819423789161502273 24333553364567841871126705)
                  ·
                    refine ⟨18250165023425881403345029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24333553364567841871126705 18250165023425881403345029)
                    ·
                      refine ⟨3421905941892352763127193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18250165023425881403345029 3421905941892352763127193)
                      ·
                        rfl

theorem cell23_6664138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_6664138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664138 prefixEnd_6664138 := by exact prefixLift 6664138
  have htrace : WordTrace (prefixWord ++ tailWord_6664138) baseStart_6664138 baseEnd_6664138 := by
    simpa [prefixWord, tailWord_6664138, baseEnd_6664138] using wordTrace_append hprefix tailTrace_6664138
  have hstable : (prefixWord ++ tailWord_6664138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664138).length < 2 ^ (prefixWord ++ tailWord_6664138).sum := by decide
  have hdescent : baseEnd_6664138 < baseStart_6664138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664142 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_6664142 : Nat := 118140960795 + 6664142 * 2 ^ 59
def prefixEnd_6664142 : Nat := 4983230072969 + 3 ^ 40 * 6664142 * 2
def baseEnd_6664142 : Nat := 3421907995814970747477175

theorem tailTrace_6664142 : CollatzResearch.WordTrace tailWord_6664142 prefixEnd_6664142 3421907995814970747477175 := by
  unfold tailWord_6664142
  simp only [CollatzResearch.WordTrace]
  refine ⟨30382653377869894210796335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162040818015306102457580453 30382653377869894210796335)
  ·
    refine ⟨45573980066804841316194503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30382653377869894210796335 45573980066804841316194503)
    ·
      refine ⟨68360970100207261974291755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45573980066804841316194503 68360970100207261974291755)
      ·
        refine ⟨102541455150310892961437633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68360970100207261974291755 102541455150310892961437633)
        ·
          refine ⟨76906091362733169721078225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102541455150310892961437633 76906091362733169721078225)
          ·
            refine ⟨57679568522049877290808669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76906091362733169721078225 57679568522049877290808669)
            ·
              refine ⟨21629838195768703984053251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57679568522049877290808669 21629838195768703984053251)
              ·
                refine ⟨32444757293653055976079877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21629838195768703984053251 32444757293653055976079877)
                ·
                  refine ⟨6083391992559947995514977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32444757293653055976079877 6083391992559947995514977)
                  ·
                    refine ⟨4562543994419960996636233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6083391992559947995514977 4562543994419960996636233)
                    ·
                      refine ⟨3421907995814970747477175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562543994419960996636233 3421907995814970747477175)
                      ·
                        rfl

theorem cell23_6664142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_6664142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664142 prefixEnd_6664142 := by exact prefixLift 6664142
  have htrace : WordTrace (prefixWord ++ tailWord_6664142) baseStart_6664142 baseEnd_6664142 := by
    simpa [prefixWord, tailWord_6664142, baseEnd_6664142] using wordTrace_append hprefix tailTrace_6664142
  have hstable : (prefixWord ++ tailWord_6664142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664142).length < 2 ^ (prefixWord ++ tailWord_6664142).sum := by decide
  have hdescent : baseEnd_6664142 < baseStart_6664142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664188 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_6664188 : Nat := 118140960795 + 6664188 * 2 ^ 59
def prefixEnd_6664188 : Nat := 4983230072969 + 3 ^ 40 * 6664188 * 2
def baseEnd_6664188 : Nat := 3421931615925077567501963

theorem tailTrace_6664188 : CollatzResearch.WordTrace tailWord_6664188 prefixEnd_6664188 3421931615925077567501963 := by
  unfold tailWord_6664188
  simp only [CollatzResearch.WordTrace]
  refine ⟨121531452390396251771272609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162041936520528335695030145 121531452390396251771272609)
  ·
    refine ⟨91148589292797188828454457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121531452390396251771272609 91148589292797188828454457)
    ·
      refine ⟨68361441969597891621340843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91148589292797188828454457 68361441969597891621340843)
      ·
        refine ⟨102542162954396837432011265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68361441969597891621340843 102542162954396837432011265)
        ·
          refine ⟨76906622215797628074008449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102542162954396837432011265 76906622215797628074008449)
          ·
            refine ⟨57679966661848221055506337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76906622215797628074008449 57679966661848221055506337)
            ·
              refine ⟨43259974996386165791629753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57679966661848221055506337 43259974996386165791629753)
              ·
                refine ⟨32444981247289624343722315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43259974996386165791629753 32444981247289624343722315)
                ·
                  refine ⟨48667471870934436515583473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32444981247289624343722315 48667471870934436515583473)
                  ·
                    refine ⟨36500603903200827386687605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48667471870934436515583473 36500603903200827386687605)
                    ·
                      refine ⟨3421931615925077567501963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36500603903200827386687605 3421931615925077567501963)
                      ·
                        rfl

theorem cell23_6664188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_6664188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664188 prefixEnd_6664188 := by exact prefixLift 6664188
  have htrace : WordTrace (prefixWord ++ tailWord_6664188) baseStart_6664188 baseEnd_6664188 := by
    simpa [prefixWord, tailWord_6664188, baseEnd_6664188] using wordTrace_append hprefix tailTrace_6664188
  have hstable : (prefixWord ++ tailWord_6664188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664188).length < 2 ^ (prefixWord ++ tailWord_6664188).sum := by decide
  have hdescent : baseEnd_6664188 < baseStart_6664188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664282 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_6664282 : Nat := 118140960795 + 6664282 * 2 ^ 59
def prefixEnd_6664282 : Nat := 4983230072969 + 3 ^ 40 * 6664282 * 2
def baseEnd_6664282 : Nat := 3421979883106600199726531

theorem tailTrace_6664282 : CollatzResearch.WordTrace tailWord_6664282 prefixEnd_6664282 3421979883106600199726531 := by
  unfold tailWord_6664282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60766583310612989399116775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162044222161634638397644733 60766583310612989399116775)
  ·
    refine ⟨91149874965919484098675163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60766583310612989399116775 91149874965919484098675163)
    ·
      refine ⟨136724812448879226148012745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91149874965919484098675163 136724812448879226148012745)
      ·
        refine ⟨102543609336659419611009559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136724812448879226148012745 102543609336659419611009559)
        ·
          refine ⟨153815414004989129416514339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102543609336659419611009559 153815414004989129416514339)
          ·
            refine ⟨230723121007483694124771509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153815414004989129416514339 230723121007483694124771509)
            ·
              refine ⟨21630292594451596324197329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230723121007483694124771509 21630292594451596324197329)
              ·
                refine ⟨16222719445838697243147997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21630292594451596324197329 16222719445838697243147997)
                ·
                  refine ⟨6083519792189511466180499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16222719445838697243147997 6083519792189511466180499)
                  ·
                    refine ⟨9125279688284267199270749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6083519792189511466180499 9125279688284267199270749)
                    ·
                      refine ⟨3421979883106600199726531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9125279688284267199270749 3421979883106600199726531)
                      ·
                        rfl

theorem cell23_6664282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_6664282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664282 prefixEnd_6664282 := by exact prefixLift 6664282
  have htrace : WordTrace (prefixWord ++ tailWord_6664282) baseStart_6664282 baseEnd_6664282 := by
    simpa [prefixWord, tailWord_6664282, baseEnd_6664282] using wordTrace_append hprefix tailTrace_6664282
  have hstable : (prefixWord ++ tailWord_6664282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664282).length < 2 ^ (prefixWord ++ tailWord_6664282).sum := by decide
  have hdescent : baseEnd_6664282 < baseStart_6664282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664286 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6664286 : Nat := 118140960795 + 6664286 * 2 ^ 59
def prefixEnd_6664286 : Nat := 4983230072969 + 3 ^ 40 * 6664286 * 2
def baseEnd_6664286 : Nat := 3421981937029218184076513

theorem tailTrace_6664286 : CollatzResearch.WordTrace tailWord_6664286 prefixEnd_6664286 3421981937029218184076513 := by
  unfold tailWord_6664286
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383309891804683284951589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162044319422958310853075141 30383309891804683284951589)
  ·
    refine ⟨5696870604713378115928423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30383309891804683284951589 5696870604713378115928423)
    ·
      refine ⟨8545305907070067173892635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5696870604713378115928423 8545305907070067173892635)
      ·
        refine ⟨12817958860605100760838953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545305907070067173892635 12817958860605100760838953)
        ·
          refine ⟨9613469145453825570629215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12817958860605100760838953 9613469145453825570629215)
          ·
            refine ⟨14420203718180738355943823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613469145453825570629215 14420203718180738355943823)
            ·
              refine ⟨21630305577271107533915735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420203718180738355943823 21630305577271107533915735)
              ·
                refine ⟨32445458365906661300873603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21630305577271107533915735 32445458365906661300873603)
                ·
                  refine ⟨48668187548859991951310405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32445458365906661300873603 48668187548859991951310405)
                  ·
                    refine ⟨9125285165411248490870701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48668187548859991951310405 9125285165411248490870701)
                    ·
                      refine ⟨3421981937029218184076513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9125285165411248490870701 3421981937029218184076513)
                      ·
                        rfl

theorem cell23_6664286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6664286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664286 prefixEnd_6664286 := by exact prefixLift 6664286
  have htrace : WordTrace (prefixWord ++ tailWord_6664286) baseStart_6664286 baseEnd_6664286 := by
    simpa [prefixWord, tailWord_6664286, baseEnd_6664286] using wordTrace_append hprefix tailTrace_6664286
  have hstable : (prefixWord ++ tailWord_6664286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664286).length < 2 ^ (prefixWord ++ tailWord_6664286).sum := by decide
  have hdescent : baseEnd_6664286 < baseStart_6664286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664302 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_6664302 : Nat := 118140960795 + 6664302 * 2 ^ 59
def prefixEnd_6664302 : Nat := 4983230072969 + 3 ^ 40 * 6664302 * 2
def baseEnd_6664302 : Nat := 1140663384239896707158813

theorem tailTrace_6664302 : CollatzResearch.WordTrace tailWord_6664302 prefixEnd_6664302 1140663384239896707158813 := by
  unfold tailWord_6664302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383382837797437626524395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162044708468253000674796773 30383382837797437626524395)
  ·
    refine ⟨45575074256696156439786593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30383382837797437626524395 45575074256696156439786593)
    ·
      refine ⟨34181305692522117329839945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45575074256696156439786593 34181305692522117329839945)
      ·
        refine ⟨25635979269391587997379959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34181305692522117329839945 25635979269391587997379959)
        ·
          refine ⟨38453968904087381996069939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25635979269391587997379959 38453968904087381996069939)
          ·
            refine ⟨57680953356131072994104909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38453968904087381996069939 57680953356131072994104909)
            ·
              refine ⟨21630357508549152372789341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57680953356131072994104909 21630357508549152372789341)
              ·
                refine ⟨8111384065705932139796003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21630357508549152372789341 8111384065705932139796003)
                ·
                  refine ⟨12167076098558898209694005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8111384065705932139796003 12167076098558898209694005)
                  ·
                    refine ⟨1140663384239896707158813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12167076098558898209694005 1140663384239896707158813)
                    ·
                      rfl

theorem cell23_6664302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_6664302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664302 prefixEnd_6664302 := by exact prefixLift 6664302
  have htrace : WordTrace (prefixWord ++ tailWord_6664302) baseStart_6664302 baseEnd_6664302 := by
    simpa [prefixWord, tailWord_6664302, baseEnd_6664302] using wordTrace_append hprefix tailTrace_6664302
  have hstable : (prefixWord ++ tailWord_6664302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664302).length < 2 ^ (prefixWord ++ tailWord_6664302).sum := by decide
  have hdescent : baseEnd_6664302 < baseStart_6664302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664325 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_6664325 : Nat := 118140960795 + 6664325 * 2 ^ 59
def prefixEnd_6664325 : Nat := 4983230072969 + 3 ^ 40 * 6664325 * 2
def baseEnd_6664325 : Nat := 3422001962774743531488833

theorem tailTrace_6664325 : CollatzResearch.WordTrace tailWord_6664325 prefixEnd_6664325 3422001962774743531488833 := by
  unfold tailWord_6664325
  simp only [CollatzResearch.WordTrace]
  refine ⟨243067901581296175940282429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162045267720864117293521619 243067901581296175940282429)
  ·
    refine ⟨91150463092986065977605911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243067901581296175940282429 91150463092986065977605911)
    ·
      refine ⟨136725694639479098966408867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91150463092986065977605911 136725694639479098966408867)
      ·
        refine ⟨205088541959218648449613301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136725694639479098966408867 205088541959218648449613301)
        ·
          refine ⟨19227050808676748292151247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205088541959218648449613301 19227050808676748292151247)
          ·
            refine ⟨28840576213015122438226871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19227050808676748292151247 28840576213015122438226871)
            ·
              refine ⟨43260864319522683657340307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28840576213015122438226871 43260864319522683657340307)
              ·
                refine ⟨64891296479284025486010461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43260864319522683657340307 64891296479284025486010461)
                ·
                  refine ⟨24334236179731509557253923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64891296479284025486010461 24334236179731509557253923)
                  ·
                    refine ⟨36501354269597264335880885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24334236179731509557253923 36501354269597264335880885)
                    ·
                      refine ⟨3422001962774743531488833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36501354269597264335880885 3422001962774743531488833)
                      ·
                        rfl

theorem cell23_6664325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_6664325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664325 prefixEnd_6664325 := by exact prefixLift 6664325
  have htrace : WordTrace (prefixWord ++ tailWord_6664325) baseStart_6664325 baseEnd_6664325 := by
    simpa [prefixWord, tailWord_6664325, baseEnd_6664325] using wordTrace_append hprefix tailTrace_6664325
  have hstable : (prefixWord ++ tailWord_6664325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664325).length < 2 ^ (prefixWord ++ tailWord_6664325).sum := by decide
  have hdescent : baseEnd_6664325 < baseStart_6664325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664350 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6664350 : Nat := 118140960795 + 6664350 * 2 ^ 59
def prefixEnd_6664350 : Nat := 4983230072969 + 3 ^ 40 * 6664350 * 2
def baseEnd_6664350 : Nat := 3422014799791105933676219

theorem tailTrace_6664350 : CollatzResearch.WordTrace tailWord_6664350 prefixEnd_6664350 3422014799791105933676219 := by
  unfold tailWord_6664350
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383601675775700651242813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162045875604137070139961669 30383601675775700651242813)
  ·
    refine ⟨11393850628415887744216055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30383601675775700651242813 11393850628415887744216055)
    ·
      refine ⟨17090775942623831616324083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11393850628415887744216055 17090775942623831616324083)
      ·
        refine ⟨25636163913935747424486125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17090775942623831616324083 25636163913935747424486125)
        ·
          refine ⟨9613561467725905284182297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25636163913935747424486125 9613561467725905284182297)
          ·
            refine ⟨7210171100794428963136723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9613561467725905284182297 7210171100794428963136723)
            ·
              refine ⟨10815256651191643444705085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210171100794428963136723 10815256651191643444705085)
              ·
                refine ⟨4055721244196866291764407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10815256651191643444705085 4055721244196866291764407)
                ·
                  refine ⟨6083581866295299437646611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055721244196866291764407 6083581866295299437646611)
                  ·
                    refine ⟨9125372799442949156469917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6083581866295299437646611 9125372799442949156469917)
                    ·
                      refine ⟨3422014799791105933676219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9125372799442949156469917 3422014799791105933676219)
                      ·
                        rfl

theorem cell23_6664350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6664350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664350 prefixEnd_6664350 := by exact prefixLift 6664350
  have htrace : WordTrace (prefixWord ++ tailWord_6664350) baseStart_6664350 baseEnd_6664350 := by
    simpa [prefixWord, tailWord_6664350, baseEnd_6664350] using wordTrace_append hprefix tailTrace_6664350
  have hstable : (prefixWord ++ tailWord_6664350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664350).length < 2 ^ (prefixWord ++ tailWord_6664350).sum := by decide
  have hdescent : baseEnd_6664350 < baseStart_6664350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664359 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6664359 : Nat := 118140960795 + 6664359 * 2 ^ 59
def prefixEnd_6664359 : Nat := 4983230072969 + 3 ^ 40 * 6664359 * 2
def baseEnd_6664359 : Nat := 3422019421116996398463677

theorem tailTrace_6664359 : CollatzResearch.WordTrace tailWord_6664359 prefixEnd_6664359 3422019421116996398463677 := by
  unfold tailWord_6664359
  simp only [CollatzResearch.WordTrace]
  refine ⟨243069141663172999747020131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162046094442115333164680087 243069141663172999747020131)
  ·
    refine ⟨364603712494759499620530197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243069141663172999747020131 364603712494759499620530197)
    ·
      refine ⟨17090799023191851544712353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 364603712494759499620530197 17090799023191851544712353)
      ·
        refine ⟨12818099267393888658534265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17090799023191851544712353 12818099267393888658534265)
        ·
          refine ⟨9613574450545416493900699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12818099267393888658534265 9613574450545416493900699)
          ·
            refine ⟨14420361675818124740851049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613574450545416493900699 14420361675818124740851049)
            ·
              refine ⟨10815271256863593555638287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14420361675818124740851049 10815271256863593555638287)
              ·
                refine ⟨16222906885295390333457431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10815271256863593555638287 16222906885295390333457431)
                ·
                  refine ⟨24334360327943085500186147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16222906885295390333457431 24334360327943085500186147)
                  ·
                    refine ⟨36501540491914628250279221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24334360327943085500186147 36501540491914628250279221)
                    ·
                      refine ⟨3422019421116996398463677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36501540491914628250279221 3422019421116996398463677)
                      ·
                        rfl

theorem cell23_6664359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6664359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664359 prefixEnd_6664359 := by exact prefixLift 6664359
  have htrace : WordTrace (prefixWord ++ tailWord_6664359) baseStart_6664359 baseEnd_6664359 := by
    simpa [prefixWord, tailWord_6664359, baseEnd_6664359] using wordTrace_append hprefix tailTrace_6664359
  have hstable : (prefixWord ++ tailWord_6664359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664359).length < 2 ^ (prefixWord ++ tailWord_6664359).sum := by decide
  have hdescent : baseEnd_6664359 < baseStart_6664359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664406 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6664406 : Nat := 118140960795 + 6664406 * 2 ^ 59
def prefixEnd_6664406 : Nat := 4983230072969 + 3 ^ 40 * 6664406 * 2
def baseEnd_6664406 : Nat := 3422043554707757714575961

theorem tailTrace_6664406 : CollatzResearch.WordTrace tailWord_6664406 prefixEnd_6664406 3422043554707757714575961 := by
  unfold tailWord_6664406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15191928493375170423373817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162047237262668484515987381 15191928493375170423373817)
  ·
    refine ⟨11393946370031377817530363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15191928493375170423373817 11393946370031377817530363)
    ·
      refine ⟨17090919555047066726295545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11393946370031377817530363 17090919555047066726295545)
      ·
        refine ⟨12818189666285300044721659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17090919555047066726295545 12818189666285300044721659)
        ·
          refine ⟨19227284499427950067082489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12818189666285300044721659 19227284499427950067082489)
          ·
            refine ⟨14420463374570962550311867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19227284499427950067082489 14420463374570962550311867)
            ·
              refine ⟨21630695061856443825467801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420463374570962550311867 21630695061856443825467801)
              ·
                refine ⟨16223021296392332869100851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21630695061856443825467801 16223021296392332869100851)
                ·
                  refine ⟨24334531944588499303651277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16223021296392332869100851 24334531944588499303651277)
                  ·
                    refine ⟨9125449479220687238869229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24334531944588499303651277 9125449479220687238869229)
                    ·
                      refine ⟨3422043554707757714575961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9125449479220687238869229 3422043554707757714575961)
                      ·
                        rfl

theorem cell23_6664406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6664406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664406 prefixEnd_6664406 := by exact prefixLift 6664406
  have htrace : WordTrace (prefixWord ++ tailWord_6664406) baseStart_6664406 baseEnd_6664406 := by
    simpa [prefixWord, tailWord_6664406, baseEnd_6664406] using wordTrace_append hprefix tailTrace_6664406
  have hstable : (prefixWord ++ tailWord_6664406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664406).length < 2 ^ (prefixWord ++ tailWord_6664406).sum := by decide
  have hdescent : baseEnd_6664406 < baseStart_6664406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664416 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 1, 3, 2]
def baseStart_6664416 : Nat := 118140960795 + 6664416 * 2 ^ 59
def prefixEnd_6664416 : Nat := 4983230072969 + 3 ^ 40 * 6664416 * 2
def baseEnd_6664416 : Nat := 3422048689514302675450915

theorem tailTrace_6664416 : CollatzResearch.WordTrace tailWord_6664416 prefixEnd_6664416 3422048689514302675450915 := by
  unfold tailWord_6664416
  simp only [CollatzResearch.WordTrace]
  refine ⟨121535610311983249240922551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162047480415977665654563401 121535610311983249240922551)
  ·
    refine ⟨182303415467974873861383827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121535610311983249240922551 182303415467974873861383827)
    ·
      refine ⟨273455123201962310792075741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182303415467974873861383827 273455123201962310792075741)
      ·
        refine ⟨102545671200735866547028403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273455123201962310792075741 102545671200735866547028403)
        ·
          refine ⟨153818506801103799820542605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102545671200735866547028403 153818506801103799820542605)
          ·
            refine ⟨57681940050413924932703477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153818506801103799820542605 57681940050413924932703477)
            ·
              refine ⟨5407681879726305462440951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57681940050413924932703477 5407681879726305462440951)
              ·
                refine ⟨8111522819589458193661427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407681879726305462440951 8111522819589458193661427)
                ·
                  refine ⟨12167284229384187290492141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8111522819589458193661427 12167284229384187290492141)
                  ·
                    refine ⟨4562731586019070233934553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12167284229384187290492141 4562731586019070233934553)
                    ·
                      refine ⟨3422048689514302675450915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562731586019070233934553 3422048689514302675450915)
                      ·
                        rfl

theorem cell23_6664416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_6664416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664416 prefixEnd_6664416 := by exact prefixLift 6664416
  have htrace : WordTrace (prefixWord ++ tailWord_6664416) baseStart_6664416 baseEnd_6664416 := by
    simpa [prefixWord, tailWord_6664416, baseEnd_6664416] using wordTrace_append hprefix tailTrace_6664416
  have hstable : (prefixWord ++ tailWord_6664416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664416).length < 2 ^ (prefixWord ++ tailWord_6664416).sum := by decide
  have hdescent : baseEnd_6664416 < baseStart_6664416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664425 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_6664425 : Nat := 118140960795 + 6664425 * 2 ^ 59
def prefixEnd_6664425 : Nat := 4983230072969 + 3 ^ 40 * 6664425 * 2
def baseEnd_6664425 : Nat := 3422053310840193140238373

theorem tailTrace_6664425 : CollatzResearch.WordTrace tailWord_6664425 prefixEnd_6664425 3422053310840193140238373 := by
  unfold tailWord_6664425
  simp only [CollatzResearch.WordTrace]
  refine ⟨243071548880933893018922729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162047699253955928679281819 243071548880933893018922729)
  ·
    refine ⟨182303661660700419764192047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243071548880933893018922729 182303661660700419764192047)
    ·
      refine ⟨273455492491050629646288071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182303661660700419764192047 273455492491050629646288071)
      ·
        refine ⟨410183238736575944469432107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273455492491050629646288071 410183238736575944469432107)
        ·
          refine ⟨615274858104863916704148161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410183238736575944469432107 615274858104863916704148161)
          ·
            refine ⟨461456143578647937528111121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615274858104863916704148161 461456143578647937528111121)
            ·
              refine ⟨346092107683985953146083341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461456143578647937528111121 346092107683985953146083341)
              ·
                refine ⟨129784540381494732429781253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346092107683985953146083341 129784540381494732429781253)
                ·
                  refine ⟨24334601321530262330583985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129784540381494732429781253 24334601321530262330583985)
                  ·
                    refine ⟨18250950991147696747937989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24334601321530262330583985 18250950991147696747937989)
                    ·
                      refine ⟨3422053310840193140238373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18250950991147696747937989 3422053310840193140238373)
                      ·
                        rfl

theorem cell23_6664425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_6664425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664425 prefixEnd_6664425 := by exact prefixLift 6664425
  have htrace : WordTrace (prefixWord ++ tailWord_6664425) baseStart_6664425 baseEnd_6664425 := by
    simpa [prefixWord, tailWord_6664425, baseEnd_6664425] using wordTrace_append hprefix tailTrace_6664425
  have hstable : (prefixWord ++ tailWord_6664425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664425).length < 2 ^ (prefixWord ++ tailWord_6664425).sum := by decide
  have hdescent : baseEnd_6664425 < baseStart_6664425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664435 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 7]
def baseStart_6664435 : Nat := 118140960795 + 6664435 * 2 ^ 59
def prefixEnd_6664435 : Nat := 4983230072969 + 3 ^ 40 * 6664435 * 2
def baseEnd_6664435 : Nat := 380228716182970900123703

theorem tailTrace_6664435 : CollatzResearch.WordTrace tailWord_6664435 prefixEnd_6664435 380228716182970900123703 := by
  unfold tailWord_6664435
  simp only [CollatzResearch.WordTrace]
  refine ⟨243071913610897664726786759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162047942407265109817857839 243071913610897664726786759)
  ·
    refine ⟨364607870416346497090180139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243071913610897664726786759 364607870416346497090180139)
    ·
      refine ⟨546911805624519745635270209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364607870416346497090180139 546911805624519745635270209)
      ·
        refine ⟨410183854218389809226452657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546911805624519745635270209 410183854218389809226452657)
        ·
          refine ⟨307637890663792356919839493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410183854218389809226452657 307637890663792356919839493)
          ·
            refine ⟨57682104499461066922469905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307637890663792356919839493 57682104499461066922469905)
            ·
              refine ⟨43261578374595800191852429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57682104499461066922469905 43261578374595800191852429)
              ·
                refine ⟨16223091890473425071944661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43261578374595800191852429 16223091890473425071944661)
                ·
                  refine ⟨380228716182970900123703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16223091890473425071944661 380228716182970900123703)
                  ·
                    rfl

theorem cell23_6664435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 7].length) (baseStart_6664435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664435 prefixEnd_6664435 := by exact prefixLift 6664435
  have htrace : WordTrace (prefixWord ++ tailWord_6664435) baseStart_6664435 baseEnd_6664435 := by
    simpa [prefixWord, tailWord_6664435, baseEnd_6664435] using wordTrace_append hprefix tailTrace_6664435
  have hstable : (prefixWord ++ tailWord_6664435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664435).length < 2 ^ (prefixWord ++ tailWord_6664435).sum := by decide
  have hdescent : baseEnd_6664435 < baseStart_6664435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664442 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_6664442 : Nat := 118140960795 + 6664442 * 2 ^ 59
def prefixEnd_6664442 : Nat := 4983230072969 + 3 ^ 40 * 6664442 * 2
def baseEnd_6664442 : Nat := 3422062040011319573725795

theorem tailTrace_6664442 : CollatzResearch.WordTrace tailWord_6664442 prefixEnd_6664442 3422062040011319573725795 := by
  unfold tailWord_6664442
  simp only [CollatzResearch.WordTrace]
  refine ⟨60768042230468076230572895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162048112614581536614861053 60768042230468076230572895)
  ·
    refine ⟨91152063345702114345859343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60768042230468076230572895 91152063345702114345859343)
    ·
      refine ⟨136728095018553171518789015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91152063345702114345859343 136728095018553171518789015)
      ·
        refine ⟨205092142527829757278183523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136728095018553171518789015 205092142527829757278183523)
        ·
          refine ⟨307638213791744635917275285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205092142527829757278183523 307638213791744635917275285)
          ·
            refine ⟨14420541271488029808622279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 307638213791744635917275285 14420541271488029808622279)
            ·
              refine ⟨21630811907232044712933419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14420541271488029808622279 21630811907232044712933419)
              ·
                refine ⟨32446217860848067069400129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21630811907232044712933419 32446217860848067069400129)
                ·
                  refine ⟨24334663395636050302050097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32446217860848067069400129 24334663395636050302050097)
                  ·
                    refine ⟨18250997546727037726537573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24334663395636050302050097 18250997546727037726537573)
                    ·
                      refine ⟨3422062040011319573725795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18250997546727037726537573 3422062040011319573725795)
                      ·
                        rfl

theorem cell23_6664442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_6664442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664442 prefixEnd_6664442 := by exact prefixLift 6664442
  have htrace : WordTrace (prefixWord ++ tailWord_6664442) baseStart_6664442 baseEnd_6664442 := by
    simpa [prefixWord, tailWord_6664442, baseEnd_6664442] using wordTrace_append hprefix tailTrace_6664442
  have hstable : (prefixWord ++ tailWord_6664442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664442).length < 2 ^ (prefixWord ++ tailWord_6664442).sum := by decide
  have hdescent : baseEnd_6664442 < baseStart_6664442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664446 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6664446 : Nat := 118140960795 + 6664446 * 2 ^ 59
def prefixEnd_6664446 : Nat := 4983230072969 + 3 ^ 40 * 6664446 * 2
def baseEnd_6664446 : Nat := 3422064093933937558075777

theorem tailTrace_6664446 : CollatzResearch.WordTrace tailWord_6664446 prefixEnd_6664446 3422064093933937558075777 := by
  unfold tailWord_6664446
  simp only [CollatzResearch.WordTrace]
  refine ⟨30384039351732226700679649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162048209875905209070291461 30384039351732226700679649)
  ·
    refine ⟨22788029513799170025509737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30384039351732226700679649 22788029513799170025509737)
    ·
      refine ⟨17091022135349377519132303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22788029513799170025509737 17091022135349377519132303)
      ·
        refine ⟨25636533203024066278698455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17091022135349377519132303 25636533203024066278698455)
        ·
          refine ⟨38454799804536099418047683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25636533203024066278698455 38454799804536099418047683)
          ·
            refine ⟨57682199706804149127071525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38454799804536099418047683 57682199706804149127071525)
            ·
              refine ⟨10815412445025777961325911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57682199706804149127071525 10815412445025777961325911)
              ·
                refine ⟨16223118667538666941988867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10815412445025777961325911 16223118667538666941988867)
                ·
                  refine ⟨24334678001308000412983301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16223118667538666941988867 24334678001308000412983301)
                  ·
                    refine ⟨4562752125245250077434369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24334678001308000412983301 4562752125245250077434369)
                    ·
                      refine ⟨3422064093933937558075777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562752125245250077434369 3422064093933937558075777)
                      ·
                        rfl

theorem cell23_6664446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6664446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664446 prefixEnd_6664446 := by exact prefixLift 6664446
  have htrace : WordTrace (prefixWord ++ tailWord_6664446) baseStart_6664446 baseEnd_6664446 := by
    simpa [prefixWord, tailWord_6664446, baseEnd_6664446] using wordTrace_append hprefix tailTrace_6664446
  have hstable : (prefixWord ++ tailWord_6664446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664446).length < 2 ^ (prefixWord ++ tailWord_6664446).sum := by decide
  have hdescent : baseEnd_6664446 < baseStart_6664446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664462 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6664462 : Nat := 118140960795 + 6664462 * 2 ^ 59
def prefixEnd_6664462 : Nat := 4983230072969 + 3 ^ 40 * 6664462 * 2
def baseEnd_6664462 : Nat := 3422072309624409495475703

theorem tailTrace_6664462 : CollatzResearch.WordTrace tailWord_6664462 prefixEnd_6664462 3422072309624409495475703 := by
  unfold tailWord_6664462
  simp only [CollatzResearch.WordTrace]
  refine ⟨30384112297724981042252455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162048598921199898892013093 30384112297724981042252455)
  ·
    refine ⟨45576168446587471563378683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30384112297724981042252455 45576168446587471563378683)
    ·
      refine ⟨68364252669881207345068025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45576168446587471563378683 68364252669881207345068025)
      ·
        refine ⟨51273189502410905508801019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68364252669881207345068025 51273189502410905508801019)
        ·
          refine ⟨76909784253616358263201529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51273189502410905508801019 76909784253616358263201529)
          ·
            refine ⟨57682338190212268697401147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76909784253616358263201529 57682338190212268697401147)
            ·
              refine ⟨86523507285318403046101721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57682338190212268697401147 86523507285318403046101721)
              ·
                refine ⟨64892630463988802284576291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86523507285318403046101721 64892630463988802284576291)
                ·
                  refine ⟨97338945695983203426864437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64892630463988802284576291 97338945695983203426864437)
                  ·
                    refine ⟨9125526158998425321268541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97338945695983203426864437 9125526158998425321268541)
                    ·
                      refine ⟨3422072309624409495475703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9125526158998425321268541 3422072309624409495475703)
                      ·
                        rfl

theorem cell23_6664462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6664462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664462 prefixEnd_6664462 := by exact prefixLift 6664462
  have htrace : WordTrace (prefixWord ++ tailWord_6664462) baseStart_6664462 baseEnd_6664462 := by
    simpa [prefixWord, tailWord_6664462, baseEnd_6664462] using wordTrace_append hprefix tailTrace_6664462
  have hstable : (prefixWord ++ tailWord_6664462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664462).length < 2 ^ (prefixWord ++ tailWord_6664462).sum := by decide
  have hdescent : baseEnd_6664462 < baseStart_6664462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664475 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_6664475 : Nat := 118140960795 + 6664475 * 2 ^ 59
def prefixEnd_6664475 : Nat := 4983230072969 + 3 ^ 40 * 6664475 * 2
def baseEnd_6664475 : Nat := 3422078984872917944613143

theorem tailTrace_6664475 : CollatzResearch.WordTrace tailWord_6664475 prefixEnd_6664475 3422078984872917944613143 := by
  unfold tailWord_6664475
  simp only [CollatzResearch.WordTrace]
  refine ⟨243073372530752751558242879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162048915020501834372161919 243073372530752751558242879)
  ·
    refine ⟨364610058796129127337364319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243073372530752751558242879 364610058796129127337364319)
    ·
      refine ⟨546915088194193691006046479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364610058796129127337364319 546915088194193691006046479)
      ·
        refine ⟨820372632291290536509069719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546915088194193691006046479 820372632291290536509069719)
        ·
          refine ⟨1230558948436935804763604579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820372632291290536509069719 1230558948436935804763604579)
          ·
            refine ⟨1845838422655403707145406869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230558948436935804763604579 1845838422655403707145406869)
            ·
              refine ⟨86523676061972048772440947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1845838422655403707145406869 86523676061972048772440947)
              ·
                refine ⟨129785514092958073158661421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86523676061972048772440947 129785514092958073158661421)
                ·
                  refine ⟨48669567784859277434498033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129785514092958073158661421 48669567784859277434498033)
                  ·
                    refine ⟨36502175838644458075873525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48669567784859277434498033 36502175838644458075873525)
                    ·
                      refine ⟨3422078984872917944613143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36502175838644458075873525 3422078984872917944613143)
                      ·
                        rfl

theorem cell23_6664475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_6664475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664475 prefixEnd_6664475 := by exact prefixLift 6664475
  have htrace : WordTrace (prefixWord ++ tailWord_6664475) baseStart_6664475 baseEnd_6664475 := by
    simpa [prefixWord, tailWord_6664475, baseEnd_6664475] using wordTrace_append hprefix tailTrace_6664475
  have hstable : (prefixWord ++ tailWord_6664475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664475).length < 2 ^ (prefixWord ++ tailWord_6664475).sum := by decide
  have hdescent : baseEnd_6664475 < baseStart_6664475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664512 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 5, 4]
def baseStart_6664512 : Nat := 118140960795 + 6664512 * 2 ^ 59
def prefixEnd_6664512 : Nat := 4983230072969 + 3 ^ 40 * 6664512 * 2
def baseEnd_6664512 : Nat := 1140699327885711433283491

theorem tailTrace_6664512 : CollatzResearch.WordTrace tailWord_6664512 prefixEnd_6664512 1140699327885711433283491 := by
  unfold tailWord_6664512
  simp only [CollatzResearch.WordTrace]
  refine ⟨121537361015809353438669895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162049814687745804584893193 121537361015809353438669895)
  ·
    refine ⟨182306041523714030158004843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121537361015809353438669895 182306041523714030158004843)
    ·
      refine ⟨273459062285571045237007265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182306041523714030158004843 273459062285571045237007265)
      ·
        refine ⟨205094296714178283927755449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273459062285571045237007265 205094296714178283927755449)
        ·
          refine ⟨153820722535633712945816587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205094296714178283927755449 153820722535633712945816587)
          ·
            refine ⟨230731083803450569418724881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153820722535633712945816587 230731083803450569418724881)
            ·
              refine ⟨173048312852587927064043661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230731083803450569418724881 173048312852587927064043661)
              ·
                refine ⟨64893117319720472649016373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173048312852587927064043661 64893117319720472649016373)
                ·
                  refine ⟨6083729748723794310845285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64893117319720472649016373 6083729748723794310845285)
                  ·
                    refine ⟨1140699327885711433283491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083729748723794310845285 1140699327885711433283491)
                    ·
                      rfl

theorem cell23_6664512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_6664512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664512 prefixEnd_6664512 := by exact prefixLift 6664512
  have htrace : WordTrace (prefixWord ++ tailWord_6664512) baseStart_6664512 baseEnd_6664512 := by
    simpa [prefixWord, tailWord_6664512, baseEnd_6664512] using wordTrace_append hprefix tailTrace_6664512
  have hstable : (prefixWord ++ tailWord_6664512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664512).length < 2 ^ (prefixWord ++ tailWord_6664512).sum := by decide
  have hdescent : baseEnd_6664512 < baseStart_6664512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664546 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_6664546 : Nat := 118140960795 + 6664546 * 2 ^ 59
def prefixEnd_6664546 : Nat := 4983230072969 + 3 ^ 40 * 6664546 * 2
def baseEnd_6664546 : Nat := 1140705147333129055608439

theorem tailTrace_6664546 : CollatzResearch.WordTrace tailWord_6664546 prefixEnd_6664546 1140705147333129055608439 := by
  unfold tailWord_6664546
  simp only [CollatzResearch.WordTrace]
  refine ⟨60768990528373882671019373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162050641408997020456051661 60768990528373882671019373)
  ·
    refine ⟨22788371448140206001632265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60768990528373882671019373 22788371448140206001632265)
    ·
      refine ⟨17091278586105154501224199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22788371448140206001632265 17091278586105154501224199)
      ·
        refine ⟨25636917879157731751836299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17091278586105154501224199 25636917879157731751836299)
        ·
          refine ⟨38455376818736597627754449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25636917879157731751836299 38455376818736597627754449)
          ·
            refine ⟨28841532614052448220815837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38455376818736597627754449 28841532614052448220815837)
            ·
              refine ⟨10815574730269668082805939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28841532614052448220815837 10815574730269668082805939)
              ·
                refine ⟨16223362095404502124208909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10815574730269668082805939 16223362095404502124208909)
                ·
                  refine ⟨6083760785776688296578341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16223362095404502124208909 6083760785776688296578341)
                  ·
                    refine ⟨1140705147333129055608439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6083760785776688296578341 1140705147333129055608439)
                    ·
                      rfl

theorem cell23_6664546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_6664546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664546 prefixEnd_6664546 := by exact prefixLift 6664546
  have htrace : WordTrace (prefixWord ++ tailWord_6664546) baseStart_6664546 baseEnd_6664546 := by
    simpa [prefixWord, tailWord_6664546, baseEnd_6664546] using wordTrace_append hprefix tailTrace_6664546
  have hstable : (prefixWord ++ tailWord_6664546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664546).length < 2 ^ (prefixWord ++ tailWord_6664546).sum := by decide
  have hdescent : baseEnd_6664546 < baseStart_6664546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664569 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 3]
def baseStart_6664569 : Nat := 118140960795 + 6664569 * 2 ^ 59
def prefixEnd_6664569 : Nat := 4983230072969 + 3 ^ 40 * 6664569 * 2
def baseEnd_6664569 : Nat := 3422127252054440576837711

theorem tailTrace_6664569 : CollatzResearch.WordTrace tailWord_6664569 prefixEnd_6664569 3422127252054440576837711 := by
  unfold tailWord_6664569
  simp only [CollatzResearch.WordTrace]
  refine ⟨243076800992412205612164761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162051200661608137074776507 243076800992412205612164761)
  ·
    refine ⟨182307600744309154209123571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243076800992412205612164761 182307600744309154209123571)
    ·
      refine ⟨273461401116463731313685357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182307600744309154209123571 273461401116463731313685357)
      ·
        refine ⟨102548025418673899242632009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273461401116463731313685357 102548025418673899242632009)
        ·
          refine ⟨76911019064005424431974007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102548025418673899242632009 76911019064005424431974007)
          ·
            refine ⟨115366528596008136647961011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76911019064005424431974007 115366528596008136647961011)
            ·
              refine ⟨173049792894012204971941517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115366528596008136647961011 173049792894012204971941517)
              ·
                refine ⟨64893672335254576864478069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173049792894012204971941517 64893672335254576864478069)
                ·
                  refine ⟨6083781781430116581044819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64893672335254576864478069 6083781781430116581044819)
                  ·
                    refine ⟨9125672672145174871567229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6083781781430116581044819 9125672672145174871567229)
                    ·
                      refine ⟨3422127252054440576837711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9125672672145174871567229 3422127252054440576837711)
                      ·
                        rfl

theorem cell23_6664569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_6664569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664569 prefixEnd_6664569 := by exact prefixLift 6664569
  have htrace : WordTrace (prefixWord ++ tailWord_6664569) baseStart_6664569 baseEnd_6664569 := by
    simpa [prefixWord, tailWord_6664569, baseEnd_6664569] using wordTrace_append hprefix tailTrace_6664569
  have hstable : (prefixWord ++ tailWord_6664569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664569).length < 2 ^ (prefixWord ++ tailWord_6664569).sum := by decide
  have hdescent : baseEnd_6664569 < baseStart_6664569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664606 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6664606 : Nat := 118140960795 + 6664606 * 2 ^ 59
def prefixEnd_6664606 : Nat := 4983230072969 + 3 ^ 40 * 6664606 * 2
def baseEnd_6664606 : Nat := 1140715416946218977358347

theorem tailTrace_6664606 : CollatzResearch.WordTrace tailWord_6664606 prefixEnd_6664606 1140715416946218977358347 := by
  unfold tailWord_6664606
  simp only [CollatzResearch.WordTrace]
  refine ⟨30384768811659770116407709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162052100328852107287507781 30384768811659770116407709)
  ·
    refine ⟨11394288304372413793652891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30384768811659770116407709 11394288304372413793652891)
    ·
      refine ⟨17091432456558620690479337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11394288304372413793652891 17091432456558620690479337)
      ·
        refine ⟨12818574342418965517859503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17091432456558620690479337 12818574342418965517859503)
        ·
          refine ⟨19227861513628448276789255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12818574342418965517859503 19227861513628448276789255)
          ·
            refine ⟨28841792270442672415183883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19227861513628448276789255 28841792270442672415183883)
            ·
              refine ⟨43262688405664008622775825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28841792270442672415183883 43262688405664008622775825)
              ·
                refine ⟨32447016304248006467081869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43262688405664008622775825 32447016304248006467081869)
                ·
                  refine ⟨12167631114093002425155701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32447016304248006467081869 12167631114093002425155701)
                  ·
                    refine ⟨1140715416946218977358347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12167631114093002425155701 1140715416946218977358347)
                    ·
                      rfl

theorem cell23_6664606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6664606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664606 prefixEnd_6664606 := by exact prefixLift 6664606
  have htrace : WordTrace (prefixWord ++ tailWord_6664606) baseStart_6664606 baseEnd_6664606 := by
    simpa [prefixWord, tailWord_6664606, baseEnd_6664606] using wordTrace_append hprefix tailTrace_6664606
  have hstable : (prefixWord ++ tailWord_6664606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664606).length < 2 ^ (prefixWord ++ tailWord_6664606).sum := by decide
  have hdescent : baseEnd_6664606 < baseStart_6664606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664660 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_6664660 : Nat := 118140960795 + 6664660 * 2 ^ 59
def prefixEnd_6664660 : Nat := 4983230072969 + 3 ^ 40 * 6664660 * 2
def baseEnd_6664660 : Nat := 3422173978793999720799793

theorem tailTrace_6664660 : CollatzResearch.WordTrace tailWord_6664660 prefixEnd_6664660 3422173978793999720799793 := by
  unfold tailWord_6664660
  simp only [CollatzResearch.WordTrace]
  refine ⟨121540060017541264076863717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162053413356721685435818289 121540060017541264076863717)
  ·
    refine ⟨22788761253288987014411947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121540060017541264076863717 22788761253288987014411947)
    ·
      refine ⟨34183141879933480521617921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22788761253288987014411947 34183141879933480521617921)
      ·
        refine ⟨25637356409950110391213441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34183141879933480521617921 25637356409950110391213441)
        ·
          refine ⟨19228017307462582793410081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25637356409950110391213441 19228017307462582793410081)
          ·
            refine ⟨14421012980596937095057561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19228017307462582793410081 14421012980596937095057561)
            ·
              refine ⟨10815759735447702821293171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14421012980596937095057561 10815759735447702821293171)
              ·
                refine ⟨16223639603171554231939757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10815759735447702821293171 16223639603171554231939757)
                ·
                  refine ⟨6083864851189332836977409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16223639603171554231939757 6083864851189332836977409)
                  ·
                    refine ⟨4562898638391999627733057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6083864851189332836977409 4562898638391999627733057)
                    ·
                      refine ⟨3422173978793999720799793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562898638391999627733057 3422173978793999720799793)
                      ·
                        rfl

theorem cell23_6664660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_6664660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664660 prefixEnd_6664660 := by exact prefixLift 6664660
  have htrace : WordTrace (prefixWord ++ tailWord_6664660) baseStart_6664660 baseEnd_6664660 := by
    simpa [prefixWord, tailWord_6664660, baseEnd_6664660] using wordTrace_append hprefix tailTrace_6664660
  have hstable : (prefixWord ++ tailWord_6664660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664660).length < 2 ^ (prefixWord ++ tailWord_6664660).sum := by decide
  have hdescent : baseEnd_6664660 < baseStart_6664660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664750 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_6664750 : Nat := 118140960795 + 6664750 * 2 ^ 59
def prefixEnd_6664750 : Nat := 4983230072969 + 3 ^ 40 * 6664750 * 2
def baseEnd_6664750 : Nat := 3422220192052904368674379

theorem tailTrace_6664750 : CollatzResearch.WordTrace tailWord_6664750 prefixEnd_6664750 3422220192052904368674379 := by
  unfold tailWord_6664750
  simp only [CollatzResearch.WordTrace]
  refine ⟨30385425325594559190562963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162055601736504315683002469 30385425325594559190562963)
  ·
    refine ⟨45578137988391838785844445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30385425325594559190562963 45578137988391838785844445)
    ·
      refine ⟨17091801745646939544691667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45578137988391838785844445 17091801745646939544691667)
      ·
        refine ⟨25637702618470409317037501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17091801745646939544691667 25637702618470409317037501)
        ·
          refine ⟨9614138481926403493889063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25637702618470409317037501 9614138481926403493889063)
          ·
            refine ⟨14421207722889605240833595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9614138481926403493889063 14421207722889605240833595)
            ·
              refine ⟨21631811584334407861250393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14421207722889605240833595 21631811584334407861250393)
              ·
                refine ⟨16223858688250805895937795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21631811584334407861250393 16223858688250805895937795)
                ·
                  refine ⟨24335788032376208843906693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16223858688250805895937795 24335788032376208843906693)
                  ·
                    refine ⟨4562960256070539158232505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24335788032376208843906693 4562960256070539158232505)
                    ·
                      refine ⟨3422220192052904368674379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4562960256070539158232505 3422220192052904368674379)
                      ·
                        rfl

theorem cell23_6664750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_6664750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664750 prefixEnd_6664750 := by exact prefixLift 6664750
  have htrace : WordTrace (prefixWord ++ tailWord_6664750) baseStart_6664750 baseEnd_6664750 := by
    simpa [prefixWord, tailWord_6664750, baseEnd_6664750] using wordTrace_append hprefix tailTrace_6664750
  have hstable : (prefixWord ++ tailWord_6664750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664750).length < 2 ^ (prefixWord ++ tailWord_6664750).sum := by decide
  have hdescent : baseEnd_6664750 < baseStart_6664750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664773 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 5]
def baseStart_6664773 : Nat := 118140960795 + 6664773 * 2 ^ 59
def prefixEnd_6664773 : Nat := 4983230072969 + 3 ^ 40 * 6664773 * 2
def baseEnd_6664773 : Nat := 380248000234217530965197

theorem tailTrace_6664773 : CollatzResearch.WordTrace tailWord_6664773 prefixEnd_6664773 380248000234217530965197 := by
  unfold tailWord_6664773
  simp only [CollatzResearch.WordTrace]
  refine ⟨243084241483673148452590973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162056160989115432301727315 243084241483673148452590973)
  ·
    refine ⟨91156590556377430669721615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243084241483673148452590973 91156590556377430669721615)
    ·
      refine ⟨136734885834566146004582423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91156590556377430669721615 136734885834566146004582423)
      ·
        refine ⟨205102328751849219006873635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136734885834566146004582423 205102328751849219006873635)
        ·
          refine ⟨307653493127773828510310453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205102328751849219006873635 307653493127773828510310453)
          ·
            refine ⟨28842514980728796422841605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307653493127773828510310453 28842514980728796422841605)
            ·
              refine ⟨5407971558886649329282801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28842514980728796422841605 5407971558886649329282801)
              ·
                refine ⟨4055978669164986996962101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407971558886649329282801 4055978669164986996962101)
                ·
                  refine ⟨380248000234217530965197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4055978669164986996962101 380248000234217530965197)
                  ·
                    rfl

theorem cell23_6664773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_6664773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664773 prefixEnd_6664773 := by exact prefixLift 6664773
  have htrace : WordTrace (prefixWord ++ tailWord_6664773) baseStart_6664773 baseEnd_6664773 := by
    simpa [prefixWord, tailWord_6664773, baseEnd_6664773] using wordTrace_append hprefix tailTrace_6664773
  have hstable : (prefixWord ++ tailWord_6664773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664773).length < 2 ^ (prefixWord ++ tailWord_6664773).sum := by decide
  have hdescent : baseEnd_6664773 < baseStart_6664773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664779 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5]
def baseStart_6664779 : Nat := 118140960795 + 6664779 * 2 ^ 59
def prefixEnd_6664779 : Nat := 4983230072969 + 3 ^ 40 * 6664779 * 2
def baseEnd_6664779 : Nat := 3422235082991884755211745

theorem tailTrace_6664779 : CollatzResearch.WordTrace tailWord_6664779 prefixEnd_6664779 3422235082991884755211745 := by
  unfold tailWord_6664779
  simp only [CollatzResearch.WordTrace]
  refine ⟨243084460321651411477309391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162056306881100940984872927 243084460321651411477309391)
  ·
    refine ⟨364626690482477117215964087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243084460321651411477309391 364626690482477117215964087)
    ·
      refine ⟨546940035723715675823946131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364626690482477117215964087 546940035723715675823946131)
      ·
        refine ⟨820410053585573513735919197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546940035723715675823946131 820410053585573513735919197)
        ·
          refine ⟨307653770094590067650969699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 820410053585573513735919197 307653770094590067650969699)
          ·
            refine ⟨461480655141885101476454549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307653770094590067650969699 461480655141885101476454549)
            ·
              refine ⟨21631905709775864131708807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 461480655141885101476454549 21631905709775864131708807)
              ·
                refine ⟨32447858564663796197563211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21631905709775864131708807 32447858564663796197563211)
                ·
                  refine ⟨48671787846995694296344817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32447858564663796197563211 48671787846995694296344817)
                  ·
                    refine ⟨36503840885246770722258613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48671787846995694296344817 36503840885246770722258613)
                    ·
                      refine ⟨3422235082991884755211745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36503840885246770722258613 3422235082991884755211745)
                      ·
                        rfl

theorem cell23_6664779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_6664779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664779 prefixEnd_6664779 := by exact prefixLift 6664779
  have htrace : WordTrace (prefixWord ++ tailWord_6664779) baseStart_6664779 baseEnd_6664779 := by
    simpa [prefixWord, tailWord_6664779, baseEnd_6664779] using wordTrace_append hprefix tailTrace_6664779
  have hstable : (prefixWord ++ tailWord_6664779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664779).length < 2 ^ (prefixWord ++ tailWord_6664779).sum := by decide
  have hdescent : baseEnd_6664779 < baseStart_6664779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664833 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6664833 : Nat := 118140960795 + 6664833 * 2 ^ 59
def prefixEnd_6664833 : Nat := 4983230072969 + 3 ^ 40 * 6664833 * 2
def baseEnd_6664833 : Nat := 1140754270315742514645499

theorem tailTrace_6664833 : CollatzResearch.WordTrace tailWord_6664833 prefixEnd_6664833 1140754270315742514645499 := by
  unfold tailWord_6664833
  simp only [CollatzResearch.WordTrace]
  refine ⟨243086429863455778699775153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162057619908970519133183435 243086429863455778699775153)
  ·
    refine ⟨182314822397591834024831365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243086429863455778699775153 182314822397591834024831365)
    ·
      refine ⟨34184029199548468879655881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182314822397591834024831365 34184029199548468879655881)
      ·
        refine ⟨25638021899661351659741911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34184029199548468879655881 25638021899661351659741911)
        ·
          refine ⟨38457032849492027489612867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25638021899661351659741911 38457032849492027489612867)
          ·
            refine ⟨57685549274238041234419301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38457032849492027489612867 57685549274238041234419301)
            ·
              refine ⟨10816040488919632731453619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57685549274238041234419301 10816040488919632731453619)
              ·
                refine ⟨16224060733379449097180429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816040488919632731453619 16224060733379449097180429)
                ·
                  refine ⟨6084022775017293411442661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16224060733379449097180429 6084022775017293411442661)
                  ·
                    refine ⟨1140754270315742514645499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084022775017293411442661 1140754270315742514645499)
                    ·
                      rfl

theorem cell23_6664833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6664833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664833 prefixEnd_6664833 := by exact prefixLift 6664833
  have htrace : WordTrace (prefixWord ++ tailWord_6664833) baseStart_6664833 baseEnd_6664833 := by
    simpa [prefixWord, tailWord_6664833, baseEnd_6664833] using wordTrace_append hprefix tailTrace_6664833
  have hstable : (prefixWord ++ tailWord_6664833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664833).length < 2 ^ (prefixWord ++ tailWord_6664833).sum := by decide
  have hdescent : baseEnd_6664833 < baseStart_6664833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664856 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_6664856 : Nat := 118140960795 + 6664856 * 2 ^ 59
def prefixEnd_6664856 : Nat := 4983230072969 + 3 ^ 40 * 6664856 * 2
def baseEnd_6664856 : Nat := 3422274621002280953948891

theorem tailTrace_6664856 : CollatzResearch.WordTrace tailWord_6664856 prefixEnd_6664856 3422274621002280953948891 := by
  unfold tailWord_6664856
  simp only [CollatzResearch.WordTrace]
  refine ⟨121543634371186226813931211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162058179161581635751908281 121543634371186226813931211)
  ·
    refine ⟨182315451556779340220896817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121543634371186226813931211 182315451556779340220896817)
    ·
      refine ⟨136736588667584505165672613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182315451556779340220896817 136736588667584505165672613)
      ·
        refine ⟨25638110375172094718563615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136736588667584505165672613 25638110375172094718563615)
        ·
          refine ⟨38457165562758142077845423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25638110375172094718563615 38457165562758142077845423)
          ·
            refine ⟨57685748344137213116768135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38457165562758142077845423 57685748344137213116768135)
            ·
              refine ⟨86528622516205819675152203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57685748344137213116768135 86528622516205819675152203)
              ·
                refine ⟨129792933774308729512728305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86528622516205819675152203 129792933774308729512728305)
                ·
                  refine ⟨97344700330731547134546229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129792933774308729512728305 97344700330731547134546229)
                  ·
                    refine ⟨9126065656006082543863709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97344700330731547134546229 9126065656006082543863709)
                    ·
                      refine ⟨3422274621002280953948891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9126065656006082543863709 3422274621002280953948891)
                      ·
                        rfl

theorem cell23_6664856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_6664856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664856 prefixEnd_6664856 := by exact prefixLift 6664856
  have htrace : WordTrace (prefixWord ++ tailWord_6664856) baseStart_6664856 baseEnd_6664856 := by
    simpa [prefixWord, tailWord_6664856, baseEnd_6664856] using wordTrace_append hprefix tailTrace_6664856
  have hstable : (prefixWord ++ tailWord_6664856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664856).length < 2 ^ (prefixWord ++ tailWord_6664856).sum := by decide
  have hdescent : baseEnd_6664856 < baseStart_6664856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664883 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 4, 3, 2]
def baseStart_6664883 : Nat := 118140960795 + 6664883 * 2 ^ 59
def prefixEnd_6664883 : Nat := 4983230072969 + 3 ^ 40 * 6664883 * 2
def baseEnd_6664883 : Nat := 3422288484979952348311267

theorem tailTrace_6664883 : CollatzResearch.WordTrace tailWord_6664883 prefixEnd_6664883 3422288484979952348311267 := by
  unfold tailWord_6664883
  simp only [CollatzResearch.WordTrace]
  refine ⟨243088253513274637239095303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162058835675516424826063535 243088253513274637239095303)
  ·
    refine ⟨364632380269911955858642955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243088253513274637239095303 364632380269911955858642955)
    ·
      refine ⟨546948570404867933787964433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364632380269911955858642955 546948570404867933787964433)
      ·
        refine ⟨410211427803650950340973325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546948570404867933787964433 410211427803650950340973325)
        ·
          refine ⟨153829285426369106377864997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410211427803650950340973325 153829285426369106377864997)
          ·
            refine ⟨28842991017444207445849687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153829285426369106377864997 28842991017444207445849687)
            ·
              refine ⟨43264486526166311168774531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28842991017444207445849687 43264486526166311168774531)
              ·
                refine ⟨64896729789249466753161797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43264486526166311168774531 64896729789249466753161797)
                ·
                  refine ⟨12168136835484275016217837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64896729789249466753161797 12168136835484275016217837)
                  ·
                    refine ⟨4563051313306603131081689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12168136835484275016217837 4563051313306603131081689)
                    ·
                      refine ⟨3422288484979952348311267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563051313306603131081689 3422288484979952348311267)
                      ·
                        rfl

theorem cell23_6664883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3, 2].length) (baseStart_6664883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664883 prefixEnd_6664883 := by exact prefixLift 6664883
  have htrace : WordTrace (prefixWord ++ tailWord_6664883) baseStart_6664883 baseEnd_6664883 := by
    simpa [prefixWord, tailWord_6664883, baseEnd_6664883] using wordTrace_append hprefix tailTrace_6664883
  have hstable : (prefixWord ++ tailWord_6664883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664883).length < 2 ^ (prefixWord ++ tailWord_6664883).sum := by decide
  have hdescent : baseEnd_6664883 < baseStart_6664883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664910 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_6664910 : Nat := 118140960795 + 6664910 * 2 ^ 59
def prefixEnd_6664910 : Nat := 4983230072969 + 3 ^ 40 * 6664910 * 2
def baseEnd_6664910 : Nat := 1140767449652541247557881

theorem tailTrace_6664910 : CollatzResearch.WordTrace tailWord_6664910 prefixEnd_6664910 1140767449652541247557881 := by
  unfold tailWord_6664910
  simp only [CollatzResearch.WordTrace]
  refine ⟨30386154785522102606291023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162059492189451213900218789 30386154785522102606291023)
  ·
    refine ⟨45579232178283153909436535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30386154785522102606291023 45579232178283153909436535)
    ·
      refine ⟨68368848267424730864154803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45579232178283153909436535 68368848267424730864154803)
      ·
        refine ⟨102553272401137096296232205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68368848267424730864154803 102553272401137096296232205)
        ·
          refine ⟨38457477150426411111087077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102553272401137096296232205 38457477150426411111087077)
          ·
            refine ⟨7210776965704952083328827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38457477150426411111087077 7210776965704952083328827)
            ·
              refine ⟨10816165448557428124993241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210776965704952083328827 10816165448557428124993241)
              ·
                refine ⟨8112124086418071093744931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10816165448557428124993241 8112124086418071093744931)
                ·
                  refine ⟨12168186129627106640617397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8112124086418071093744931 12168186129627106640617397)
                  ·
                    refine ⟨1140767449652541247557881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12168186129627106640617397 1140767449652541247557881)
                    ·
                      rfl

theorem cell23_6664910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_6664910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664910 prefixEnd_6664910 := by exact prefixLift 6664910
  have htrace : WordTrace (prefixWord ++ tailWord_6664910) baseStart_6664910 baseEnd_6664910 := by
    simpa [prefixWord, tailWord_6664910, baseEnd_6664910] using wordTrace_append hprefix tailTrace_6664910
  have hstable : (prefixWord ++ tailWord_6664910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664910).length < 2 ^ (prefixWord ++ tailWord_6664910).sum := by decide
  have hdescent : baseEnd_6664910 < baseStart_6664910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664933 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_6664933 : Nat := 118140960795 + 6664933 * 2 ^ 59
def prefixEnd_6664933 : Nat := 4983230072969 + 3 ^ 40 * 6664933 * 2
def baseEnd_6664933 : Nat := 3422314159012677152686037

theorem tailTrace_6664933 : CollatzResearch.WordTrace tailWord_6664933 prefixEnd_6664933 3422314159012677152686037 := by
  unfold tailWord_6664933
  simp only [CollatzResearch.WordTrace]
  refine ⟨243090077163093495778415453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162060051442062330518943635 243090077163093495778415453)
  ·
    refine ⟨91158778936160060916905795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243090077163093495778415453 91158778936160060916905795)
    ·
      refine ⟨136738168404240091375358693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91158778936160060916905795 136738168404240091375358693)
      ·
        refine ⟨25638406575795017132879755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136738168404240091375358693 25638406575795017132879755)
        ·
          refine ⟨38457609863692525699319633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25638406575795017132879755 38457609863692525699319633)
          ·
            refine ⟨28843207397769394274489725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38457609863692525699319633 28843207397769394274489725)
            ·
              refine ⟨10816202774163522852933647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28843207397769394274489725 10816202774163522852933647)
              ·
                refine ⟨16224304161245284279400471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816202774163522852933647 16224304161245284279400471)
                ·
                  refine ⟨24336456241867926419100707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16224304161245284279400471 24336456241867926419100707)
                  ·
                    refine ⟨36504684362801889628651061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24336456241867926419100707 36504684362801889628651061)
                    ·
                      refine ⟨3422314159012677152686037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36504684362801889628651061 3422314159012677152686037)
                      ·
                        rfl

theorem cell23_6664933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_6664933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664933 prefixEnd_6664933 := by exact prefixLift 6664933
  have htrace : WordTrace (prefixWord ++ tailWord_6664933) baseStart_6664933 baseEnd_6664933 := by
    simpa [prefixWord, tailWord_6664933, baseEnd_6664933] using wordTrace_append hprefix tailTrace_6664933
  have hstable : (prefixWord ++ tailWord_6664933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664933).length < 2 ^ (prefixWord ++ tailWord_6664933).sum := by decide
  have hdescent : baseEnd_6664933 < baseStart_6664933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664936 : List Nat := [2, 1, 4, 1, 4, 11]
def baseStart_6664936 : Nat := 118140960795 + 6664936 * 2 ^ 59
def prefixEnd_6664936 : Nat := 4983230072969 + 3 ^ 40 * 6664936 * 2
def baseEnd_6664936 : Nat := 14083603701459426505961

theorem tailTrace_6664936 : CollatzResearch.WordTrace tailWord_6664936 prefixEnd_6664936 14083603701459426505961 := by
  unfold tailWord_6664936
  simp only [CollatzResearch.WordTrace]
  refine ⟨121545093291041313645387331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162060124388055084860516441 121545093291041313645387331)
  ·
    refine ⟨182317639936561970468080997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121545093291041313645387331 182317639936561970468080997)
    ·
      refine ⟨34184557488105369462765187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182317639936561970468080997 34184557488105369462765187)
      ·
        refine ⟨51276836232158054194147781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34184557488105369462765187 51276836232158054194147781)
        ·
          refine ⟨9614406793529635161402709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51276836232158054194147781 9614406793529635161402709)
          ·
            refine ⟨14083603701459426505961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9614406793529635161402709 14083603701459426505961)
            ·
              rfl

theorem cell23_6664936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 11].length) (baseStart_6664936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664936 prefixEnd_6664936 := by exact prefixLift 6664936
  have htrace : WordTrace (prefixWord ++ tailWord_6664936) baseStart_6664936 baseEnd_6664936 := by
    simpa [prefixWord, tailWord_6664936, baseEnd_6664936] using wordTrace_append hprefix tailTrace_6664936
  have hstable : (prefixWord ++ tailWord_6664936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664936).length < 2 ^ (prefixWord ++ tailWord_6664936).sum := by decide
  have hdescent : baseEnd_6664936 < baseStart_6664936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6664963 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 3]
def baseStart_6664963 : Nat := 118140960795 + 6664963 * 2 ^ 59
def prefixEnd_6664963 : Nat := 4983230072969 + 3 ^ 40 * 6664963 * 2
def baseEnd_6664963 : Nat := 3422329563432312035310899

theorem tailTrace_6664963 : CollatzResearch.WordTrace tailWord_6664963 prefixEnd_6664963 3422329563432312035310899 := by
  unfold tailWord_6664963
  simp only [CollatzResearch.WordTrace]
  refine ⟨243091171352984810902007543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162060780901989873934671695 243091171352984810902007543)
  ·
    refine ⟨364636757029477216353011315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243091171352984810902007543 364636757029477216353011315)
    ·
      refine ⟨546955135544215824529516973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364636757029477216353011315 546955135544215824529516973)
      ·
        refine ⟨205108175829080934198568865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546955135544215824529516973 205108175829080934198568865)
        ·
          refine ⟨153831131871810700648926649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205108175829080934198568865 153831131871810700648926649)
          ·
            refine ⟨115373348903858025486694987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153831131871810700648926649 115373348903858025486694987)
            ·
              refine ⟨173060023355787038230042481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115373348903858025486694987 173060023355787038230042481)
              ·
                refine ⟨129795017516840278672531861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173060023355787038230042481 129795017516840278672531861)
                ·
                  refine ⟨6084141446101888062774931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129795017516840278672531861 6084141446101888062774931)
                  ·
                    refine ⟨9126212169152832094162397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6084141446101888062774931 9126212169152832094162397)
                    ·
                      refine ⟨3422329563432312035310899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9126212169152832094162397 3422329563432312035310899)
                      ·
                        rfl

theorem cell23_6664963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_6664963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6664963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6664963 prefixEnd_6664963 := by exact prefixLift 6664963
  have htrace : WordTrace (prefixWord ++ tailWord_6664963) baseStart_6664963 baseEnd_6664963 := by
    simpa [prefixWord, tailWord_6664963, baseEnd_6664963] using wordTrace_append hprefix tailTrace_6664963
  have hstable : (prefixWord ++ tailWord_6664963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6664963).length < 2 ^ (prefixWord ++ tailWord_6664963).sum := by decide
  have hdescent : baseEnd_6664963 < baseStart_6664963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6664963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665003 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 5, 4, 2]
def baseStart_6665003 : Nat := 118140960795 + 6665003 * 2 ^ 59
def prefixEnd_6665003 : Nat := 4983230072969 + 3 ^ 40 * 6665003 * 2
def baseEnd_6665003 : Nat := 3422350102658491878810715

theorem tailTrace_6665003 : CollatzResearch.WordTrace tailWord_6665003 prefixEnd_6665003 3422350102658491878810715 := by
  unfold tailWord_6665003
  simp only [CollatzResearch.WordTrace]
  refine ⟨243092630272839897733463663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162061753515226598488975775 243092630272839897733463663)
  ·
    refine ⟨364638945409259846600195495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243092630272839897733463663 364638945409259846600195495)
    ·
      refine ⟨546958418113889769900293243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364638945409259846600195495 546958418113889769900293243)
      ·
        refine ⟨820437627170834654850439865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546958418113889769900293243 820437627170834654850439865)
        ·
          refine ⟨615328220378125991137829899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820437627170834654850439865 615328220378125991137829899)
          ·
            refine ⟨922992330567188986706744849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615328220378125991137829899 922992330567188986706744849)
            ·
              refine ⟨692244247925391740030058637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922992330567188986706744849 692244247925391740030058637)
              ·
                refine ⟨259591592972021902511271989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692244247925391740030058637 259591592972021902511271989)
                ·
                  refine ⟨24336711841127053360431749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259591592972021902511271989 24336711841127053360431749)
                  ·
                    refine ⟨4563133470211322505080953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24336711841127053360431749 4563133470211322505080953)
                    ·
                      refine ⟨3422350102658491878810715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563133470211322505080953 3422350102658491878810715)
                      ·
                        rfl

theorem cell23_6665003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4, 2].length) (baseStart_6665003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665003 prefixEnd_6665003 := by exact prefixLift 6665003
  have htrace : WordTrace (prefixWord ++ tailWord_6665003) baseStart_6665003 baseEnd_6665003 := by
    simpa [prefixWord, tailWord_6665003, baseEnd_6665003] using wordTrace_append hprefix tailTrace_6665003
  have hstable : (prefixWord ++ tailWord_6665003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665003).length < 2 ^ (prefixWord ++ tailWord_6665003).sum := by decide
  have hdescent : baseEnd_6665003 < baseStart_6665003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665013 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_6665013 : Nat := 118140960795 + 6665013 * 2 ^ 59
def prefixEnd_6665013 : Nat := 4983230072969 + 3 ^ 40 * 6665013 * 2
def baseEnd_6665013 : Nat := 1140785079155012279895223

theorem tailTrace_6665013 : CollatzResearch.WordTrace tailWord_6665013 prefixEnd_6665013 1140785079155012279895223 := by
  unfold tailWord_6665013
  simp only [CollatzResearch.WordTrace]
  refine ⟨243092995002803669441327693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162061996668535779627551795 243092995002803669441327693)
  ·
    refine ⟨91159873126051376040497885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243092995002803669441327693 91159873126051376040497885)
    ·
      refine ⟨34184952422269266015186707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91159873126051376040497885 34184952422269266015186707)
      ·
        refine ⟨51277428633403899022780061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34184952422269266015186707 51277428633403899022780061)
        ·
          refine ⟨19229035737526462133542523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51277428633403899022780061 19229035737526462133542523)
          ·
            refine ⟨28843553606289693200313785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19229035737526462133542523 28843553606289693200313785)
            ·
              refine ⟨21632665204717269900235339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28843553606289693200313785 21632665204717269900235339)
              ·
                refine ⟨32448997807075904850353009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21632665204717269900235339 32448997807075904850353009)
                ·
                  refine ⟨24336748355306928637764757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32448997807075904850353009 24336748355306928637764757)
                  ·
                    refine ⟨1140785079155012279895223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24336748355306928637764757 1140785079155012279895223)
                    ·
                      rfl

theorem cell23_6665013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_6665013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665013 prefixEnd_6665013 := by exact prefixLift 6665013
  have htrace : WordTrace (prefixWord ++ tailWord_6665013) baseStart_6665013 baseEnd_6665013 := by
    simpa [prefixWord, tailWord_6665013, baseEnd_6665013] using wordTrace_append hprefix tailTrace_6665013
  have hstable : (prefixWord ++ tailWord_6665013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665013).length < 2 ^ (prefixWord ++ tailWord_6665013).sum := by decide
  have hdescent : baseEnd_6665013 < baseStart_6665013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665014 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6665014 : Nat := 118140960795 + 6665014 * 2 ^ 59
def prefixEnd_6665014 : Nat := 4983230072969 + 3 ^ 40 * 6665014 * 2
def baseEnd_6665014 : Nat := 3422355750945691335773165

theorem tailTrace_6665014 : CollatzResearch.WordTrace tailWord_6665014 prefixEnd_6665014 3422355750945691335773165 := by
  unfold tailWord_6665014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193314467237502913257131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162062020983866697741409397 15193314467237502913257131)
  ·
    refine ⟨22789971700856254369885697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15193314467237502913257131 22789971700856254369885697)
    ·
      refine ⟨17092478775642190777414273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22789971700856254369885697 17092478775642190777414273)
      ·
        refine ⟨12819359081731643083060705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17092478775642190777414273 12819359081731643083060705)
        ·
          refine ⟨9614519311298732312295529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12819359081731643083060705 9614519311298732312295529)
          ·
            refine ⟨7210889483474049234221647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9614519311298732312295529 7210889483474049234221647)
            ·
              refine ⟨10816334225211073851332471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210889483474049234221647 10816334225211073851332471)
              ·
                refine ⟨16224501337816610776998707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816334225211073851332471 16224501337816610776998707)
                ·
                  refine ⟨24336752006724916165498061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16224501337816610776998707 24336752006724916165498061)
                  ·
                    refine ⟨9126282002521843562061773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24336752006724916165498061 9126282002521843562061773)
                    ·
                      refine ⟨3422355750945691335773165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9126282002521843562061773 3422355750945691335773165)
                      ·
                        rfl

theorem cell23_6665014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6665014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665014 prefixEnd_6665014 := by exact prefixLift 6665014
  have htrace : WordTrace (prefixWord ++ tailWord_6665014) baseStart_6665014 baseEnd_6665014 := by
    simpa [prefixWord, tailWord_6665014, baseEnd_6665014] using wordTrace_append hprefix tailTrace_6665014
  have hstable : (prefixWord ++ tailWord_6665014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665014).length < 2 ^ (prefixWord ++ tailWord_6665014).sum := by decide
  have hdescent : baseEnd_6665014 < baseStart_6665014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665060 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 7]
def baseStart_6665060 : Nat := 118140960795 + 6665060 * 2 ^ 59
def prefixEnd_6665060 : Nat := 4983230072969 + 3 ^ 40 * 6665060 * 2
def baseEnd_6665060 : Nat := 380264374561755350644217

theorem tailTrace_6665060 : CollatzResearch.WordTrace tailWord_6665060 prefixEnd_6665060 380264374561755350644217 := by
  unfold tailWord_6665060
  simp only [CollatzResearch.WordTrace]
  refine ⟨121547354616816698234144317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162063139489088930978859089 121547354616816698234144317)
  ·
    refine ⟨45580257981306261837804119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121547354616816698234144317 45580257981306261837804119)
    ·
      refine ⟨68370386971959392756706179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45580257981306261837804119 68370386971959392756706179)
      ·
        refine ⟨102555580457939089135059269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68370386971959392756706179 102555580457939089135059269)
        ·
          refine ⟨19229171335863579212823613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102555580457939089135059269 19229171335863579212823613)
          ·
            refine ⟨7210939250948842204808855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19229171335863579212823613 7210939250948842204808855)
            ·
              refine ⟨10816408876423263307213283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210939250948842204808855 10816408876423263307213283)
              ·
                refine ⟨16224613314634894960819925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816408876423263307213283 16224613314634894960819925)
                ·
                  refine ⟨380264374561755350644217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16224613314634894960819925 380264374561755350644217)
                  ·
                    rfl

theorem cell23_6665060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_6665060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665060 prefixEnd_6665060 := by exact prefixLift 6665060
  have htrace : WordTrace (prefixWord ++ tailWord_6665060) baseStart_6665060 baseEnd_6665060 := by
    simpa [prefixWord, tailWord_6665060, baseEnd_6665060] using wordTrace_append hprefix tailTrace_6665060
  have hstable : (prefixWord ++ tailWord_6665060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665060).length < 2 ^ (prefixWord ++ tailWord_6665060).sum := by decide
  have hdescent : baseEnd_6665060 < baseStart_6665060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665113 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_6665113 : Nat := 118140960795 + 6665113 * 2 ^ 59
def prefixEnd_6665113 : Nat := 4983230072969 + 3 ^ 40 * 6665113 * 2
def baseEnd_6665113 : Nat := 3422406585530486448435209

theorem tailTrace_6665113 : CollatzResearch.WordTrace tailWord_6665113 prefixEnd_6665113 3422406585530486448435209 := by
  unfold tailWord_6665113
  simp only [CollatzResearch.WordTrace]
  refine ⟨243096642302441386519967993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162064428201627591013311995 243096642302441386519967993)
  ·
    refine ⟨182322481726831039889975995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243096642302441386519967993 182322481726831039889975995)
    ·
      refine ⟨273483722590246559834963993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182322481726831039889975995 273483722590246559834963993)
      ·
        refine ⟨205112791942684919876222995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273483722590246559834963993 205112791942684919876222995)
        ·
          refine ⟨307669187914027379814334493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205112791942684919876222995 307669187914027379814334493)
          ·
            refine ⟨115375945467760267430375435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307669187914027379814334493 115375945467760267430375435)
            ·
              refine ⟨173063918201640401145563153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115375945467760267430375435 173063918201640401145563153)
              ·
                refine ⟨129797938651230300859172365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173063918201640401145563153 129797938651230300859172365)
                ·
                  refine ⟨48674226994211362822189637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129797938651230300859172365 48674226994211362822189637)
                  ·
                    refine ⟨9126417561414630529160557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48674226994211362822189637 9126417561414630529160557)
                    ·
                      refine ⟨3422406585530486448435209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9126417561414630529160557 3422406585530486448435209)
                      ·
                        rfl

theorem cell23_6665113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_6665113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665113 prefixEnd_6665113 := by exact prefixLift 6665113
  have htrace : WordTrace (prefixWord ++ tailWord_6665113) baseStart_6665113 baseEnd_6665113 := by
    simpa [prefixWord, tailWord_6665113, baseEnd_6665113] using wordTrace_append hprefix tailTrace_6665113
  have hstable : (prefixWord ++ tailWord_6665113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665113).length < 2 ^ (prefixWord ++ tailWord_6665113).sum := by decide
  have hdescent : baseEnd_6665113 < baseStart_6665113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665137 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 3, 4]
def baseStart_6665137 : Nat := 118140960795 + 6665137 * 2 ^ 59
def prefixEnd_6665137 : Nat := 4983230072969 + 3 ^ 40 * 6665137 * 2
def baseEnd_6665137 : Nat := 1140806303022064784845033

theorem tailTrace_6665137 : CollatzResearch.WordTrace tailWord_6665137 prefixEnd_6665137 1140806303022064784845033 := by
  unfold tailWord_6665137
  simp only [CollatzResearch.WordTrace]
  refine ⟨243097517654354438618841665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162065011769569625745894443 243097517654354438618841665)
  ·
    refine ⟨182323138240765828964131249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243097517654354438618841665 182323138240765828964131249)
    ·
      refine ⟨136742353680574371723098437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182323138240765828964131249 136742353680574371723098437)
      ·
        refine ⟨25639191315107694698080957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136742353680574371723098437 25639191315107694698080957)
        ·
          refine ⟨9614696743165385511780359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25639191315107694698080957 9614696743165385511780359)
          ·
            refine ⟨14422045114748078267670539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9614696743165385511780359 14422045114748078267670539)
            ·
              refine ⟨21633067672122117401505809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14422045114748078267670539 21633067672122117401505809)
              ·
                refine ⟨16224800754091588051129357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21633067672122117401505809 16224800754091588051129357)
                ·
                  refine ⟨6084300282784345519173509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16224800754091588051129357 6084300282784345519173509)
                  ·
                    refine ⟨1140806303022064784845033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084300282784345519173509 1140806303022064784845033)
                    ·
                      rfl

theorem cell23_6665137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_6665137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665137 prefixEnd_6665137 := by exact prefixLift 6665137
  have htrace : WordTrace (prefixWord ++ tailWord_6665137) baseStart_6665137 baseEnd_6665137 := by
    simpa [prefixWord, tailWord_6665137, baseEnd_6665137] using wordTrace_append hprefix tailTrace_6665137
  have hstable : (prefixWord ++ tailWord_6665137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665137).length < 2 ^ (prefixWord ++ tailWord_6665137).sum := by decide
  have hdescent : baseEnd_6665137 < baseStart_6665137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665170 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6665170 : Nat := 118140960795 + 6665170 * 2 ^ 59
def prefixEnd_6665170 : Nat := 4983230072969 + 3 ^ 40 * 6665170 * 2
def baseEnd_6665170 : Nat := 3422435853927792725422447

theorem tailTrace_6665170 : CollatzResearch.WordTrace tailWord_6665170 prefixEnd_6665170 3422435853927792725422447 := by
  unfold tailWord_6665170
  simp only [CollatzResearch.WordTrace]
  refine ⟨60774680315808721313698241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162065814175489923503195309 60774680315808721313698241)
  ·
    refine ⟨45581010236856540985273681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60774680315808721313698241 45581010236856540985273681)
    ·
      refine ⟨34185757677642405738955261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45581010236856540985273681 34185757677642405738955261)
      ·
        refine ⟨12819659129115902152108223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34185757677642405738955261 12819659129115902152108223)
        ·
          refine ⟨19229488693673853228162335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12819659129115902152108223 19229488693673853228162335)
          ·
            refine ⟨28844233040510779842243503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19229488693673853228162335 28844233040510779842243503)
            ·
              refine ⟨43266349560766169763365255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28844233040510779842243503 43266349560766169763365255)
              ·
                refine ⟨64899524341149254645047883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43266349560766169763365255 64899524341149254645047883)
                ·
                  refine ⟨97349286511723881967571825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64899524341149254645047883 97349286511723881967571825)
                  ·
                    refine ⟨73011964883792911475678869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97349286511723881967571825 73011964883792911475678869)
                    ·
                      refine ⟨3422435853927792725422447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73011964883792911475678869 3422435853927792725422447)
                      ·
                        rfl

theorem cell23_6665170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6665170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665170 prefixEnd_6665170 := by exact prefixLift 6665170
  have htrace : WordTrace (prefixWord ++ tailWord_6665170) baseStart_6665170 baseEnd_6665170 := by
    simpa [prefixWord, tailWord_6665170, baseEnd_6665170] using wordTrace_append hprefix tailTrace_6665170
  have hstable : (prefixWord ++ tailWord_6665170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665170).length < 2 ^ (prefixWord ++ tailWord_6665170).sum := by decide
  have hdescent : baseEnd_6665170 < baseStart_6665170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665177 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 3]
def baseStart_6665177 : Nat := 118140960795 + 6665177 * 2 ^ 59
def prefixEnd_6665177 : Nat := 4983230072969 + 3 ^ 40 * 6665177 * 2
def baseEnd_6665177 : Nat := 3422439448292374198034915

theorem tailTrace_6665177 : CollatzResearch.WordTrace tailWord_6665177 prefixEnd_6665177 3422439448292374198034915 := by
  unfold tailWord_6665177
  simp only [CollatzResearch.WordTrace]
  refine ⟨243098976574209525450297785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162065984382806350300198523 243098976574209525450297785)
  ·
    refine ⟨182324232430657144087723339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243098976574209525450297785 182324232430657144087723339)
    ·
      refine ⟨273486348645985716131585009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182324232430657144087723339 273486348645985716131585009)
      ·
        refine ⟨205114761484489287098688757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273486348645985716131585009 205114761484489287098688757)
        ·
          refine ⟨19229508889170870665502071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205114761484489287098688757 19229508889170870665502071)
          ·
            refine ⟨28844263333756305998253107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19229508889170870665502071 28844263333756305998253107)
            ·
              refine ⟨43266395000634458997379661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28844263333756305998253107 43266395000634458997379661)
              ·
                refine ⟨16224898125237922124017373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43266395000634458997379661 16224898125237922124017373)
                ·
                  refine ⟨6084336796964220796506515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16224898125237922124017373 6084336796964220796506515)
                  ·
                    refine ⟨9126505195446331194759773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6084336796964220796506515 9126505195446331194759773)
                    ·
                      refine ⟨3422439448292374198034915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9126505195446331194759773 3422439448292374198034915)
                      ·
                        rfl

theorem cell23_6665177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_6665177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665177 prefixEnd_6665177 := by exact prefixLift 6665177
  have htrace : WordTrace (prefixWord ++ tailWord_6665177) baseStart_6665177 baseEnd_6665177 := by
    simpa [prefixWord, tailWord_6665177, baseEnd_6665177] using wordTrace_append hprefix tailTrace_6665177
  have hstable : (prefixWord ++ tailWord_6665177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665177).length < 2 ^ (prefixWord ++ tailWord_6665177).sum := by decide
  have hdescent : baseEnd_6665177 < baseStart_6665177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665200 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 8, 2]
def baseStart_6665200 : Nat := 118140960795 + 6665200 * 2 ^ 59
def prefixEnd_6665200 : Nat := 4983230072969 + 3 ^ 40 * 6665200 * 2
def baseEnd_6665200 : Nat := 3422451258347427608047309

theorem tailTrace_6665200 : CollatzResearch.WordTrace tailWord_6665200 prefixEnd_6665200 3422451258347427608047309 := by
  unfold tailWord_6665200
  simp only [CollatzResearch.WordTrace]
  refine ⟨121549907726563100189192527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162066543635417466918923369 121549907726563100189192527)
  ·
    refine ⟨182324861589844650283788791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121549907726563100189192527 182324861589844650283788791)
    ·
      refine ⟨273487292384766975425683187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182324861589844650283788791 273487292384766975425683187)
      ·
        refine ⟨410230938577150463138524781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273487292384766975425683187 410230938577150463138524781)
        ·
          refine ⟨153836601966431423676946793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410230938577150463138524781 153836601966431423676946793)
          ·
            refine ⟨115377451474823567757710095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153836601966431423676946793 115377451474823567757710095)
            ·
              refine ⟨173066177212235351636565143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115377451474823567757710095 173066177212235351636565143)
              ·
                refine ⟨259599265818353027454847715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173066177212235351636565143 259599265818353027454847715)
                ·
                  refine ⟨389398898727529541182271573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259599265818353027454847715 389398898727529541182271573)
                  ·
                    refine ⟨4563268344463236810729745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 389398898727529541182271573 4563268344463236810729745)
                    ·
                      refine ⟨3422451258347427608047309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563268344463236810729745 3422451258347427608047309)
                      ·
                        rfl

theorem cell23_6665200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 8, 2].length) (baseStart_6665200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665200 prefixEnd_6665200 := by exact prefixLift 6665200
  have htrace : WordTrace (prefixWord ++ tailWord_6665200) baseStart_6665200 baseEnd_6665200 := by
    simpa [prefixWord, tailWord_6665200, baseEnd_6665200] using wordTrace_append hprefix tailTrace_6665200
  have hstable : (prefixWord ++ tailWord_6665200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665200).length < 2 ^ (prefixWord ++ tailWord_6665200).sum := by decide
  have hdescent : baseEnd_6665200 < baseStart_6665200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665205 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6665205 : Nat := 118140960795 + 6665205 * 2 ^ 59
def prefixEnd_6665205 : Nat := 4983230072969 + 3 ^ 40 * 6665205 * 2
def baseEnd_6665205 : Nat := 1140817941916900029494929

theorem tailTrace_6665205 : CollatzResearch.WordTrace tailWord_6665205 prefixEnd_6665205 1140817941916900029494929 := by
  unfold tailWord_6665205
  simp only [CollatzResearch.WordTrace]
  refine ⟨243099997818108086232317069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162066665212072057488211379 243099997818108086232317069)
  ·
    refine ⟨91162499181790532337118901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243099997818108086232317069 91162499181790532337118901)
    ·
      refine ⟨8546484298292862406604897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91162499181790532337118901 8546484298292862406604897)
      ·
        refine ⟨6409863223719646804953673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8546484298292862406604897 6409863223719646804953673)
        ·
          refine ⟨4807397417789735103715255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6409863223719646804953673 4807397417789735103715255)
          ·
            refine ⟨7211096126684602655572883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807397417789735103715255 7211096126684602655572883)
            ·
              refine ⟨10816644190026903983359325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211096126684602655572883 10816644190026903983359325)
              ·
                refine ⟨4056241571260088993759747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10816644190026903983359325 4056241571260088993759747)
                ·
                  refine ⟨6084362356890133490639621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056241571260088993759747 6084362356890133490639621)
                  ·
                    refine ⟨1140817941916900029494929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084362356890133490639621 1140817941916900029494929)
                    ·
                      rfl

theorem cell23_6665205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6665205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665205 prefixEnd_6665205 := by exact prefixLift 6665205
  have htrace : WordTrace (prefixWord ++ tailWord_6665205) baseStart_6665205 baseEnd_6665205 := by
    simpa [prefixWord, tailWord_6665205, baseEnd_6665205] using wordTrace_append hprefix tailTrace_6665205
  have hstable : (prefixWord ++ tailWord_6665205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665205).length < 2 ^ (prefixWord ++ tailWord_6665205).sum := by decide
  have hdescent : baseEnd_6665205 < baseStart_6665205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665217 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_6665217 : Nat := 118140960795 + 6665217 * 2 ^ 59
def prefixEnd_6665217 : Nat := 4983230072969 + 3 ^ 40 * 6665217 * 2
def baseEnd_6665217 : Nat := 3422459987518554041534731

theorem tailTrace_6665217 : CollatzResearch.WordTrace tailWord_6665217 prefixEnd_6665217 3422459987518554041534731 := by
  unfold tailWord_6665217
  simp only [CollatzResearch.WordTrace]
  refine ⟨243100435494064612281753905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162066956996043074854502603 243100435494064612281753905)
  ·
    refine ⟨182325326620548459211315429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243100435494064612281753905 182325326620548459211315429)
    ·
      refine ⟨34185998741352836102121643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182325326620548459211315429 34185998741352836102121643)
      ·
        refine ⟨51278998112029254153182465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34185998741352836102121643 51278998112029254153182465)
        ·
          refine ⟨38459248584021940614886849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51278998112029254153182465 38459248584021940614886849)
          ·
            refine ⟨28844436438016455461165137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38459248584021940614886849 28844436438016455461165137)
            ·
              refine ⟨21633327328512341595873853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28844436438016455461165137 21633327328512341595873853)
              ·
                refine ⟨8112497748192128098452695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21633327328512341595873853 8112497748192128098452695)
                ·
                  refine ⟨12168746622288192147679043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8112497748192128098452695 12168746622288192147679043)
                  ·
                    refine ⟨18253119933432288221518565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12168746622288192147679043 18253119933432288221518565)
                    ·
                      refine ⟨3422459987518554041534731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18253119933432288221518565 3422459987518554041534731)
                      ·
                        rfl

theorem cell23_6665217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_6665217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665217 prefixEnd_6665217 := by exact prefixLift 6665217
  have htrace : WordTrace (prefixWord ++ tailWord_6665217) baseStart_6665217 baseEnd_6665217 := by
    simpa [prefixWord, tailWord_6665217, baseEnd_6665217] using wordTrace_append hprefix tailTrace_6665217
  have hstable : (prefixWord ++ tailWord_6665217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665217).length < 2 ^ (prefixWord ++ tailWord_6665217).sum := by decide
  have hdescent : baseEnd_6665217 < baseStart_6665217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665230 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6665230 : Nat := 118140960795 + 6665230 * 2 ^ 59
def prefixEnd_6665230 : Nat := 4983230072969 + 3 ^ 40 * 6665230 * 2
def baseEnd_6665230 : Nat := 3422466662767062490672171

theorem tailTrace_6665230 : CollatzResearch.WordTrace tailWord_6665230 prefixEnd_6665230 3422466662767062490672171 := by
  unfold tailWord_6665230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30387613705377189437747143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162067273095345010334651429 30387613705377189437747143)
  ·
    refine ⟨45581420558065784156620715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30387613705377189437747143 45581420558065784156620715)
    ·
      refine ⟨68372130837098676234931073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45581420558065784156620715 68372130837098676234931073)
      ·
        refine ⟨51279098127824007176198305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68372130837098676234931073 51279098127824007176198305)
        ·
          refine ⟨38459323595868005382148729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51279098127824007176198305 38459323595868005382148729)
          ·
            refine ⟨28844492696901004036611547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38459323595868005382148729 28844492696901004036611547)
            ·
              refine ⟨43266739045351506054917321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28844492696901004036611547 43266739045351506054917321)
              ·
                refine ⟨32450054284013629541187991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43266739045351506054917321 32450054284013629541187991)
                ·
                  refine ⟨48675081426020444311781987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32450054284013629541187991 48675081426020444311781987)
                  ·
                    refine ⟨73012622139030666467672981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48675081426020444311781987 73012622139030666467672981)
                    ·
                      refine ⟨3422466662767062490672171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73012622139030666467672981 3422466662767062490672171)
                      ·
                        rfl

theorem cell23_6665230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6665230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665230 prefixEnd_6665230 := by exact prefixLift 6665230
  have htrace : WordTrace (prefixWord ++ tailWord_6665230) baseStart_6665230 baseEnd_6665230 := by
    simpa [prefixWord, tailWord_6665230, baseEnd_6665230] using wordTrace_append hprefix tailTrace_6665230
  have hstable : (prefixWord ++ tailWord_6665230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665230).length < 2 ^ (prefixWord ++ tailWord_6665230).sum := by decide
  have hdescent : baseEnd_6665230 < baseStart_6665230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665240 : List Nat := [2, 1, 2, 3, 2, 3, 2, 8]
def baseStart_6665240 : Nat := 118140960795 + 6665240 * 2 ^ 59
def prefixEnd_6665240 : Nat := 4983230072969 + 3 ^ 40 * 6665240 * 2
def baseEnd_6665240 : Nat := 126758214724948424131375

theorem tailTrace_6665240 : CollatzResearch.WordTrace tailWord_6665240 prefixEnd_6665240 126758214724948424131375 := by
  unfold tailWord_6665240
  simp only [CollatzResearch.WordTrace]
  refine ⟨121550637186490643604920587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162067516248654191473227449 121550637186490643604920587)
  ·
    refine ⟨182325955779735965407380881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121550637186490643604920587 182325955779735965407380881)
    ·
      refine ⟨136744466834801974055535661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182325955779735965407380881 136744466834801974055535661)
      ·
        refine ⟨51279175063050740270825873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136744466834801974055535661 51279175063050740270825873)
        ·
          refine ⟨38459381297288055203119405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51279175063050740270825873 38459381297288055203119405)
          ·
            refine ⟨14422267986483020701169777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38459381297288055203119405 14422267986483020701169777)
            ·
              refine ⟨10816700989862265525877333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14422267986483020701169777 10816700989862265525877333)
              ·
                refine ⟨126758214724948424131375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10816700989862265525877333 126758214724948424131375)
                ·
                  rfl

theorem cell23_6665240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 8].length) (baseStart_6665240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665240 prefixEnd_6665240 := by exact prefixLift 6665240
  have htrace : WordTrace (prefixWord ++ tailWord_6665240) baseStart_6665240 baseEnd_6665240 := by
    simpa [prefixWord, tailWord_6665240, baseEnd_6665240] using wordTrace_append hprefix tailTrace_6665240
  have hstable : (prefixWord ++ tailWord_6665240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665240).length < 2 ^ (prefixWord ++ tailWord_6665240).sum := by decide
  have hdescent : baseEnd_6665240 < baseStart_6665240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665244 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6665244 : Nat := 118140960795 + 6665244 * 2 ^ 59
def prefixEnd_6665244 : Nat := 4983230072969 + 3 ^ 40 * 6665244 * 2
def baseEnd_6665244 : Nat := 1140824617165408478632369

theorem tailTrace_6665244 : CollatzResearch.WordTrace tailWord_6665244 prefixEnd_6665244 1140824617165408478632369 := by
  unfold tailWord_6665244
  simp only [CollatzResearch.WordTrace]
  refine ⟨121550710132483397946493393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162067613509977863928657857 121550710132483397946493393)
  ·
    refine ⟨91163032599362548459870045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121550710132483397946493393 91163032599362548459870045)
    ·
      refine ⟨34186137224760955672451267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91163032599362548459870045 34186137224760955672451267)
      ·
        refine ⟨51279205837141433508676901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34186137224760955672451267 51279205837141433508676901)
        ·
          refine ⟨9614851094464018782876919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51279205837141433508676901 9614851094464018782876919)
          ·
            refine ⟨14422276641696028174315379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9614851094464018782876919 14422276641696028174315379)
            ·
              refine ⟨21633414962544042261473069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14422276641696028174315379 21633414962544042261473069)
              ·
                refine ⟨8112530610954015848052401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21633414962544042261473069 8112530610954015848052401)
                ·
                  refine ⟨6084397958215511886039301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8112530610954015848052401 6084397958215511886039301)
                  ·
                    refine ⟨1140824617165408478632369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084397958215511886039301 1140824617165408478632369)
                    ·
                      rfl

theorem cell23_6665244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6665244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665244 prefixEnd_6665244 := by exact prefixLift 6665244
  have htrace : WordTrace (prefixWord ++ tailWord_6665244) baseStart_6665244 baseEnd_6665244 := by
    simpa [prefixWord, tailWord_6665244, baseEnd_6665244] using wordTrace_append hprefix tailTrace_6665244
  have hstable : (prefixWord ++ tailWord_6665244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665244).length < 2 ^ (prefixWord ++ tailWord_6665244).sum := by decide
  have hdescent : baseEnd_6665244 < baseStart_6665244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665263 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_6665263 : Nat := 118140960795 + 6665263 * 2 ^ 59
def prefixEnd_6665263 : Nat := 4983230072969 + 3 ^ 40 * 6665263 * 2
def baseEnd_6665263 : Nat := 3422483607628660861559519

theorem tailTrace_6665263 : CollatzResearch.WordTrace tailWord_6665263 prefixEnd_6665263 3422483607628660861559519 := by
  unfold tailWord_6665263
  simp only [CollatzResearch.WordTrace]
  refine ⟨243102113251897962137928443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162068075501265308091952295 243102113251897962137928443)
  ·
    refine ⟨364653169877846943206892665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243102113251897962137928443 364653169877846943206892665)
    ·
      refine ⟨273489877408385207405169499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364653169877846943206892665 273489877408385207405169499)
      ·
        refine ⟨410234816112577811107754249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273489877408385207405169499 410234816112577811107754249)
        ·
          refine ⟨307676112084433358330815687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410234816112577811107754249 307676112084433358330815687)
          ·
            refine ⟨461514168126650037496223531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307676112084433358330815687 461514168126650037496223531)
            ·
              refine ⟨692271252189975056244335297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461514168126650037496223531 692271252189975056244335297)
              ·
                refine ⟨519203439142481292183251473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692271252189975056244335297 519203439142481292183251473)
                ·
                  refine ⟨389402579356860969137438605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519203439142481292183251473 389402579356860969137438605)
                  ·
                    refine ⟨146025967258822863426539477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389402579356860969137438605 146025967258822863426539477)
                    ·
                      refine ⟨3422483607628660861559519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146025967258822863426539477 3422483607628660861559519)
                      ·
                        rfl

theorem cell23_6665263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_6665263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665263 prefixEnd_6665263 := by exact prefixLift 6665263
  have htrace : WordTrace (prefixWord ++ tailWord_6665263) baseStart_6665263 baseEnd_6665263 := by
    simpa [prefixWord, tailWord_6665263, baseEnd_6665263] using wordTrace_append hprefix tailTrace_6665263
  have hstable : (prefixWord ++ tailWord_6665263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665263).length < 2 ^ (prefixWord ++ tailWord_6665263).sum := by decide
  have hdescent : baseEnd_6665263 < baseStart_6665263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665290 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_6665290 : Nat := 118140960795 + 6665290 * 2 ^ 59
def prefixEnd_6665290 : Nat := 4983230072969 + 3 ^ 40 * 6665290 * 2
def baseEnd_6665290 : Nat := 3422497471606332255921895

theorem tailTrace_6665290 : CollatzResearch.WordTrace tailWord_6665290 prefixEnd_6665290 3422497471606332255921895 := by
  unfold tailWord_6665290
  simp only [CollatzResearch.WordTrace]
  refine ⟨60775774505700036437290331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162068732015200097166107549 60775774505700036437290331)
  ·
    refine ⟨91163661758550054655935497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60775774505700036437290331 91163661758550054655935497)
    ·
      refine ⟨68372746318912540991951623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91163661758550054655935497 68372746318912540991951623)
      ·
        refine ⟨102559119478368811487927435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68372746318912540991951623 102559119478368811487927435)
        ·
          refine ⟨153838679217553217231891153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102559119478368811487927435 153838679217553217231891153)
          ·
            refine ⟨115379009413164912923918365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153838679217553217231891153 115379009413164912923918365)
            ·
              refine ⟨43267128529936842346469387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115379009413164912923918365 43267128529936842346469387)
              ·
                refine ⟨64900692794905263519704081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43267128529936842346469387 64900692794905263519704081)
                ·
                  refine ⟨48675519596178947639778061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64900692794905263519704081 48675519596178947639778061)
                  ·
                    refine ⟨18253319848567105364916773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48675519596178947639778061 18253319848567105364916773)
                    ·
                      refine ⟨3422497471606332255921895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18253319848567105364916773 3422497471606332255921895)
                      ·
                        rfl

theorem cell23_6665290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_6665290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665290 prefixEnd_6665290 := by exact prefixLift 6665290
  have htrace : WordTrace (prefixWord ++ tailWord_6665290) baseStart_6665290 baseEnd_6665290 := by
    simpa [prefixWord, tailWord_6665290, baseEnd_6665290] using wordTrace_append hprefix tailTrace_6665290
  have hstable : (prefixWord ++ tailWord_6665290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665290).length < 2 ^ (prefixWord ++ tailWord_6665290).sum := by decide
  have hdescent : baseEnd_6665290 < baseStart_6665290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665300 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_6665300 : Nat := 118140960795 + 6665300 * 2 ^ 59
def prefixEnd_6665300 : Nat := 4983230072969 + 3 ^ 40 * 6665300 * 2
def baseEnd_6665300 : Nat := 1140834202137625738932283

theorem tailTrace_6665300 : CollatzResearch.WordTrace tailWord_6665300 prefixEnd_6665300 1140834202137625738932283 := by
  unfold tailWord_6665300
  simp only [CollatzResearch.WordTrace]
  refine ⟨121551731376381958728512677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162068975168509278304683569 121551731376381958728512677)
  ·
    refine ⟨22790949633071617261596127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121551731376381958728512677 22790949633071617261596127)
    ·
      refine ⟨34186424449607425892394191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22790949633071617261596127 34186424449607425892394191)
      ·
        refine ⟨51279636674411138838591287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34186424449607425892394191 51279636674411138838591287)
        ·
          refine ⟨76919455011616708257886931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51279636674411138838591287 76919455011616708257886931)
          ·
            refine ⟨115379182517425062386830397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76919455011616708257886931 115379182517425062386830397)
            ·
              refine ⟨43267193444034398395061399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115379182517425062386830397 43267193444034398395061399)
              ·
                refine ⟨64900790166051597592592099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43267193444034398395061399 64900790166051597592592099)
                ·
                  refine ⟨97351185249077396388888149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64900790166051597592592099 97351185249077396388888149)
                  ·
                    refine ⟨1140834202137625738932283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97351185249077396388888149 1140834202137625738932283)
                    ·
                      rfl

theorem cell23_6665300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_6665300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665300 prefixEnd_6665300 := by exact prefixLift 6665300
  have htrace : WordTrace (prefixWord ++ tailWord_6665300) baseStart_6665300 baseEnd_6665300 := by
    simpa [prefixWord, tailWord_6665300, baseEnd_6665300] using wordTrace_append hprefix tailTrace_6665300
  have hstable : (prefixWord ++ tailWord_6665300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665300).length < 2 ^ (prefixWord ++ tailWord_6665300).sum := by decide
  have hdescent : baseEnd_6665300 < baseStart_6665300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665324 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 4, 2, 2]
def baseStart_6665324 : Nat := 118140960795 + 6665324 * 2 ^ 59
def prefixEnd_6665324 : Nat := 4983230072969 + 3 ^ 40 * 6665324 * 2
def baseEnd_6665324 : Nat := 3422514929948585122896739

theorem tailTrace_6665324 : CollatzResearch.WordTrace tailWord_6665324 prefixEnd_6665324 3422514929948585122896739 := by
  unfold tailWord_6665324
  simp only [CollatzResearch.WordTrace]
  refine ⟨121552169052338484777949513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162069558736451313037266017 121552169052338484777949513)
  ·
    refine ⟨91164126789253863583462135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121552169052338484777949513 91164126789253863583462135)
    ·
      refine ⟨136746190183880795375193203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91164126789253863583462135 136746190183880795375193203)
      ·
        refine ⟨205119285275821193062789805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136746190183880795375193203 205119285275821193062789805)
        ·
          refine ⟨76919731978432947398546177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205119285275821193062789805 76919731978432947398546177)
          ·
            refine ⟨57689798983824710548909633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76919731978432947398546177 57689798983824710548909633)
            ·
              refine ⟨43267349237868532911682225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57689798983824710548909633 43267349237868532911682225)
              ·
                refine ⟨32450511928401399683761669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43267349237868532911682225 32450511928401399683761669)
                ·
                  refine ⟨6084470986575262440705313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32450511928401399683761669 6084470986575262440705313)
                  ·
                    refine ⟨4563353239931446830528985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6084470986575262440705313 4563353239931446830528985)
                    ·
                      refine ⟨3422514929948585122896739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563353239931446830528985 3422514929948585122896739)
                      ·
                        rfl

theorem cell23_6665324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_6665324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665324 prefixEnd_6665324 := by exact prefixLift 6665324
  have htrace : WordTrace (prefixWord ++ tailWord_6665324) baseStart_6665324 baseEnd_6665324 := by
    simpa [prefixWord, tailWord_6665324, baseEnd_6665324] using wordTrace_append hprefix tailTrace_6665324
  have hstable : (prefixWord ++ tailWord_6665324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665324).length < 2 ^ (prefixWord ++ tailWord_6665324).sum := by decide
  have hdescent : baseEnd_6665324 < baseStart_6665324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665330 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_6665330 : Nat := 118140960795 + 6665330 * 2 ^ 59
def prefixEnd_6665330 : Nat := 4983230072969 + 3 ^ 40 * 6665330 * 2
def baseEnd_6665330 : Nat := 380279778981390233269079

theorem tailTrace_6665330 : CollatzResearch.WordTrace tailWord_6665330 prefixEnd_6665330 380279778981390233269079 := by
  unfold tailWord_6665330
  simp only [CollatzResearch.WordTrace]
  refine ⟨60776139235663808145154361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162069704628436821720411629 60776139235663808145154361)
  ·
    refine ⟨45582104426747856108865771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60776139235663808145154361 45582104426747856108865771)
    ·
      refine ⟨68373156640121784163298657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45582104426747856108865771 68373156640121784163298657)
      ·
        refine ⟨51279867480091338122473993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68373156640121784163298657 51279867480091338122473993)
        ·
          refine ⟨38459900610068503591855495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51279867480091338122473993 38459900610068503591855495)
          ·
            refine ⟨57689850915102755387783243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38459900610068503591855495 57689850915102755387783243)
            ·
              refine ⟨86534776372654133081674865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57689850915102755387783243 86534776372654133081674865)
              ·
                refine ⟨64901082279490599811256149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86534776372654133081674865 64901082279490599811256149)
                ·
                  refine ⟨380279778981390233269079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64901082279490599811256149 380279778981390233269079)
                  ·
                    rfl

theorem cell23_6665330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_6665330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665330 prefixEnd_6665330 := by exact prefixLift 6665330
  have htrace : WordTrace (prefixWord ++ tailWord_6665330) baseStart_6665330 baseEnd_6665330 := by
    simpa [prefixWord, tailWord_6665330, baseEnd_6665330] using wordTrace_append hprefix tailTrace_6665330
  have hstable : (prefixWord ++ tailWord_6665330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665330).length < 2 ^ (prefixWord ++ tailWord_6665330).sum := by decide
  have hdescent : baseEnd_6665330 < baseStart_6665330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665347 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 5]
def baseStart_6665347 : Nat := 118140960795 + 6665347 * 2 ^ 59
def prefixEnd_6665347 : Nat := 4983230072969 + 3 ^ 40 * 6665347 * 2
def baseEnd_6665347 : Nat := 380280748889293170323237

theorem tailTrace_6665347 : CollatzResearch.WordTrace tailWord_6665347 prefixEnd_6665347 380280748889293170323237 := by
  unfold tailWord_6665347
  simp only [CollatzResearch.WordTrace]
  refine ⟨243105176983593644483986295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162070117989062429655990863 243105176983593644483986295)
  ·
    refine ⟨364657765475390466725979443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243105176983593644483986295 364657765475390466725979443)
    ·
      refine ⟨546986648213085700088969165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364657765475390466725979443 546986648213085700088969165)
      ·
        refine ⟨205119993079907137533363437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546986648213085700088969165 205119993079907137533363437)
        ·
          refine ⟨76919997404965176575011289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205119993079907137533363437 76919997404965176575011289)
          ·
            refine ⟨57689998053723882431258467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76919997404965176575011289 57689998053723882431258467)
            ·
              refine ⟨86534997080585823646887701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57689998053723882431258467 86534997080585823646887701)
              ·
                refine ⟨4056327988152460483447861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86534997080585823646887701 4056327988152460483447861)
                ·
                  refine ⟨380280748889293170323237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056327988152460483447861 380280748889293170323237)
                  ·
                    rfl

theorem cell23_6665347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 5].length) (baseStart_6665347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665347 prefixEnd_6665347 := by exact prefixLift 6665347
  have htrace : WordTrace (prefixWord ++ tailWord_6665347) baseStart_6665347 baseEnd_6665347 := by
    simpa [prefixWord, tailWord_6665347, baseEnd_6665347] using wordTrace_append hprefix tailTrace_6665347
  have hstable : (prefixWord ++ tailWord_6665347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665347).length < 2 ^ (prefixWord ++ tailWord_6665347).sum := by decide
  have hdescent : baseEnd_6665347 < baseStart_6665347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665360 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_6665360 : Nat := 118140960795 + 6665360 * 2 ^ 59
def prefixEnd_6665360 : Nat := 4983230072969 + 3 ^ 40 * 6665360 * 2
def baseEnd_6665360 : Nat := 1140844471750715660682191

theorem tailTrace_6665360 : CollatzResearch.WordTrace tailWord_6665360 prefixEnd_6665360 1140844471750715660682191 := by
  unfold tailWord_6665360
  simp only [CollatzResearch.WordTrace]
  refine ⟨121552825566273273852104767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162070434088364365136139689 121552825566273273852104767)
  ·
    refine ⟨182329238349409910778157151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121552825566273273852104767 182329238349409910778157151)
    ·
      refine ⟨273493857524114866167235727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182329238349409910778157151 273493857524114866167235727)
      ·
        refine ⟨410240786286172299250853591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273493857524114866167235727 410240786286172299250853591)
        ·
          refine ⟨615361179429258448876280387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410240786286172299250853591 615361179429258448876280387)
          ·
            refine ⟨923041769143887673314420581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615361179429258448876280387 923041769143887673314420581)
            ·
              refine ⟨173070331714478938746453859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 923041769143887673314420581 173070331714478938746453859)
              ·
                refine ⟨259605497571718408119680789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173070331714478938746453859 259605497571718408119680789)
                ·
                  refine ⟨12169007698674300380610037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 259605497571718408119680789 12169007698674300380610037)
                  ·
                    refine ⟨1140844471750715660682191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12169007698674300380610037 1140844471750715660682191)
                    ·
                      rfl

theorem cell23_6665360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_6665360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665360 prefixEnd_6665360 := by exact prefixLift 6665360
  have htrace : WordTrace (prefixWord ++ tailWord_6665360) baseStart_6665360 baseEnd_6665360 := by
    simpa [prefixWord, tailWord_6665360, baseEnd_6665360] using wordTrace_append hprefix tailTrace_6665360
  have hstable : (prefixWord ++ tailWord_6665360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665360).length < 2 ^ (prefixWord ++ tailWord_6665360).sum := by decide
  have hdescent : baseEnd_6665360 < baseStart_6665360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665377 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 2, 5]
def baseStart_6665377 : Nat := 118140960795 + 6665377 * 2 ^ 59
def prefixEnd_6665377 : Nat := 4983230072969 + 3 ^ 40 * 6665377 * 2
def baseEnd_6665377 : Nat := 1140847381474424471844665

theorem tailTrace_6665377 : CollatzResearch.WordTrace tailWord_6665377 prefixEnd_6665377 1140847381474424471844665 := by
  unfold tailWord_6665377
  simp only [CollatzResearch.WordTrace]
  refine ⟨243106271173484959607578385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162070847448989973071718923 243106271173484959607578385)
  ·
    refine ⟨182329703380113719705683789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243106271173484959607578385 182329703380113719705683789)
    ·
      refine ⟨68373638767542644889631421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182329703380113719705683789 68373638767542644889631421)
      ·
        refine ⟨25640114537828491833611783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68373638767542644889631421 25640114537828491833611783)
        ·
          refine ⟨38460171806742737750417675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25640114537828491833611783 38460171806742737750417675)
          ·
            refine ⟨57690257710114106625626513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38460171806742737750417675 57690257710114106625626513)
            ·
              refine ⟨43267693282585579969219885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57690257710114106625626513 43267693282585579969219885)
              ·
                refine ⟨16225384980969592488457457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43267693282585579969219885 16225384980969592488457457)
                ·
                  refine ⟨12169038735727194366343093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16225384980969592488457457 12169038735727194366343093)
                  ·
                    refine ⟨1140847381474424471844665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12169038735727194366343093 1140847381474424471844665)
                    ·
                      rfl

theorem cell23_6665377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_6665377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665377 prefixEnd_6665377 := by exact prefixLift 6665377
  have htrace : WordTrace (prefixWord ++ tailWord_6665377) baseStart_6665377 baseEnd_6665377 := by
    simpa [prefixWord, tailWord_6665377, baseEnd_6665377] using wordTrace_append hprefix tailTrace_6665377
  have hstable : (prefixWord ++ tailWord_6665377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665377).length < 2 ^ (prefixWord ++ tailWord_6665377).sum := by decide
  have hdescent : baseEnd_6665377 < baseStart_6665377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665398 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_6665398 : Nat := 118140960795 + 6665398 * 2 ^ 59
def prefixEnd_6665398 : Nat := 4983230072969 + 3 ^ 40 * 6665398 * 2
def baseEnd_6665398 : Nat := 380283658613001981485711

theorem tailTrace_6665398 : CollatzResearch.WordTrace tailWord_6665398 prefixEnd_6665398 380283658613001981485711 := by
  unfold tailWord_6665398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15194189819150555012130803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162071358070939253462728565 15194189819150555012130803)
  ·
    refine ⟨22791284728725832518196205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15194189819150555012130803 22791284728725832518196205)
    ·
      refine ⟨8546731773272187194323577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22791284728725832518196205 8546731773272187194323577)
      ·
        refine ⟨6410048829954140395742683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8546731773272187194323577 6410048829954140395742683)
        ·
          refine ⟨9615073244931210593614025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410048829954140395742683 9615073244931210593614025)
          ·
            refine ⟨7211304933698407945210519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9615073244931210593614025 7211304933698407945210519)
            ·
              refine ⟨10816957400547611917815779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211304933698407945210519 10816957400547611917815779)
              ·
                refine ⟨16225436100821417876723669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816957400547611917815779 16225436100821417876723669)
                ·
                  refine ⟨380283658613001981485711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16225436100821417876723669 380283658613001981485711)
                  ·
                    rfl

theorem cell23_6665398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_6665398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665398 prefixEnd_6665398 := by exact prefixLift 6665398
  have htrace : WordTrace (prefixWord ++ tailWord_6665398) baseStart_6665398 baseEnd_6665398 := by
    simpa [prefixWord, tailWord_6665398, baseEnd_6665398] using wordTrace_append hprefix tailTrace_6665398
  have hstable : (prefixWord ++ tailWord_6665398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665398).length < 2 ^ (prefixWord ++ tailWord_6665398).sum := by decide
  have hdescent : baseEnd_6665398 < baseStart_6665398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665400 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_6665400 : Nat := 118140960795 + 6665400 * 2 ^ 59
def prefixEnd_6665400 : Nat := 4983230072969 + 3 ^ 40 * 6665400 * 2
def baseEnd_6665400 : Nat := 3422553954478326825546389

theorem tailTrace_6665400 : CollatzResearch.WordTrace tailWord_6665400 prefixEnd_6665400 3422553954478326825546389 := by
  unfold tailWord_6665400
  simp only [CollatzResearch.WordTrace]
  refine ⟨121553555026200817267832827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162071406701601089690443769 121553555026200817267832827)
  ·
    refine ⟨182330332539301225901749241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121553555026200817267832827 182330332539301225901749241)
    ·
      refine ⟨136747749404475919426311931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182330332539301225901749241 136747749404475919426311931)
      ·
        refine ⟨205121624106713879139467897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136747749404475919426311931 205121624106713879139467897)
        ·
          refine ⟨153841218080035409354600923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205121624106713879139467897 153841218080035409354600923)
          ·
            refine ⟨230761827120053114031901385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153841218080035409354600923 230761827120053114031901385)
            ·
              refine ⟨173071370340039835523926039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230761827120053114031901385 173071370340039835523926039)
              ·
                refine ⟨259607055510059753285889059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173071370340039835523926039 259607055510059753285889059)
                ·
                  refine ⟨389410583265089629928833589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259607055510059753285889059 389410583265089629928833589)
                  ·
                    refine ⟨36507242181102152805828149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 389410583265089629928833589 36507242181102152805828149)
                    ·
                      refine ⟨3422553954478326825546389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36507242181102152805828149 3422553954478326825546389)
                      ·
                        rfl

theorem cell23_6665400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_6665400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665400 prefixEnd_6665400 := by exact prefixLift 6665400
  have htrace : WordTrace (prefixWord ++ tailWord_6665400) baseStart_6665400 baseEnd_6665400 := by
    simpa [prefixWord, tailWord_6665400, baseEnd_6665400] using wordTrace_append hprefix tailTrace_6665400
  have hstable : (prefixWord ++ tailWord_6665400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665400).length < 2 ^ (prefixWord ++ tailWord_6665400).sum := by decide
  have hdescent : baseEnd_6665400 < baseStart_6665400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665458 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_6665458 : Nat := 118140960795 + 6665458 * 2 ^ 59
def prefixEnd_6665458 : Nat := 4983230072969 + 3 ^ 40 * 6665458 * 2
def baseEnd_6665458 : Nat := 1140861245452095866207041

theorem tailTrace_6665458 : CollatzResearch.WordTrace tailWord_6665458 prefixEnd_6665458 1140861245452095866207041 := by
  unfold tailWord_6665458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60777306371547877610319257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162072816990794340294184685 60777306371547877610319257)
  ·
    refine ⟨45582979778660908207739443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60777306371547877610319257 45582979778660908207739443)
    ·
      refine ⟨68374469667991362311609165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45582979778660908207739443 68374469667991362311609165)
      ·
        refine ⟨25640426125496760866853437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68374469667991362311609165 25640426125496760866853437)
        ·
          refine ⟨9615159797061285325070039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25640426125496760866853437 9615159797061285325070039)
          ·
            refine ⟨14422739695591927987605059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9615159797061285325070039 14422739695591927987605059)
            ·
              refine ⟨21634109543387891981407589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14422739695591927987605059 21634109543387891981407589)
              ·
                refine ⟨4056395539385229746513923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21634109543387891981407589 4056395539385229746513923)
                ·
                  refine ⟨6084593309077844619770885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056395539385229746513923 6084593309077844619770885)
                  ·
                    refine ⟨1140861245452095866207041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084593309077844619770885 1140861245452095866207041)
                    ·
                      rfl

theorem cell23_6665458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_6665458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665458 prefixEnd_6665458 := by exact prefixLift 6665458
  have htrace : WordTrace (prefixWord ++ tailWord_6665458) baseStart_6665458 baseEnd_6665458 := by
    simpa [prefixWord, tailWord_6665458, baseEnd_6665458] using wordTrace_append hprefix tailTrace_6665458
  have hstable : (prefixWord ++ tailWord_6665458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665458).length < 2 ^ (prefixWord ++ tailWord_6665458).sum := by decide
  have hdescent : baseEnd_6665458 < baseStart_6665458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665498 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3]
def baseStart_6665498 : Nat := 118140960795 + 6665498 * 2 ^ 59
def prefixEnd_6665498 : Nat := 4983230072969 + 3 ^ 40 * 6665498 * 2
def baseEnd_6665498 : Nat := 3422604275582467442120939

theorem tailTrace_6665498 : CollatzResearch.WordTrace tailWord_6665498 prefixEnd_6665498 3422604275582467442120939 := by
  unfold tailWord_6665498
  simp only [CollatzResearch.WordTrace]
  refine ⟨60777671101511649318183287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162073789604031064848488765 60777671101511649318183287)
  ·
    refine ⟨91166506652267473977274931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60777671101511649318183287 91166506652267473977274931)
    ·
      refine ⟨136749759978401210965912397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91166506652267473977274931 136749759978401210965912397)
      ·
        refine ⟨51281159991900454112217149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136749759978401210965912397 51281159991900454112217149)
        ·
          refine ⟨19230434996962670292081431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51281159991900454112217149 19230434996962670292081431)
          ·
            refine ⟨28845652495444005438122147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19230434996962670292081431 28845652495444005438122147)
            ·
              refine ⟨43268478743166008157183221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28845652495444005438122147 43268478743166008157183221)
              ·
                refine ⟨4056419882171813264735927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43268478743166008157183221 4056419882171813264735927)
                ·
                  refine ⟨6084629823257719897103891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056419882171813264735927 6084629823257719897103891)
                  ·
                    refine ⟨9126944734886579845655837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6084629823257719897103891 9126944734886579845655837)
                    ·
                      refine ⟨3422604275582467442120939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9126944734886579845655837 3422604275582467442120939)
                      ·
                        rfl

theorem cell23_6665498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_6665498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665498 prefixEnd_6665498 := by exact prefixLift 6665498
  have htrace : WordTrace (prefixWord ++ tailWord_6665498) baseStart_6665498 baseEnd_6665498 := by
    simpa [prefixWord, tailWord_6665498, baseEnd_6665498] using wordTrace_append hprefix tailTrace_6665498
  have hstable : (prefixWord ++ tailWord_6665498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665498).length < 2 ^ (prefixWord ++ tailWord_6665498).sum := by decide
  have hdescent : baseEnd_6665498 < baseStart_6665498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665501 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_6665501 : Nat := 118140960795 + 6665501 * 2 ^ 59
def prefixEnd_6665501 : Nat := 4983230072969 + 3 ^ 40 * 6665501 * 2
def baseEnd_6665501 : Nat := 1140868605341476976794475

theorem tailTrace_6665501 : CollatzResearch.WordTrace tailWord_6665501 prefixEnd_6665501 1140868605341476976794475 := by
  unfold tailWord_6665501
  simp only [CollatzResearch.WordTrace]
  refine ⟨243110793825035728785092357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162073862550023819190061571 243110793825035728785092357)
  ·
    refine ⟨45583273842194199147204817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243110793825035728785092357 45583273842194199147204817)
    ·
      refine ⟨34187455381645649360403613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45583273842194199147204817 34187455381645649360403613)
      ·
        refine ⟨12820295768117118510151355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34187455381645649360403613 12820295768117118510151355)
        ·
          refine ⟨19230443652175677765227033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12820295768117118510151355 19230443652175677765227033)
          ·
            refine ⟨14422832739131758323920275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19230443652175677765227033 14422832739131758323920275)
            ·
              refine ⟨21634249108697637485880413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14422832739131758323920275 21634249108697637485880413)
              ·
                refine ⟨8112843415761614057205155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21634249108697637485880413 8112843415761614057205155)
                ·
                  refine ⟨12169265123642421085807733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8112843415761614057205155 12169265123642421085807733)
                  ·
                    refine ⟨1140868605341476976794475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12169265123642421085807733 1140868605341476976794475)
                    ·
                      rfl

theorem cell23_6665501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_6665501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665501 prefixEnd_6665501 := by exact prefixLift 6665501
  have htrace : WordTrace (prefixWord ++ tailWord_6665501) baseStart_6665501 baseEnd_6665501 := by
    simpa [prefixWord, tailWord_6665501, baseEnd_6665501] using wordTrace_append hprefix tailTrace_6665501
  have hstable : (prefixWord ++ tailWord_6665501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665501).length < 2 ^ (prefixWord ++ tailWord_6665501).sum := by decide
  have hdescent : baseEnd_6665501 < baseStart_6665501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665534 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6665534 : Nat := 118140960795 + 6665534 * 2 ^ 59
def prefixEnd_6665534 : Nat := 4983230072969 + 3 ^ 40 * 6665534 * 2
def baseEnd_6665534 : Nat := 3422622760886029301270773

theorem tailTrace_6665534 : CollatzResearch.WordTrace tailWord_6665534 prefixEnd_6665534 3422622760886029301270773 := by
  unfold tailWord_6665534
  simp only [CollatzResearch.WordTrace]
  refine ⟨30388999679239521927630457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162074664955944116947362437 30388999679239521927630457)
  ·
    refine ⟨22791749759429641445722843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30388999679239521927630457 22791749759429641445722843)
    ·
      refine ⟨34187624639144462168584265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22791749759429641445722843 34187624639144462168584265)
      ·
        refine ⟨25640718479358346626438199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34187624639144462168584265 25640718479358346626438199)
        ·
          refine ⟨38461077719037519939657299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25640718479358346626438199 38461077719037519939657299)
          ·
            refine ⟨57691616578556279909485949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38461077719037519939657299 57691616578556279909485949)
            ·
              refine ⟨21634356216958604966057231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57691616578556279909485949 21634356216958604966057231)
              ·
                refine ⟨32451534325437907449085847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21634356216958604966057231 32451534325437907449085847)
                ·
                  refine ⟨48677301488156861173628771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32451534325437907449085847 48677301488156861173628771)
                  ·
                    refine ⟨73015952232235291760443157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48677301488156861173628771 73015952232235291760443157)
                    ·
                      refine ⟨3422622760886029301270773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73015952232235291760443157 3422622760886029301270773)
                      ·
                        rfl

theorem cell23_6665534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6665534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665534 prefixEnd_6665534 := by exact prefixLift 6665534
  have htrace : WordTrace (prefixWord ++ tailWord_6665534) baseStart_6665534 baseEnd_6665534 := by
    simpa [prefixWord, tailWord_6665534, baseEnd_6665534] using wordTrace_append hprefix tailTrace_6665534
  have hstable : (prefixWord ++ tailWord_6665534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665534).length < 2 ^ (prefixWord ++ tailWord_6665534).sum := by decide
  have hdescent : baseEnd_6665534 < baseStart_6665534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665549 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6665549 : Nat := 118140960795 + 6665549 * 2 ^ 59
def prefixEnd_6665549 : Nat := 4983230072969 + 3 ^ 40 * 6665549 * 2
def baseEnd_6665549 : Nat := 3422630463095846742583205

theorem tailTrace_6665549 : CollatzResearch.WordTrace tailWord_6665549 prefixEnd_6665549 3422630463095846742583205 := by
  unfold tailWord_6665549
  simp only [CollatzResearch.WordTrace]
  refine ⟨243112544528861832982839701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162075029685907888655226467 243112544528861832982839701)
  ·
    refine ⟨11395900524790398421070611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 243112544528861832982839701 11395900524790398421070611)
    ·
      refine ⟨17093850787185597631605917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11395900524790398421070611 17093850787185597631605917)
      ·
        refine ⟨6410194045194599111852219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17093850787185597631605917 6410194045194599111852219)
        ·
          refine ⟨9615291067791898667778329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410194045194599111852219 9615291067791898667778329)
          ·
            refine ⟨7211468300843924000833747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9615291067791898667778329 7211468300843924000833747)
            ·
              refine ⟨10817202451265886001250621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211468300843924000833747 10817202451265886001250621)
              ·
                refine ⟨4056450919224707250468983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10817202451265886001250621 4056450919224707250468983)
                ·
                  refine ⟨6084676378837060875703475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056450919224707250468983 6084676378837060875703475)
                  ·
                    refine ⟨9127014568255591313555213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6084676378837060875703475 9127014568255591313555213)
                    ·
                      refine ⟨3422630463095846742583205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127014568255591313555213 3422630463095846742583205)
                      ·
                        rfl

theorem cell23_6665549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6665549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665549 prefixEnd_6665549 := by exact prefixLift 6665549
  have htrace : WordTrace (prefixWord ++ tailWord_6665549) baseStart_6665549 baseEnd_6665549 := by
    simpa [prefixWord, tailWord_6665549, baseEnd_6665549] using wordTrace_append hprefix tailTrace_6665549
  have hstable : (prefixWord ++ tailWord_6665549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665549).length < 2 ^ (prefixWord ++ tailWord_6665549).sum := by decide
  have hdescent : baseEnd_6665549 < baseStart_6665549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665554 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_6665554 : Nat := 118140960795 + 6665554 * 2 ^ 59
def prefixEnd_6665554 : Nat := 4983230072969 + 3 ^ 40 * 6665554 * 2
def baseEnd_6665554 : Nat := 3422633030499119223020681

theorem tailTrace_6665554 : CollatzResearch.WordTrace tailWord_6665554 prefixEnd_6665554 3422633030499119223020681 := by
  unfold tailWord_6665554
  simp only [CollatzResearch.WordTrace]
  refine ⟨60778181723460929709192929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162075151262562479224514477 60778181723460929709192929)
  ·
    refine ⟨45583636292595697281894697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60778181723460929709192929 45583636292595697281894697)
    ·
      refine ⟨34187727219446772961421023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45583636292595697281894697 34187727219446772961421023)
      ·
        refine ⟨51281590829170159442131535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34187727219446772961421023 51281590829170159442131535)
        ·
          refine ⟨76922386243755239163197303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51281590829170159442131535 76922386243755239163197303)
          ·
            refine ⟨115383579365632858744795955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76922386243755239163197303 115383579365632858744795955)
            ·
              refine ⟨173075369048449288117193933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115383579365632858744795955 173075369048449288117193933)
              ·
                refine ⟨64903263393168483043947725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173075369048449288117193933 64903263393168483043947725)
                ·
                  refine ⟨24338723772438181141480397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64903263393168483043947725 24338723772438181141480397)
                  ·
                    refine ⟨9127021414664317928055149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24338723772438181141480397 9127021414664317928055149)
                    ·
                      refine ⟨3422633030499119223020681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127021414664317928055149 3422633030499119223020681)
                      ·
                        rfl

theorem cell23_6665554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_6665554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665554 prefixEnd_6665554 := by exact prefixLift 6665554
  have htrace : WordTrace (prefixWord ++ tailWord_6665554) baseStart_6665554 baseEnd_6665554 := by
    simpa [prefixWord, tailWord_6665554, baseEnd_6665554] using wordTrace_append hprefix tailTrace_6665554
  have hstable : (prefixWord ++ tailWord_6665554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665554).length < 2 ^ (prefixWord ++ tailWord_6665554).sum := by decide
  have hdescent : baseEnd_6665554 < baseStart_6665554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665567 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_6665567 : Nat := 118140960795 + 6665567 * 2 ^ 59
def prefixEnd_6665567 : Nat := 4983230072969 + 3 ^ 40 * 6665567 * 2
def baseEnd_6665567 : Nat := 3422639705747627672158121

theorem tailTrace_6665567 : CollatzResearch.WordTrace tailWord_6665567 prefixEnd_6665567 3422639705747627672158121 := by
  unfold tailWord_6665567
  simp only [CollatzResearch.WordTrace]
  refine ⟨243113201042796622056994955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162075467361864414704663303 243113201042796622056994955)
  ·
    refine ⟨364669801564194933085492433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243113201042796622056994955 364669801564194933085492433)
    ·
      refine ⟨273502351173146199814119325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364669801564194933085492433 273502351173146199814119325)
      ·
        refine ⟨102563381689929824930294747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273502351173146199814119325 102563381689929824930294747)
        ·
          refine ⟨153845072534894737395442121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102563381689929824930294747 153845072534894737395442121)
          ·
            refine ⟨115383804401171053046581591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153845072534894737395442121 115383804401171053046581591)
            ·
              refine ⟨173075706601756579569872387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115383804401171053046581591 173075706601756579569872387)
              ·
                refine ⟨259613559902634869354808581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173075706601756579569872387 259613559902634869354808581)
                ·
                  refine ⟨48677542481744038004026609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259613559902634869354808581 48677542481744038004026609)
                  ·
                    refine ⟨36508156861308028503019957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48677542481744038004026609 36508156861308028503019957)
                    ·
                      refine ⟨3422639705747627672158121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36508156861308028503019957 3422639705747627672158121)
                      ·
                        rfl

theorem cell23_6665567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_6665567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665567 prefixEnd_6665567 := by exact prefixLift 6665567
  have htrace : WordTrace (prefixWord ++ tailWord_6665567) baseStart_6665567 baseEnd_6665567 := by
    simpa [prefixWord, tailWord_6665567, baseEnd_6665567] using wordTrace_append hprefix tailTrace_6665567
  have hstable : (prefixWord ++ tailWord_6665567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665567).length < 2 ^ (prefixWord ++ tailWord_6665567).sum := by decide
  have hdescent : baseEnd_6665567 < baseStart_6665567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665571 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 3]
def baseStart_6665571 : Nat := 118140960795 + 6665571 * 2 ^ 59
def prefixEnd_6665571 : Nat := 4983230072969 + 3 ^ 40 * 6665571 * 2
def baseEnd_6665571 : Nat := 3422641759670245656508103

theorem tailTrace_6665571 : CollatzResearch.WordTrace tailWord_6665571 prefixEnd_6665571 3422641759670245656508103 := by
  unfold tailWord_6665571
  simp only [CollatzResearch.WordTrace]
  refine ⟨243113346934782130740140567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162075564623188087160093711 243113346934782130740140567)
  ·
    refine ⟨364670020402173196110210851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243113346934782130740140567 364670020402173196110210851)
    ·
      refine ⟨547005030603259794165316277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364670020402173196110210851 547005030603259794165316277)
      ·
        refine ⟨51281721619055605702998401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 547005030603259794165316277 51281721619055605702998401)
        ·
          refine ⟨38461291214291704277248801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51281721619055605702998401 38461291214291704277248801)
          ·
            refine ⟨28845968410718778207936601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38461291214291704277248801 28845968410718778207936601)
            ·
              refine ⟨21634476308039083655952451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28845968410718778207936601 21634476308039083655952451)
              ·
                refine ⟨32451714462058625483928677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21634476308039083655952451 32451714462058625483928677)
                ·
                  refine ⟨6084696461635992278236627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32451714462058625483928677 6084696461635992278236627)
                  ·
                    refine ⟨9127044692453988417354941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6084696461635992278236627 9127044692453988417354941)
                    ·
                      refine ⟨3422641759670245656508103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127044692453988417354941 3422641759670245656508103)
                      ·
                        rfl

theorem cell23_6665571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_6665571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665571 prefixEnd_6665571 := by exact prefixLift 6665571
  have htrace : WordTrace (prefixWord ++ tailWord_6665571) baseStart_6665571 baseEnd_6665571 := by
    simpa [prefixWord, tailWord_6665571, baseEnd_6665571] using wordTrace_append hprefix tailTrace_6665571
  have hstable : (prefixWord ++ tailWord_6665571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665571).length < 2 ^ (prefixWord ++ tailWord_6665571).sum := by decide
  have hdescent : baseEnd_6665571 < baseStart_6665571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665572 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_6665572 : Nat := 118140960795 + 6665572 * 2 ^ 59
def prefixEnd_6665572 : Nat := 4983230072969 + 3 ^ 40 * 6665572 * 2
def baseEnd_6665572 : Nat := 3422642273150900152595599

theorem tailTrace_6665572 : CollatzResearch.WordTrace tailWord_6665572 prefixEnd_6665572 3422642273150900152595599 := by
  unfold tailWord_6665572
  simp only [CollatzResearch.WordTrace]
  refine ⟨121556691703889253955463485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162075588938519005273951313 121556691703889253955463485)
  ·
    refine ⟨45583759388958470233298807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121556691703889253955463485 45583759388958470233298807)
    ·
      refine ⟨68375639083437705349948211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45583759388958470233298807 68375639083437705349948211)
      ·
        refine ⟨102563458625156558024922317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68375639083437705349948211 102563458625156558024922317)
        ·
          refine ⟨38461296984433709259345869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102563458625156558024922317 38461296984433709259345869)
          ·
            refine ⟨14422986369162640972254701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38461296984433709259345869 14422986369162640972254701)
            ·
              refine ⟨5408619888435990364595513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14422986369162640972254701 5408619888435990364595513)
              ·
                refine ⟨4056464916326992773446635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408619888435990364595513 4056464916326992773446635)
                ·
                  refine ⟨6084697374490489160169953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056464916326992773446635 6084697374490489160169953)
                  ·
                    refine ⟨4563523030867866870127465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6084697374490489160169953 4563523030867866870127465)
                    ·
                      refine ⟨3422642273150900152595599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563523030867866870127465 3422642273150900152595599)
                      ·
                        rfl

theorem cell23_6665572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_6665572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665572 prefixEnd_6665572 := by exact prefixLift 6665572
  have htrace : WordTrace (prefixWord ++ tailWord_6665572) baseStart_6665572 baseEnd_6665572 := by
    simpa [prefixWord, tailWord_6665572, baseEnd_6665572] using wordTrace_append hprefix tailTrace_6665572
  have hstable : (prefixWord ++ tailWord_6665572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665572).length < 2 ^ (prefixWord ++ tailWord_6665572).sum := by decide
  have hdescent : baseEnd_6665572 < baseStart_6665572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665582 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_6665582 : Nat := 118140960795 + 6665582 * 2 ^ 59
def prefixEnd_6665582 : Nat := 4983230072969 + 3 ^ 40 * 6665582 * 2
def baseEnd_6665582 : Nat := 1140882469319148371156851

theorem tailTrace_6665582 : CollatzResearch.WordTrace tailWord_6665582 prefixEnd_6665582 1140882469319148371156851 := by
  unfold tailWord_6665582
  simp only [CollatzResearch.WordTrace]
  refine ⟨30389218517217784952348875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162075832091828186412527333 30389218517217784952348875)
  ·
    refine ⟨45583827775826677428523313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30389218517217784952348875 45583827775826677428523313)
    ·
      refine ⟨34187870831870008071392485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45583827775826677428523313 34187870831870008071392485)
      ·
        refine ⟨6410225780975626513386091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34187870831870008071392485 6410225780975626513386091)
        ·
          refine ⟨9615338671463439770079137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410225780975626513386091 9615338671463439770079137)
          ·
            refine ⟨7211504003597579827559353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9615338671463439770079137 7211504003597579827559353)
            ·
              refine ⟨5408628002698184870669515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211504003597579827559353 5408628002698184870669515)
              ·
                refine ⟨8112942004047277306004273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408628002698184870669515 8112942004047277306004273)
                ·
                  refine ⟨6084706503035457979503205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8112942004047277306004273 6084706503035457979503205)
                  ·
                    refine ⟨1140882469319148371156851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084706503035457979503205 1140882469319148371156851)
                    ·
                      rfl

theorem cell23_6665582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_6665582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665582 prefixEnd_6665582 := by exact prefixLift 6665582
  have htrace : WordTrace (prefixWord ++ tailWord_6665582) baseStart_6665582 baseEnd_6665582 := by
    simpa [prefixWord, tailWord_6665582, baseEnd_6665582] using wordTrace_append hprefix tailTrace_6665582
  have hstable : (prefixWord ++ tailWord_6665582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665582).length < 2 ^ (prefixWord ++ tailWord_6665582).sum := by decide
  have hdescent : baseEnd_6665582 < baseStart_6665582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665611 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 1, 4, 2]
def baseStart_6665611 : Nat := 118140960795 + 6665611 * 2 ^ 59
def prefixEnd_6665611 : Nat := 4983230072969 + 3 ^ 40 * 6665611 * 2
def baseEnd_6665611 : Nat := 3422662298896425500007919

theorem tailTrace_6665611 : CollatzResearch.WordTrace tailWord_6665611 prefixEnd_6665611 3422662298896425500007919 := by
  unfold tailWord_6665611
  simp only [CollatzResearch.WordTrace]
  refine ⟨243114805854637217571596687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162076537236424811714397791 243114805854637217571596687)
  ·
    refine ⟨364672208781955826357395031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243114805854637217571596687 364672208781955826357395031)
    ·
      refine ⟨547008313172933739536092547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364672208781955826357395031 547008313172933739536092547)
      ·
        refine ⟨820512469759400609304138821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547008313172933739536092547 820512469759400609304138821)
        ·
          refine ⟨153846088079887614244526029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 820512469759400609304138821 153846088079887614244526029)
          ·
            refine ⟨57692283029957855341697261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153846088079887614244526029 57692283029957855341697261)
            ·
              refine ⟨21634606136234195753136473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57692283029957855341697261 21634606136234195753136473)
              ·
                refine ⟨16225954602175646814852355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21634606136234195753136473 16225954602175646814852355)
                ·
                  refine ⟨24338931903263470222278533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16225954602175646814852355 24338931903263470222278533)
                  ·
                    refine ⟨4563549731861900666677225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24338931903263470222278533 4563549731861900666677225)
                    ·
                      refine ⟨3422662298896425500007919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563549731861900666677225 3422662298896425500007919)
                      ·
                        rfl

theorem cell23_6665611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4, 2].length) (baseStart_6665611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665611 prefixEnd_6665611 := by exact prefixLift 6665611
  have htrace : WordTrace (prefixWord ++ tailWord_6665611) baseStart_6665611 baseEnd_6665611 := by
    simpa [prefixWord, tailWord_6665611, baseEnd_6665611] using wordTrace_append hprefix tailTrace_6665611
  have hstable : (prefixWord ++ tailWord_6665611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665611).length < 2 ^ (prefixWord ++ tailWord_6665611).sum := by decide
  have hdescent : baseEnd_6665611 < baseStart_6665611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665617 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 9]
def baseStart_6665617 : Nat := 118140960795 + 6665617 * 2 ^ 59
def prefixEnd_6665617 : Nat := 4983230072969 + 3 ^ 40 * 6665617 * 2
def baseEnd_6665617 : Nat := 380296153308928052948099

theorem tailTrace_6665617 : CollatzResearch.WordTrace tailWord_6665617 prefixEnd_6665617 380296153308928052948099 := by
  unfold tailWord_6665617
  simp only [CollatzResearch.WordTrace]
  refine ⟨243115024692615480596315105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162076683128410320397543403 243115024692615480596315105)
  ·
    refine ⟨182336268519461610447236329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243115024692615480596315105 182336268519461610447236329)
    ·
      refine ⟨136752201389596207835427247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182336268519461610447236329 136752201389596207835427247)
      ·
        refine ⟨205128302084394311753140871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136752201389596207835427247 205128302084394311753140871)
        ·
          refine ⟨307692453126591467629711307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205128302084394311753140871 307692453126591467629711307)
          ·
            refine ⟨461538679689887201444566961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307692453126591467629711307 461538679689887201444566961)
            ·
              refine ⟨346154009767415401083425221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461538679689887201444566961 346154009767415401083425221)
              ·
                refine ⟨64903876831390387703142229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346154009767415401083425221 64903876831390387703142229)
                ·
                  refine ⟨380296153308928052948099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64903876831390387703142229 380296153308928052948099)
                  ·
                    rfl

theorem cell23_6665617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 9].length) (baseStart_6665617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665617 prefixEnd_6665617 := by exact prefixLift 6665617
  have htrace : WordTrace (prefixWord ++ tailWord_6665617) baseStart_6665617 baseEnd_6665617 := by
    simpa [prefixWord, tailWord_6665617, baseEnd_6665617] using wordTrace_append hprefix tailTrace_6665617
  have hstable : (prefixWord ++ tailWord_6665617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665617).length < 2 ^ (prefixWord ++ tailWord_6665617).sum := by decide
  have hdescent : baseEnd_6665617 < baseStart_6665617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665644 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_6665644 : Nat := 118140960795 + 6665644 * 2 ^ 59
def prefixEnd_6665644 : Nat := 4983230072969 + 3 ^ 40 * 6665644 * 2
def baseEnd_6665644 : Nat := 3422679243758023870895267

theorem tailTrace_6665644 : CollatzResearch.WordTrace tailWord_6665644 prefixEnd_6665644 3422679243758023870895267 := by
  unfold tailWord_6665644
  simp only [CollatzResearch.WordTrace]
  refine ⟨121558004731758832103773993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162077339642345109471698657 121558004731758832103773993)
  ·
    refine ⟨91168503548819124077830495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121558004731758832103773993 91168503548819124077830495)
    ·
      refine ⟨136752755323228686116745743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91168503548819124077830495 136752755323228686116745743)
      ·
        refine ⟨205129132984843029175118615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136752755323228686116745743 205129132984843029175118615)
        ·
          refine ⟨307693699477264543762677923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205129132984843029175118615 307693699477264543762677923)
          ·
            refine ⟨461540549215896815644016885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307693699477264543762677923 461540549215896815644016885)
            ·
              refine ⟨43269426488990326466626583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 461540549215896815644016885 43269426488990326466626583)
              ·
                refine ⟨64904139733485489699939875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43269426488990326466626583 64904139733485489699939875)
                ·
                  refine ⟨97356209600228234549909813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64904139733485489699939875 97356209600228234549909813)
                  ·
                    refine ⟨9127144650021396989054045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97356209600228234549909813 9127144650021396989054045)
                    ·
                      refine ⟨3422679243758023870895267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127144650021396989054045 3422679243758023870895267)
                      ·
                        rfl

theorem cell23_6665644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_6665644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665644 prefixEnd_6665644 := by exact prefixLift 6665644
  have htrace : WordTrace (prefixWord ++ tailWord_6665644) baseStart_6665644 baseEnd_6665644 := by
    simpa [prefixWord, tailWord_6665644, baseEnd_6665644] using wordTrace_append hprefix tailTrace_6665644
  have hstable : (prefixWord ++ tailWord_6665644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665644).length < 2 ^ (prefixWord ++ tailWord_6665644).sum := by decide
  have hdescent : baseEnd_6665644 < baseStart_6665644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665645 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6665645 : Nat := 118140960795 + 6665645 * 2 ^ 59
def prefixEnd_6665645 : Nat := 4983230072969 + 3 ^ 40 * 6665645 * 2
def baseEnd_6665645 : Nat := 3422679757238678366982763

theorem tailTrace_6665645 : CollatzResearch.WordTrace tailWord_6665645 prefixEnd_6665645 3422679757238678366982763 := by
  unfold tailWord_6665645
  simp only [CollatzResearch.WordTrace]
  refine ⟨243116045936514041378334389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162077363957676027585556259 243116045936514041378334389)
  ·
    refine ⟨22792129306548191379218849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243116045936514041378334389 22792129306548191379218849)
    ·
      refine ⟨17094096979911143534414137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22792129306548191379218849 17094096979911143534414137)
      ·
        refine ⟨12820572734933357650810603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17094096979911143534414137 12820572734933357650810603)
        ·
          refine ⟨19230859102400036476215905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12820572734933357650810603 19230859102400036476215905)
          ·
            refine ⟨14423144326800027357161929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19230859102400036476215905 14423144326800027357161929)
            ·
              refine ⟨10817358245100020517871447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14423144326800027357161929 10817358245100020517871447)
              ·
                refine ⟨16226037367650030776807171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817358245100020517871447 16226037367650030776807171)
                ·
                  refine ⟨24339056051475046165210757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16226037367650030776807171 24339056051475046165210757)
                  ·
                    refine ⟨4563573009651571155977017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24339056051475046165210757 4563573009651571155977017)
                    ·
                      refine ⟨3422679757238678366982763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563573009651571155977017 3422679757238678366982763)
                      ·
                        rfl

theorem cell23_6665645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6665645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665645 prefixEnd_6665645 := by exact prefixLift 6665645
  have htrace : WordTrace (prefixWord ++ tailWord_6665645) baseStart_6665645 baseEnd_6665645 := by
    simpa [prefixWord, tailWord_6665645, baseEnd_6665645] using wordTrace_append hprefix tailTrace_6665645
  have hstable : (prefixWord ++ tailWord_6665645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665645).length < 2 ^ (prefixWord ++ tailWord_6665645).sum := by decide
  have hdescent : baseEnd_6665645 < baseStart_6665645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665666 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6665666 : Nat := 118140960795 + 6665666 * 2 ^ 59
def prefixEnd_6665666 : Nat := 4983230072969 + 3 ^ 40 * 6665666 * 2
def baseEnd_6665666 : Nat := 3422690540332422784820167

theorem tailTrace_6665666 : CollatzResearch.WordTrace tailWord_6665666 prefixEnd_6665666 3422690540332422784820167 := by
  unfold tailWord_6665666
  simp only [CollatzResearch.WordTrace]
  refine ⟨60779202967359490491212213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162077874579625307976565901 60779202967359490491212213)
  ·
    refine ⟨5698050278189952233551145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60779202967359490491212213 5698050278189952233551145)
    ·
      refine ⟨4273537708642464175163359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5698050278189952233551145 4273537708642464175163359)
      ·
        refine ⟨6410306562963696262745039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4273537708642464175163359 6410306562963696262745039)
        ·
          refine ⟨9615459844445544394117559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410306562963696262745039 9615459844445544394117559)
          ·
            refine ⟨14423189766668316591176339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9615459844445544394117559 14423189766668316591176339)
            ·
              refine ⟨21634784650002474886764509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423189766668316591176339 21634784650002474886764509)
              ·
                refine ⟨8113044243750928082536691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21634784650002474886764509 8113044243750928082536691)
                ·
                  refine ⟨12169566365626392123805037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8113044243750928082536691 12169566365626392123805037)
                  ·
                    refine ⟨4563587387109897046426889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12169566365626392123805037 4563587387109897046426889)
                    ·
                      refine ⟨3422690540332422784820167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563587387109897046426889 3422690540332422784820167)
                      ·
                        rfl

theorem cell23_6665666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6665666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665666 prefixEnd_6665666 := by exact prefixLift 6665666
  have htrace : WordTrace (prefixWord ++ tailWord_6665666) baseStart_6665666 baseEnd_6665666 := by
    simpa [prefixWord, tailWord_6665666, baseEnd_6665666] using wordTrace_append hprefix tailTrace_6665666
  have hstable : (prefixWord ++ tailWord_6665666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665666).length < 2 ^ (prefixWord ++ tailWord_6665666).sum := by decide
  have hdescent : baseEnd_6665666 < baseStart_6665666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665668 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 5]
def baseStart_6665668 : Nat := 118140960795 + 6665668 * 2 ^ 59
def prefixEnd_6665668 : Nat := 4983230072969 + 3 ^ 40 * 6665668 * 2
def baseEnd_6665668 : Nat := 380299063032636864110573

theorem tailTrace_6665668 : CollatzResearch.WordTrace tailWord_6665668 prefixEnd_6665668 380299063032636864110573 := by
  unfold tailWord_6665668
  simp only [CollatzResearch.WordTrace]
  refine ⟨121558442407715358153210829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162077923210287144204281105 121558442407715358153210829)
  ·
    refine ⟨45584415902893259307454061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121558442407715358153210829 45584415902893259307454061)
    ·
      refine ⟨17094155963584972240295273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45584415902893259307454061 17094155963584972240295273)
      ·
        refine ⟨12820616972688729180221455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17094155963584972240295273 12820616972688729180221455)
        ·
          refine ⟨19230925459033093770332183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12820616972688729180221455 19230925459033093770332183)
          ·
            refine ⟨28846388188549640655498275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19230925459033093770332183 28846388188549640655498275)
            ·
              refine ⟨43269582282824460983247413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28846388188549640655498275 43269582282824460983247413)
              ·
                refine ⟨4056523339014793217179445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43269582282824460983247413 4056523339014793217179445)
                ·
                  refine ⟨380299063032636864110573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056523339014793217179445 380299063032636864110573)
                  ·
                    rfl

theorem cell23_6665668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_6665668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665668 prefixEnd_6665668 := by exact prefixLift 6665668
  have htrace : WordTrace (prefixWord ++ tailWord_6665668) baseStart_6665668 baseEnd_6665668 := by
    simpa [prefixWord, tailWord_6665668, baseEnd_6665668] using wordTrace_append hprefix tailTrace_6665668
  have hstable : (prefixWord ++ tailWord_6665668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665668).length < 2 ^ (prefixWord ++ tailWord_6665668).sum := by decide
  have hdescent : baseEnd_6665668 < baseStart_6665668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665701 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6665701 : Nat := 118140960795 + 6665701 * 2 ^ 59
def prefixEnd_6665701 : Nat := 4983230072969 + 3 ^ 40 * 6665701 * 2
def baseEnd_6665701 : Nat := 3422708512155330147882505

theorem tailTrace_6665701 : CollatzResearch.WordTrace tailWord_6665701 prefixEnd_6665701 3422708512155330147882505 := by
  unfold tailWord_6665701
  simp only [CollatzResearch.WordTrace]
  refine ⟨243118088424311162942372957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162078725616207441961581971 243118088424311162942372957)
  ·
    refine ⟨91169283159116686103389859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243118088424311162942372957 91169283159116686103389859)
    ·
      refine ⟨136753924738675029155084789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91169283159116686103389859 136753924738675029155084789)
      ·
        refine ⟨12820680444250783983289199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136753924738675029155084789 12820680444250783983289199)
        ·
          refine ⟨19231020666376175974933799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12820680444250783983289199 19231020666376175974933799)
          ·
            refine ⟨28846530999564263962400699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19231020666376175974933799 28846530999564263962400699)
            ·
              refine ⟨43269796499346395943601049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28846530999564263962400699 43269796499346395943601049)
              ·
                refine ⟨32452347374509796957700787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43269796499346395943601049 32452347374509796957700787)
                ·
                  refine ⟨48678521061764695436551181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32452347374509796957700787 48678521061764695436551181)
                  ·
                    refine ⟨18254445398161760788706693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48678521061764695436551181 18254445398161760788706693)
                    ·
                      refine ⟨3422708512155330147882505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18254445398161760788706693 3422708512155330147882505)
                      ·
                        rfl

theorem cell23_6665701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6665701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665701 prefixEnd_6665701 := by exact prefixLift 6665701
  have htrace : WordTrace (prefixWord ++ tailWord_6665701) baseStart_6665701 baseEnd_6665701 := by
    simpa [prefixWord, tailWord_6665701, baseEnd_6665701] using wordTrace_append hprefix tailTrace_6665701
  have hstable : (prefixWord ++ tailWord_6665701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665701).length < 2 ^ (prefixWord ++ tailWord_6665701).sum := by decide
  have hdescent : baseEnd_6665701 < baseStart_6665701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665711 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 3, 4]
def baseStart_6665711 : Nat := 118140960795 + 6665711 * 2 ^ 59
def prefixEnd_6665711 : Nat := 4983230072969 + 3 ^ 40 * 6665711 * 2
def baseEnd_6665711 : Nat := 1140904548987291702919153

theorem tailTrace_6665711 : CollatzResearch.WordTrace tailWord_6665711 prefixEnd_6665711 1140904548987291702919153 := by
  unfold tailWord_6665711
  simp only [CollatzResearch.WordTrace]
  refine ⟨243118453154274934650236987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162078968769516623100157991 243118453154274934650236987)
  ·
    refine ⟨364677679731412401975355481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243118453154274934650236987 364677679731412401975355481)
    ·
      refine ⟨273508259798559301481516611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364677679731412401975355481 273508259798559301481516611)
      ·
        refine ⟨410262389697838952222274917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273508259798559301481516611 410262389697838952222274917)
        ·
          refine ⟨76924198068344803541676547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410262389697838952222274917 76924198068344803541676547)
          ·
            refine ⟨115386297102517205312514821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76924198068344803541676547 115386297102517205312514821)
            ·
              refine ⟨21634930706721975996096529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115386297102517205312514821 21634930706721975996096529)
              ·
                refine ⟨16226198030041481997072397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21634930706721975996096529 16226198030041481997072397)
                ·
                  refine ⟨6084824261265555748902149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16226198030041481997072397 6084824261265555748902149)
                  ·
                    refine ⟨1140904548987291702919153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084824261265555748902149 1140904548987291702919153)
                    ·
                      rfl

theorem cell23_6665711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_6665711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665711 prefixEnd_6665711 := by exact prefixLift 6665711
  have htrace : WordTrace (prefixWord ++ tailWord_6665711) baseStart_6665711 baseEnd_6665711 := by
    simpa [prefixWord, tailWord_6665711, baseEnd_6665711] using wordTrace_append hprefix tailTrace_6665711
  have hstable : (prefixWord ++ tailWord_6665711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665711).length < 2 ^ (prefixWord ++ tailWord_6665711).sum := by decide
  have hdescent : baseEnd_6665711 < baseStart_6665711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665721 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_6665721 : Nat := 118140960795 + 6665721 * 2 ^ 59
def prefixEnd_6665721 : Nat := 4983230072969 + 3 ^ 40 * 6665721 * 2
def baseEnd_6665721 : Nat := 3422718781768420069632413

theorem tailTrace_6665721 : CollatzResearch.WordTrace tailWord_6665721 prefixEnd_6665721 3422718781768420069632413 := by
  unfold tailWord_6665721
  simp only [CollatzResearch.WordTrace]
  refine ⟨243118817884238706358101017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162079211922825804238734011 243118817884238706358101017)
  ·
    refine ⟨182339113413179029768575763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243118817884238706358101017 182339113413179029768575763)
    ·
      refine ⟨273508670119768544652863645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182339113413179029768575763 273508670119768544652863645)
      ·
        refine ⟨102565751294913204244823867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273508670119768544652863645 102565751294913204244823867)
        ·
          refine ⟨153848626942369806367235801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102565751294913204244823867 153848626942369806367235801)
          ·
            refine ⟨115386470206777354775426851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153848626942369806367235801 115386470206777354775426851)
            ·
              refine ⟨173079705310166032163140277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115386470206777354775426851 173079705310166032163140277)
              ·
                refine ⟨16226222372828065515294401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173079705310166032163140277 16226222372828065515294401)
                ·
                  refine ⟨12169666779621049136470801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16226222372828065515294401 12169666779621049136470801)
                  ·
                    refine ⟨9127250084715786852353101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12169666779621049136470801 9127250084715786852353101)
                    ·
                      refine ⟨3422718781768420069632413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127250084715786852353101 3422718781768420069632413)
                      ·
                        rfl

theorem cell23_6665721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_6665721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665721 prefixEnd_6665721 := by exact prefixLift 6665721
  have htrace : WordTrace (prefixWord ++ tailWord_6665721) baseStart_6665721 baseEnd_6665721 := by
    simpa [prefixWord, tailWord_6665721, baseEnd_6665721] using wordTrace_append hprefix tailTrace_6665721
  have hstable : (prefixWord ++ tailWord_6665721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665721).length < 2 ^ (prefixWord ++ tailWord_6665721).sum := by decide
  have hdescent : baseEnd_6665721 < baseStart_6665721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665724 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 8]
def baseStart_6665724 : Nat := 118140960795 + 6665724 * 2 ^ 59
def prefixEnd_6665724 : Nat := 4983230072969 + 3 ^ 40 * 6665724 * 2
def baseEnd_6665724 : Nat := 380302258023375950877211

theorem tailTrace_6665724 : CollatzResearch.WordTrace tailWord_6665724 prefixEnd_6665724 380302258023375950877211 := by
  unfold tailWord_6665724
  simp only [CollatzResearch.WordTrace]
  refine ⟨121559463651613918935230113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162079284868818558580306817 121559463651613918935230113)
  ·
    refine ⟨91169597738710439201422585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121559463651613918935230113 91169597738710439201422585)
    ·
      refine ⟨68377198304032829401066939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91169597738710439201422585 68377198304032829401066939)
      ·
        refine ⟨102565797456049244101600409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68377198304032829401066939 102565797456049244101600409)
        ·
          refine ⟨76924348092036933076200307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102565797456049244101600409 76924348092036933076200307)
          ·
            refine ⟨115386522138055399614300461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76924348092036933076200307 115386522138055399614300461)
            ·
              refine ⟨43269945801770774855362673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115386522138055399614300461 43269945801770774855362673)
              ·
                refine ⟨32452459351328081141522005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43269945801770774855362673 32452459351328081141522005)
                ·
                  refine ⟨380302258023375950877211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32452459351328081141522005 380302258023375950877211)
                  ·
                    rfl

theorem cell23_6665724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_6665724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665724 prefixEnd_6665724 := by exact prefixLift 6665724
  have htrace : WordTrace (prefixWord ++ tailWord_6665724) baseStart_6665724 baseEnd_6665724 := by
    simpa [prefixWord, tailWord_6665724, baseEnd_6665724] using wordTrace_append hprefix tailTrace_6665724
  have hstable : (prefixWord ++ tailWord_6665724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665724).length < 2 ^ (prefixWord ++ tailWord_6665724).sum := by decide
  have hdescent : baseEnd_6665724 < baseStart_6665724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665738 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_6665738 : Nat := 118140960795 + 6665738 * 2 ^ 59
def prefixEnd_6665738 : Nat := 4983230072969 + 3 ^ 40 * 6665738 * 2
def baseEnd_6665738 : Nat := 3422727510939546503119835

theorem tailTrace_6665738 : CollatzResearch.WordTrace tailWord_6665738 prefixEnd_6665738 3422727510939546503119835 := by
  unfold tailWord_6665738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60779859481294279565367467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162079625283451412174313245 60779859481294279565367467)
  ·
    refine ⟨91169789221941419348051201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60779859481294279565367467 91169789221941419348051201)
    ·
      refine ⟨68377341916456064511038401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91169789221941419348051201 68377341916456064511038401)
      ·
        refine ⟨51283006437342048383278801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68377341916456064511038401 51283006437342048383278801)
        ·
          refine ⟨38462254828006536287459101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51283006437342048383278801 38462254828006536287459101)
          ·
            refine ⟨14423345560502451107797163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38462254828006536287459101 14423345560502451107797163)
            ·
              refine ⟨21635018340753676661695745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423345560502451107797163 21635018340753676661695745)
              ·
                refine ⟨16226263755565257496271809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21635018340753676661695745 16226263755565257496271809)
                ·
                  refine ⟨12169697816673943122203857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16226263755565257496271809 12169697816673943122203857)
                  ·
                    refine ⟨9127273362505457341652893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12169697816673943122203857 9127273362505457341652893)
                    ·
                      refine ⟨3422727510939546503119835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127273362505457341652893 3422727510939546503119835)
                      ·
                        rfl

theorem cell23_6665738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_6665738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665738 prefixEnd_6665738 := by exact prefixLift 6665738
  have htrace : WordTrace (prefixWord ++ tailWord_6665738) baseStart_6665738 baseEnd_6665738 := by
    simpa [prefixWord, tailWord_6665738, baseEnd_6665738] using wordTrace_append hprefix tailTrace_6665738
  have hstable : (prefixWord ++ tailWord_6665738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665738).length < 2 ^ (prefixWord ++ tailWord_6665738).sum := by decide
  have hdescent : baseEnd_6665738 < baseStart_6665738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665745 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 1, 4]
def baseStart_6665745 : Nat := 118140960795 + 6665745 * 2 ^ 59
def prefixEnd_6665745 : Nat := 4983230072969 + 3 ^ 40 * 6665745 * 2
def baseEnd_6665745 : Nat := 1140910368434709325244101

theorem tailTrace_6665745 : CollatzResearch.WordTrace tailWord_6665745 prefixEnd_6665745 1140910368434709325244101 := by
  unfold tailWord_6665745
  simp only [CollatzResearch.WordTrace]
  refine ⟨243119693236151758456974689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162079795490767838971316459 243119693236151758456974689)
  ·
    refine ⟨182339769927113818842731017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243119693236151758456974689 182339769927113818842731017)
    ·
      refine ⟨136754827445335364132048263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182339769927113818842731017 136754827445335364132048263)
      ·
        refine ⟨205132241168003046198072395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136754827445335364132048263 205132241168003046198072395)
        ·
          refine ⟨307698361752004569297108593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205132241168003046198072395 307698361752004569297108593)
          ·
            refine ⟨230773771314003426972831445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307698361752004569297108593 230773771314003426972831445)
            ·
              refine ⟨5408760265171955319675737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230773771314003426972831445 5408760265171955319675737)
              ·
                refine ⟨4056570198878966489756803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408760265171955319675737 4056570198878966489756803)
                ·
                  refine ⟨6084855298318449734635205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056570198878966489756803 6084855298318449734635205)
                  ·
                    refine ⟨1140910368434709325244101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084855298318449734635205 1140910368434709325244101)
                    ·
                      rfl

theorem cell23_6665745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_6665745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665745 prefixEnd_6665745 := by exact prefixLift 6665745
  have htrace : WordTrace (prefixWord ++ tailWord_6665745) baseStart_6665745 baseEnd_6665745 := by
    simpa [prefixWord, tailWord_6665745, baseEnd_6665745] using wordTrace_append hprefix tailTrace_6665745
  have hstable : (prefixWord ++ tailWord_6665745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665745).length < 2 ^ (prefixWord ++ tailWord_6665745).sum := by decide
  have hdescent : baseEnd_6665745 < baseStart_6665745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665754 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_6665754 : Nat := 118140960795 + 6665754 * 2 ^ 59
def prefixEnd_6665754 : Nat := 4983230072969 + 3 ^ 40 * 6665754 * 2
def baseEnd_6665754 : Nat := 1140911908876672813506587

theorem tailTrace_6665754 : CollatzResearch.WordTrace tailWord_6665754 prefixEnd_6665754 1140911908876672813506587 := by
  unfold tailWord_6665754
  simp only [CollatzResearch.WordTrace]
  refine ⟨60780005373279788248513079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162080014328746101996034877 60780005373279788248513079)
  ·
    refine ⟨91170008059919682372769619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60780005373279788248513079 91170008059919682372769619)
    ·
      refine ⟨136755012089879523559154429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91170008059919682372769619 136755012089879523559154429)
      ·
        refine ⟨51283129533704821334682911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136755012089879523559154429 51283129533704821334682911)
        ·
          refine ⟨76924694300557232002024367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51283129533704821334682911 76924694300557232002024367)
          ·
            refine ⟨115387041450835848003036551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76924694300557232002024367 115387041450835848003036551)
            ·
              refine ⟨173080562176253772004554827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115387041450835848003036551 173080562176253772004554827)
              ·
                refine ⟨259620843264380658006832241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173080562176253772004554827 259620843264380658006832241)
                ·
                  refine ⟨194715632448285493505124181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259620843264380658006832241 194715632448285493505124181)
                  ·
                    refine ⟨1140911908876672813506587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194715632448285493505124181 1140911908876672813506587)
                    ·
                      rfl

theorem cell23_6665754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_6665754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665754 prefixEnd_6665754 := by exact prefixLift 6665754
  have htrace : WordTrace (prefixWord ++ tailWord_6665754) baseStart_6665754 baseEnd_6665754 := by
    simpa [prefixWord, tailWord_6665754, baseEnd_6665754] using wordTrace_append hprefix tailTrace_6665754
  have hstable : (prefixWord ++ tailWord_6665754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665754).length < 2 ^ (prefixWord ++ tailWord_6665754).sum := by decide
  have hdescent : baseEnd_6665754 < baseStart_6665754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665801 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 4, 4]
def baseStart_6665801 : Nat := 118140960795 + 6665801 * 2 ^ 59
def prefixEnd_6665801 : Nat := 4983230072969 + 3 ^ 40 * 6665801 * 2
def baseEnd_6665801 : Nat := 1140919953406926585544015

theorem tailTrace_6665801 : CollatzResearch.WordTrace tailWord_6665801 prefixEnd_6665801 1140919953406926585544015 := by
  unfold tailWord_6665801
  simp only [CollatzResearch.WordTrace]
  refine ⟨243121735723948880021013257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162081157149299253347342171 243121735723948880021013257)
  ·
    refine ⟨182341301792961660015759943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243121735723948880021013257 182341301792961660015759943)
    ·
      refine ⟨273511952689442490023639915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182341301792961660015759943 273511952689442490023639915)
      ·
        refine ⟨410267929034163735035459873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273511952689442490023639915 410267929034163735035459873)
        ·
          refine ⟨307700946775622801276594905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410267929034163735035459873 307700946775622801276594905)
          ·
            refine ⟨230775710081717100957446179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307700946775622801276594905 230775710081717100957446179)
            ·
              refine ⟨346163565122575651436169269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230775710081717100957446179 346163565122575651436169269)
              ·
                refine ⟨32452834230241467322140869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346163565122575651436169269 32452834230241467322140869)
                ·
                  refine ⟨6084906418170275122901413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32452834230241467322140869 6084906418170275122901413)
                  ·
                    refine ⟨1140919953406926585544015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6084906418170275122901413 1140919953406926585544015)
                    ·
                      rfl

theorem cell23_6665801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_6665801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665801 prefixEnd_6665801 := by exact prefixLift 6665801
  have htrace : WordTrace (prefixWord ++ tailWord_6665801) baseStart_6665801 baseEnd_6665801 := by
    simpa [prefixWord, tailWord_6665801, baseEnd_6665801] using wordTrace_append hprefix tailTrace_6665801
  have hstable : (prefixWord ++ tailWord_6665801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665801).length < 2 ^ (prefixWord ++ tailWord_6665801).sum := by decide
  have hdescent : baseEnd_6665801 < baseStart_6665801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665825 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_6665825 : Nat := 118140960795 + 6665825 * 2 ^ 59
def prefixEnd_6665825 : Nat := 4983230072969 + 3 ^ 40 * 6665825 * 2
def baseEnd_6665825 : Nat := 3422772183756487662731935

theorem tailTrace_6665825 : CollatzResearch.WordTrace tailWord_6665825 prefixEnd_6665825 3422772183756487662731935 := by
  unfold tailWord_6665825
  simp only [CollatzResearch.WordTrace]
  refine ⟨243122611075861932119886929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162081740717241288079924619 243122611075861932119886929)
  ·
    refine ⟨182341958306896449089915197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243122611075861932119886929 182341958306896449089915197)
    ·
      refine ⟨68378234365086168408718199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182341958306896449089915197 68378234365086168408718199)
      ·
        refine ⟨102567351547629252613077299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68378234365086168408718199 102567351547629252613077299)
        ·
          refine ⟨153851027321443878919615949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102567351547629252613077299 153851027321443878919615949)
          ·
            refine ⟨57694135245541454594855981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153851027321443878919615949 57694135245541454594855981)
            ·
              refine ⟨21635300717078045473070993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57694135245541454594855981 21635300717078045473070993)
              ·
                refine ⟨16226475537808534104803245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21635300717078045473070993 16226475537808534104803245)
                ·
                  refine ⟨6084928326678200289301217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16226475537808534104803245 6084928326678200289301217)
                  ·
                    refine ⟨4563696245008650216975913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6084928326678200289301217 4563696245008650216975913)
                    ·
                      refine ⟨3422772183756487662731935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563696245008650216975913 3422772183756487662731935)
                      ·
                        rfl

theorem cell23_6665825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_6665825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665825 prefixEnd_6665825 := by exact prefixLift 6665825
  have htrace : WordTrace (prefixWord ++ tailWord_6665825) baseStart_6665825 baseEnd_6665825 := by
    simpa [prefixWord, tailWord_6665825, baseEnd_6665825] using wordTrace_append hprefix tailTrace_6665825
  have hstable : (prefixWord ++ tailWord_6665825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665825).length < 2 ^ (prefixWord ++ tailWord_6665825).sum := by decide
  have hdescent : baseEnd_6665825 < baseStart_6665825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665828 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_6665828 : Nat := 118140960795 + 6665828 * 2 ^ 59
def prefixEnd_6665828 : Nat := 4983230072969 + 3 ^ 40 * 6665828 * 2
def baseEnd_6665828 : Nat := 3422773724198451150994421

theorem tailTrace_6665828 : CollatzResearch.WordTrace tailWord_6665828 prefixEnd_6665828 3422773724198451150994421 := by
  unfold tailWord_6665828
  simp only [CollatzResearch.WordTrace]
  refine ⟨121561360247425531816123069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162081813663234042421497425 121561360247425531816123069)
  ·
    refine ⟨45585510092784574431046151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121561360247425531816123069 45585510092784574431046151)
    ·
      refine ⟨68378265139176861646569227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45585510092784574431046151 68378265139176861646569227)
      ·
        refine ⟨102567397708765292469853841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68378265139176861646569227 102567397708765292469853841)
        ·
          refine ⟨76925548281573969352390381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102567397708765292469853841 76925548281573969352390381)
          ·
            refine ⟨28847080605590238507146393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76925548281573969352390381 28847080605590238507146393)
            ·
              refine ⟨21635310454192678880359795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28847080605590238507146393 21635310454192678880359795)
              ·
                refine ⟨32452965681289018320539693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21635310454192678880359795 32452965681289018320539693)
                ·
                  refine ⟨12169862130483381870202385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32452965681289018320539693 12169862130483381870202385)
                  ·
                    refine ⟨9127396597862536402651789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12169862130483381870202385 9127396597862536402651789)
                    ·
                      refine ⟨3422773724198451150994421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127396597862536402651789 3422773724198451150994421)
                      ·
                        rfl

theorem cell23_6665828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_6665828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665828 prefixEnd_6665828 := by exact prefixLift 6665828
  have htrace : WordTrace (prefixWord ++ tailWord_6665828) baseStart_6665828 baseEnd_6665828 := by
    simpa [prefixWord, tailWord_6665828, baseEnd_6665828] using wordTrace_append hprefix tailTrace_6665828
  have hstable : (prefixWord ++ tailWord_6665828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665828).length < 2 ^ (prefixWord ++ tailWord_6665828).sum := by decide
  have hdescent : baseEnd_6665828 < baseStart_6665828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665842 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_6665842 : Nat := 118140960795 + 6665842 * 2 ^ 59
def prefixEnd_6665842 : Nat := 4983230072969 + 3 ^ 40 * 6665842 * 2
def baseEnd_6665842 : Nat := 3422780912927614096219357

theorem tailTrace_6665842 : CollatzResearch.WordTrace tailWord_6665842 prefixEnd_6665842 3422780912927614096219357 := by
  unfold tailWord_6665842
  simp only [CollatzResearch.WordTrace]
  refine ⟨60780807779200086005813945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162082154077866896015503853 60780807779200086005813945)
  ·
    refine ⟨45585605834400064504360459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60780807779200086005813945 45585605834400064504360459)
    ·
      refine ⟨68378408751600096756540689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45585605834400064504360459 68378408751600096756540689)
      ·
        refine ⟨51283806563700072567405517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68378408751600096756540689 51283806563700072567405517)
        ·
          refine ⟨19231427461387527212777069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51283806563700072567405517 19231427461387527212777069)
          ·
            refine ⟨7211785298020322704791401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19231427461387527212777069 7211785298020322704791401)
            ·
              refine ⟨5408838973515242028593551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211785298020322704791401 5408838973515242028593551)
              ·
                refine ⟨8113258460272863042890327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408838973515242028593551 8113258460272863042890327)
                ·
                  refine ⟨12169887690409294564335491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8113258460272863042890327 12169887690409294564335491)
                  ·
                    refine ⟨18254831535613941846503237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12169887690409294564335491 18254831535613941846503237)
                    ·
                      refine ⟨3422780912927614096219357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18254831535613941846503237 3422780912927614096219357)
                      ·
                        rfl

theorem cell23_6665842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_6665842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665842 prefixEnd_6665842 := by exact prefixLift 6665842
  have htrace : WordTrace (prefixWord ++ tailWord_6665842) baseStart_6665842 baseEnd_6665842 := by
    simpa [prefixWord, tailWord_6665842, baseEnd_6665842] using wordTrace_append hprefix tailTrace_6665842
  have hstable : (prefixWord ++ tailWord_6665842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665842).length < 2 ^ (prefixWord ++ tailWord_6665842).sum := by decide
  have hdescent : baseEnd_6665842 < baseStart_6665842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665926 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6665926 : Nat := 118140960795 + 6665926 * 2 ^ 59
def prefixEnd_6665926 : Nat := 4983230072969 + 3 ^ 40 * 6665926 * 2
def baseEnd_6665926 : Nat := 3422824045302591767568971

theorem tailTrace_6665926 : CollatzResearch.WordTrace tailWord_6665926 prefixEnd_6665926 3422824045302591767568971 := by
  unfold tailWord_6665926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597696714015500824041051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162084196565664017579542421 7597696714015500824041051)
  ·
    refine ⟨11396545071023251236061577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7597696714015500824041051 11396545071023251236061577)
    ·
      refine ⟨8547408803267438427046183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11396545071023251236061577 8547408803267438427046183)
      ·
        refine ⟨12821113204901157640569275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547408803267438427046183 12821113204901157640569275)
        ·
          refine ⟨19231669807351736460853913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821113204901157640569275 19231669807351736460853913)
          ·
            refine ⟨14423752355513802345640435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19231669807351736460853913 14423752355513802345640435)
            ·
              refine ⟨21635628533270703518460653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423752355513802345640435 21635628533270703518460653)
              ·
                refine ⟨8113360699976513819422745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21635628533270703518460653 8113360699976513819422745)
                ·
                  refine ⟨6085020524982385364567059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8113360699976513819422745 6085020524982385364567059)
                  ·
                    refine ⟨9127530787473578046850589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6085020524982385364567059 9127530787473578046850589)
                    ·
                      refine ⟨3422824045302591767568971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127530787473578046850589 3422824045302591767568971)
                      ·
                        rfl

theorem cell23_6665926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6665926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665926 prefixEnd_6665926 := by exact prefixLift 6665926
  have htrace : WordTrace (prefixWord ++ tailWord_6665926) baseStart_6665926 baseEnd_6665926 := by
    simpa [prefixWord, tailWord_6665926, baseEnd_6665926] using wordTrace_append hprefix tailTrace_6665926
  have hstable : (prefixWord ++ tailWord_6665926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665926).length < 2 ^ (prefixWord ++ tailWord_6665926).sum := by decide
  have hdescent : baseEnd_6665926 < baseStart_6665926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665949 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6665949 : Nat := 118140960795 + 6665949 * 2 ^ 59
def prefixEnd_6665949 : Nat := 4983230072969 + 3 ^ 40 * 6665949 * 2
def baseEnd_6665949 : Nat := 3422835855357645177581365

theorem tailTrace_6665949 : CollatzResearch.WordTrace tailWord_6665949 prefixEnd_6665949 3422835855357645177581365 := by
  unfold tailWord_6665949
  simp only [CollatzResearch.WordTrace]
  refine ⟨243127133727412701297400901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162084755818275134198267267 243127133727412701297400901)
  ·
    refine ⟨45586337573889881493262669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243127133727412701297400901 45586337573889881493262669)
    ·
      refine ⟨17094876590208705559973501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45586337573889881493262669 17094876590208705559973501)
      ·
        refine ⟨6410578721328264584990063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17094876590208705559973501 6410578721328264584990063)
        ·
          refine ⟨9615868081992396877485095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410578721328264584990063 9615868081992396877485095)
          ·
            refine ⟨14423802122988595316227643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9615868081992396877485095 14423802122988595316227643)
            ·
              refine ⟨21635703184482892974341465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423802122988595316227643 21635703184482892974341465)
              ·
                refine ⟨16226777388362169730756099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21635703184482892974341465 16226777388362169730756099)
                ·
                  refine ⟨24340166082543254596134149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16226777388362169730756099 24340166082543254596134149)
                  ·
                    refine ⟨4563781140476860236775153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24340166082543254596134149 4563781140476860236775153)
                    ·
                      refine ⟨3422835855357645177581365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563781140476860236775153 3422835855357645177581365)
                      ·
                        rfl

theorem cell23_6665949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6665949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665949 prefixEnd_6665949 := by exact prefixLift 6665949
  have htrace : WordTrace (prefixWord ++ tailWord_6665949) baseStart_6665949 baseEnd_6665949 := by
    simpa [prefixWord, tailWord_6665949, baseEnd_6665949] using wordTrace_append hprefix tailTrace_6665949
  have hstable : (prefixWord ++ tailWord_6665949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665949).length < 2 ^ (prefixWord ++ tailWord_6665949).sum := by decide
  have hdescent : baseEnd_6665949 < baseStart_6665949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6665982 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6665982 : Nat := 118140960795 + 6665982 * 2 ^ 59
def prefixEnd_6665982 : Nat := 4983230072969 + 3 ^ 40 * 6665982 * 2
def baseEnd_6665982 : Nat := 3422852800219243548468713

theorem tailTrace_6665982 : CollatzResearch.WordTrace tailWord_6665982 prefixEnd_6665982 3422852800219243548468713 := by
  unfold tailWord_6665982
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391042167036643491669025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162085558224195431955568133 30391042167036643491669025)
  ·
    refine ⟨22793281625277482618751769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30391042167036643491669025 22793281625277482618751769)
    ·
      refine ⟨17094961218958111964063827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22793281625277482618751769 17094961218958111964063827)
      ·
        refine ⟨25642441828437167946095741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17094961218958111964063827 25642441828437167946095741)
        ·
          refine ⟨9615915685663937979785903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25642441828437167946095741 9615915685663937979785903)
          ·
            refine ⟨14423873528495906969678855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9615915685663937979785903 14423873528495906969678855)
            ·
              refine ⟨21635810292743860454518283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423873528495906969678855 21635810292743860454518283)
              ·
                refine ⟨32453715439115790681777425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21635810292743860454518283 32453715439115790681777425)
                ·
                  refine ⟨24340286579336843011333069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32453715439115790681777425 24340286579336843011333069)
                  ·
                    refine ⟨9127607467251316129249901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24340286579336843011333069 9127607467251316129249901)
                    ·
                      refine ⟨3422852800219243548468713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127607467251316129249901 3422852800219243548468713)
                      ·
                        rfl

theorem cell23_6665982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6665982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6665982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6665982 prefixEnd_6665982 := by exact prefixLift 6665982
  have htrace : WordTrace (prefixWord ++ tailWord_6665982) baseStart_6665982 baseEnd_6665982 := by
    simpa [prefixWord, tailWord_6665982, baseEnd_6665982] using wordTrace_append hprefix tailTrace_6665982
  have hstable : (prefixWord ++ tailWord_6665982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6665982).length < 2 ^ (prefixWord ++ tailWord_6665982).sum := by decide
  have hdescent : baseEnd_6665982 < baseStart_6665982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6665982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666002 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6666002 : Nat := 118140960795 + 6666002 * 2 ^ 59
def prefixEnd_6666002 : Nat := 4983230072969 + 3 ^ 40 * 6666002 * 2
def baseEnd_6666002 : Nat := 1140954356610777823406207

theorem tailTrace_6666002 : CollatzResearch.WordTrace tailWord_6666002 prefixEnd_6666002 1140954356610777823406207 := by
  unfold tailWord_6666002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60782266699055172837270065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162086044530813794232720173 60782266699055172837270065)
  ·
    refine ⟨45586700024291379627952549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60782266699055172837270065 45586700024291379627952549)
    ·
      refine ⟨8547506254554633680241103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45586700024291379627952549 8547506254554633680241103)
      ·
        refine ⟨12821259381831950520361655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547506254554633680241103 12821259381831950520361655)
        ·
          refine ⟨19231889072747925780542483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821259381831950520361655 19231889072747925780542483)
          ·
            refine ⟨28847833609121888670813725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19231889072747925780542483 28847833609121888670813725)
            ·
              refine ⟨10817937603420708251555147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28847833609121888670813725 10817937603420708251555147)
              ·
                refine ⟨16226906405131062377332721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817937603420708251555147 16226906405131062377332721)
                ·
                  refine ⟨12170179803848296782999541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16226906405131062377332721 12170179803848296782999541)
                  ·
                    refine ⟨1140954356610777823406207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12170179803848296782999541 1140954356610777823406207)
                    ·
                      rfl

theorem cell23_6666002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6666002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666002 prefixEnd_6666002 := by exact prefixLift 6666002
  have htrace : WordTrace (prefixWord ++ tailWord_6666002) baseStart_6666002 baseEnd_6666002 := by
    simpa [prefixWord, tailWord_6666002, baseEnd_6666002] using wordTrace_append hprefix tailTrace_6666002
  have hstable : (prefixWord ++ tailWord_6666002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666002).length < 2 ^ (prefixWord ++ tailWord_6666002).sum := by decide
  have hdescent : baseEnd_6666002 < baseStart_6666002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666005 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_6666005 : Nat := 118140960795 + 6666005 * 2 ^ 59
def prefixEnd_6666005 : Nat := 4983230072969 + 3 ^ 40 * 6666005 * 2
def baseEnd_6666005 : Nat := 3422864610274296958481107

theorem tailTrace_6666005 : CollatzResearch.WordTrace tailWord_6666005 prefixEnd_6666005 3422864610274296958481107 := by
  unfold tailWord_6666005
  simp only [CollatzResearch.WordTrace]
  refine ⟨243129176215209822861439469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162086117476806548574292979 243129176215209822861439469)
  ·
    refine ⟨91173441080703683573039801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243129176215209822861439469 91173441080703683573039801)
    ·
      refine ⟨68380080810527762679779851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91173441080703683573039801 68380080810527762679779851)
      ·
        refine ⟨102570121215791644019669777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68380080810527762679779851 102570121215791644019669777)
        ·
          refine ⟨76927590911843733014752333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102570121215791644019669777 76927590911843733014752333)
          ·
            refine ⟨28847846591941399880532125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76927590911843733014752333 28847846591941399880532125)
            ·
              refine ⟨10817942471978024955199547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28847846591941399880532125 10817942471978024955199547)
              ·
                refine ⟨16226913707967037432799321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817942471978024955199547 16226913707967037432799321)
                ·
                  refine ⟨12170185280975278074599491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16226913707967037432799321 12170185280975278074599491)
                  ·
                    refine ⟨18255277921462917111899237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12170185280975278074599491 18255277921462917111899237)
                    ·
                      refine ⟨3422864610274296958481107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18255277921462917111899237 3422864610274296958481107)
                      ·
                        rfl

theorem cell23_6666005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_6666005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666005 prefixEnd_6666005 := by exact prefixLift 6666005
  have htrace : WordTrace (prefixWord ++ tailWord_6666005) baseStart_6666005 baseEnd_6666005 := by
    simpa [prefixWord, tailWord_6666005, baseEnd_6666005] using wordTrace_append hprefix tailTrace_6666005
  have hstable : (prefixWord ++ tailWord_6666005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666005).length < 2 ^ (prefixWord ++ tailWord_6666005).sum := by decide
  have hdescent : baseEnd_6666005 < baseStart_6666005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666011 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 10]
def baseStart_6666011 : Nat := 118140960795 + 6666011 * 2 ^ 59
def prefixEnd_6666011 : Nat := 4983230072969 + 3 ^ 40 * 6666011 * 2
def baseEnd_6666011 : Nat := 380318632350913770556231

theorem tailTrace_6666011 : CollatzResearch.WordTrace tailWord_6666011 prefixEnd_6666011 380318632350913770556231 := by
  unfold tailWord_6666011
  simp only [CollatzResearch.WordTrace]
  refine ⟨243129395053188085886157887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162086263368792057257438591 243129395053188085886157887)
  ·
    refine ⟨364694092579782128829236831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243129395053188085886157887 364694092579782128829236831)
    ·
      refine ⟨547041138869673193243855247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364694092579782128829236831 547041138869673193243855247)
      ·
        refine ⟨820561708304509789865782871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547041138869673193243855247 820561708304509789865782871)
        ·
          refine ⟨1230842562456764684798674307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820561708304509789865782871 1230842562456764684798674307)
          ·
            refine ⟨1846263843685147027198011461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230842562456764684798674307 1846263843685147027198011461)
            ·
              refine ⟨346174470690965067599627149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1846263843685147027198011461 346174470690965067599627149)
              ·
                refine ⟨129815426509111900349860181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346174470690965067599627149 129815426509111900349860181)
                ·
                  refine ⟨380318632350913770556231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129815426509111900349860181 380318632350913770556231)
                  ·
                    rfl

theorem cell23_6666011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 10].length) (baseStart_6666011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666011 prefixEnd_6666011 := by exact prefixLift 6666011
  have htrace : WordTrace (prefixWord ++ tailWord_6666011) baseStart_6666011 baseEnd_6666011 := by
    simpa [prefixWord, tailWord_6666011, baseEnd_6666011] using wordTrace_append hprefix tailTrace_6666011
  have hstable : (prefixWord ++ tailWord_6666011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666011).length < 2 ^ (prefixWord ++ tailWord_6666011).sum := by decide
  have hdescent : baseEnd_6666011 < baseStart_6666011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666018 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_6666018 : Nat := 118140960795 + 6666018 * 2 ^ 59
def prefixEnd_6666018 : Nat := 4983230072969 + 3 ^ 40 * 6666018 * 2
def baseEnd_6666018 : Nat := 3422871285522805407618547

theorem tailTrace_6666018 : CollatzResearch.WordTrace tailWord_6666018 prefixEnd_6666018 3422871285522805407618547 := by
  unfold tailWord_6666018
  simp only [CollatzResearch.WordTrace]
  refine ⟨60782412591040681520415677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162086433576108484054441805 60782412591040681520415677)
  ·
    refine ⟨22793404721640255570155879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60782412591040681520415677 22793404721640255570155879)
    ·
      refine ⟨34190107082460383355233819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22793404721640255570155879 34190107082460383355233819)
      ·
        refine ⟨51285160623690575032850729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34190107082460383355233819 51285160623690575032850729)
        ·
          refine ⟨38463870467767931274638047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51285160623690575032850729 38463870467767931274638047)
          ·
            refine ⟨57695805701651896911957071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38463870467767931274638047 57695805701651896911957071)
            ·
              refine ⟨86543708552477845367935607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57695805701651896911957071 86543708552477845367935607)
              ·
                refine ⟨129815562828716768051903411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86543708552477845367935607 129815562828716768051903411)
                ·
                  refine ⟨194723344243075152077855117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129815562828716768051903411 194723344243075152077855117)
                  ·
                    refine ⟨73021254091153182029195669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194723344243075152077855117 73021254091153182029195669)
                    ·
                      refine ⟨3422871285522805407618547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73021254091153182029195669 3422871285522805407618547)
                      ·
                        rfl

theorem cell23_6666018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_6666018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666018 prefixEnd_6666018 := by exact prefixLift 6666018
  have htrace : WordTrace (prefixWord ++ tailWord_6666018) baseStart_6666018 baseEnd_6666018 := by
    simpa [prefixWord, tailWord_6666018, baseEnd_6666018] using wordTrace_append hprefix tailTrace_6666018
  have hstable : (prefixWord ++ tailWord_6666018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666018).length < 2 ^ (prefixWord ++ tailWord_6666018).sum := by decide
  have hdescent : baseEnd_6666018 < baseStart_6666018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666028 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 8]
def baseStart_6666028 : Nat := 118140960795 + 6666028 * 2 ^ 59
def prefixEnd_6666028 : Nat := 4983230072969 + 3 ^ 40 * 6666028 * 2
def baseEnd_6666028 : Nat := 380319602258816707610389

theorem tailTrace_6666028 : CollatzResearch.WordTrace tailWord_6666028 prefixEnd_6666028 380319602258816707610389 := by
  unfold tailWord_6666028
  simp only [CollatzResearch.WordTrace]
  refine ⟨121565007547063248894763369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162086676729417665193017825 121565007547063248894763369)
  ·
    refine ⟨91173755660297436671072527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121565007547063248894763369 91173755660297436671072527)
    ·
      refine ⟨136760633490446155006608791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91173755660297436671072527 136760633490446155006608791)
      ·
        refine ⟨205140950235669232509913187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136760633490446155006608791 205140950235669232509913187)
        ·
          refine ⟨307711425353503848764869781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205140950235669232509913187 307711425353503848764869781)
          ·
            refine ⟨14423973063445492910853271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 307711425353503848764869781 14423973063445492910853271)
            ·
              refine ⟨21635959595168239366279907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423973063445492910853271 21635959595168239366279907)
              ·
                refine ⟨32453939392752359049419861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21635959595168239366279907 32453939392752359049419861)
                ·
                  refine ⟨380319602258816707610389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32453939392752359049419861 380319602258816707610389)
                  ·
                    rfl

theorem cell23_6666028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_6666028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666028 prefixEnd_6666028 := by exact prefixLift 6666028
  have htrace : WordTrace (prefixWord ++ tailWord_6666028) baseStart_6666028 baseEnd_6666028 := by
    simpa [prefixWord, tailWord_6666028, baseEnd_6666028] using wordTrace_append hprefix tailTrace_6666028
  have hstable : (prefixWord ++ tailWord_6666028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666028).length < 2 ^ (prefixWord ++ tailWord_6666028).sum := by decide
  have hdescent : baseEnd_6666028 < baseStart_6666028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666112 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 5, 2, 2]
def baseStart_6666112 : Nat := 118140960795 + 6666112 * 2 ^ 59
def prefixEnd_6666112 : Nat := 4983230072969 + 3 ^ 40 * 6666112 * 2
def baseEnd_6666112 : Nat := 3422919552704328039843115

theorem tailTrace_6666112 : CollatzResearch.WordTrace tailWord_6666112 prefixEnd_6666112 3422919552704328039843115 := by
  unfold tailWord_6666112
  simp only [CollatzResearch.WordTrace]
  refine ⟨121566539412911090067792295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162088719217214786757056393 121566539412911090067792295)
  ·
    refine ⟨182349809119366635101688443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121566539412911090067792295 182349809119366635101688443)
    ·
      refine ⟨273524713679049952652532665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182349809119366635101688443 273524713679049952652532665)
      ·
        refine ⟨205143535259287464489399499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273524713679049952652532665 205143535259287464489399499)
        ·
          refine ⟨307715302888931196734099249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205143535259287464489399499 307715302888931196734099249)
          ·
            refine ⟨230786477166698397550574437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307715302888931196734099249 230786477166698397550574437)
            ·
              refine ⟨43272464468755949540732707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230786477166698397550574437 43272464468755949540732707)
              ·
                refine ⟨64908696703133924311099061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43272464468755949540732707 64908696703133924311099061)
                ·
                  refine ⟨6085190315918805404165537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64908696703133924311099061 6085190315918805404165537)
                  ·
                    refine ⟨4563892736939104053124153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6085190315918805404165537 4563892736939104053124153)
                    ·
                      refine ⟨3422919552704328039843115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563892736939104053124153 3422919552704328039843115)
                      ·
                        rfl

theorem cell23_6666112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_6666112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666112 prefixEnd_6666112 := by exact prefixLift 6666112
  have htrace : WordTrace (prefixWord ++ tailWord_6666112) baseStart_6666112 baseEnd_6666112 := by
    simpa [prefixWord, tailWord_6666112, baseEnd_6666112] using wordTrace_append hprefix tailTrace_6666112
  have hstable : (prefixWord ++ tailWord_6666112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666112).length < 2 ^ (prefixWord ++ tailWord_6666112).sum := by decide
  have hdescent : baseEnd_6666112 < baseStart_6666112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666122 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_6666122 : Nat := 118140960795 + 6666122 * 2 ^ 59
def prefixEnd_6666122 : Nat := 4983230072969 + 3 ^ 40 * 6666122 * 2
def baseEnd_6666122 : Nat := 1140974895836957666906023

theorem tailTrace_6666122 : CollatzResearch.WordTrace tailWord_6666122 prefixEnd_6666122 1140974895836957666906023 := by
  unfold tailWord_6666122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60783360888946487960862155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162088962370523967895632413 60783360888946487960862155)
  ·
    refine ⟨91175041333419731941293233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60783360888946487960862155 91175041333419731941293233)
    ·
      refine ⟨68381281000064798955969925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91175041333419731941293233 68381281000064798955969925)
      ·
        refine ⟨12821490187512149804244361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68381281000064798955969925 12821490187512149804244361)
        ·
          refine ⟨9616117640634112353183271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12821490187512149804244361 9616117640634112353183271)
          ·
            refine ⟨14424176460951168529774907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616117640634112353183271 14424176460951168529774907)
            ·
              refine ⟨21636264691426752794662361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14424176460951168529774907 21636264691426752794662361)
              ·
                refine ⟨16227198518570064595996771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21636264691426752794662361 16227198518570064595996771)
                ·
                  refine ⟨24340797777855096893995157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16227198518570064595996771 24340797777855096893995157)
                  ·
                    refine ⟨1140974895836957666906023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24340797777855096893995157 1140974895836957666906023)
                    ·
                      rfl

theorem cell23_6666122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_6666122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666122 prefixEnd_6666122 := by exact prefixLift 6666122
  have htrace : WordTrace (prefixWord ++ tailWord_6666122) baseStart_6666122 baseEnd_6666122 := by
    simpa [prefixWord, tailWord_6666122, baseEnd_6666122] using wordTrace_append hprefix tailTrace_6666122
  have hstable : (prefixWord ++ tailWord_6666122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666122).length < 2 ^ (prefixWord ++ tailWord_6666122).sum := by decide
  have hdescent : baseEnd_6666122 < baseStart_6666122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666126 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_6666126 : Nat := 118140960795 + 6666126 * 2 ^ 59
def prefixEnd_6666126 : Nat := 4983230072969 + 3 ^ 40 * 6666126 * 2
def baseEnd_6666126 : Nat := 1140975580477830328356017

theorem tailTrace_6666126 : CollatzResearch.WordTrace tailWord_6666126 prefixEnd_6666126 1140975580477830328356017 := by
  unfold tailWord_6666126
  simp only [CollatzResearch.WordTrace]
  refine ⟨30391698680971432565824279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162089059631847640351062821 30391698680971432565824279)
  ·
    refine ⟨45587548021457148848736419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30391698680971432565824279 45587548021457148848736419)
    ·
      refine ⟨68381322032185723273104629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45587548021457148848736419 68381322032185723273104629)
      ·
        refine ⟨6410748940517411556853559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68381322032185723273104629 6410748940517411556853559)
        ·
          refine ⟨9616123410776117335280339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410748940517411556853559 9616123410776117335280339)
          ·
            refine ⟨14424185116164176002920509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616123410776117335280339 14424185116164176002920509)
            ·
              refine ⟨5409069418561566001095191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14424185116164176002920509 5409069418561566001095191)
              ·
                refine ⟨8113604127842349001642787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409069418561566001095191 8113604127842349001642787)
                ·
                  refine ⟨12170406191763523502464181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8113604127842349001642787 12170406191763523502464181)
                  ·
                    refine ⟨1140975580477830328356017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12170406191763523502464181 1140975580477830328356017)
                    ·
                      rfl

theorem cell23_6666126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_6666126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666126 prefixEnd_6666126 := by exact prefixLift 6666126
  have htrace : WordTrace (prefixWord ++ tailWord_6666126) baseStart_6666126 baseEnd_6666126 := by
    simpa [prefixWord, tailWord_6666126, baseEnd_6666126] using wordTrace_append hprefix tailTrace_6666126
  have hstable : (prefixWord ++ tailWord_6666126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666126).length < 2 ^ (prefixWord ++ tailWord_6666126).sum := by decide
  have hdescent : baseEnd_6666126 < baseStart_6666126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666132 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_6666132 : Nat := 118140960795 + 6666132 * 2 ^ 59
def prefixEnd_6666132 : Nat := 4983230072969 + 3 ^ 40 * 6666132 * 2
def baseEnd_6666132 : Nat := 3422929822317417961593023

theorem tailTrace_6666132 : CollatzResearch.WordTrace tailWord_6666132 prefixEnd_6666132 3422929822317417961593023 := by
  unfold tailWord_6666132
  simp only [CollatzResearch.WordTrace]
  refine ⟨121566904142874861775656325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162089205523833149034208433 121566904142874861775656325)
  ·
    refine ⟨22793794526789036582935561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121566904142874861775656325 22793794526789036582935561)
    ·
      refine ⟨17095345895091777437201671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22793794526789036582935561 17095345895091777437201671)
      ·
        refine ⟨25643018842637666155802507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17095345895091777437201671 25643018842637666155802507)
        ·
          refine ⟨38464528263956499233703761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25643018842637666155802507 38464528263956499233703761)
          ·
            refine ⟨28848396197967374425277821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38464528263956499233703761 28848396197967374425277821)
            ·
              refine ⟨10818148574237765409479183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28848396197967374425277821 10818148574237765409479183)
              ·
                refine ⟨16227222861356648114218775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10818148574237765409479183 16227222861356648114218775)
                ·
                  refine ⟨24340834292034972171328163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16227222861356648114218775 24340834292034972171328163)
                  ·
                    refine ⟨36511251438052458256992245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24340834292034972171328163 36511251438052458256992245)
                    ·
                      refine ⟨3422929822317417961593023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36511251438052458256992245 3422929822317417961593023)
                      ·
                        rfl

theorem cell23_6666132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_6666132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666132 prefixEnd_6666132 := by exact prefixLift 6666132
  have htrace : WordTrace (prefixWord ++ tailWord_6666132) baseStart_6666132 baseEnd_6666132 := by
    simpa [prefixWord, tailWord_6666132, baseEnd_6666132] using wordTrace_append hprefix tailTrace_6666132
  have hstable : (prefixWord ++ tailWord_6666132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666132).length < 2 ^ (prefixWord ++ tailWord_6666132).sum := by decide
  have hdescent : baseEnd_6666132 < baseStart_6666132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666155 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 9, 2]
def baseStart_6666155 : Nat := 118140960795 + 6666155 * 2 ^ 59
def prefixEnd_6666155 : Nat := 4983230072969 + 3 ^ 40 * 6666155 * 2
def baseEnd_6666155 : Nat := 3422941632372471371605417

theorem tailTrace_6666155 : CollatzResearch.WordTrace tailWord_6666155 prefixEnd_6666155 3422941632372471371605417 := by
  unfold tailWord_6666155
  simp only [CollatzResearch.WordTrace]
  refine ⟨243134647164666398479399919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162089764776444265652933279 243134647164666398479399919)
  ·
    refine ⟨364701970746999597719099879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243134647164666398479399919 364701970746999597719099879)
    ·
      refine ⟨547052956120499396578649819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364701970746999597719099879 547052956120499396578649819)
      ·
        refine ⟨820579434180749094867974729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547052956120499396578649819 820579434180749094867974729)
        ·
          refine ⟨615434575635561821150981047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820579434180749094867974729 615434575635561821150981047)
          ·
            refine ⟨923151863453342731726471571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615434575635561821150981047 923151863453342731726471571)
            ·
              refine ⟨1384727795180014097589707357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923151863453342731726471571 1384727795180014097589707357)
              ·
                refine ⟨519272923192505286596140259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384727795180014097589707357 519272923192505286596140259)
                ·
                  refine ⟨778909384788757929894210389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519272923192505286596140259 778909384788757929894210389)
                  ·
                    refine ⟨4563922176496628495473889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 778909384788757929894210389 4563922176496628495473889)
                    ·
                      refine ⟨3422941632372471371605417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563922176496628495473889 3422941632372471371605417)
                      ·
                        rfl

theorem cell23_6666155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9, 2].length) (baseStart_6666155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666155 prefixEnd_6666155 := by exact prefixLift 6666155
  have htrace : WordTrace (prefixWord ++ tailWord_6666155) baseStart_6666155 baseEnd_6666155 := by
    simpa [prefixWord, tailWord_6666155, baseEnd_6666155] using wordTrace_append hprefix tailTrace_6666155
  have hstable : (prefixWord ++ tailWord_6666155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666155).length < 2 ^ (prefixWord ++ tailWord_6666155).sum := by decide
  have hdescent : baseEnd_6666155 < baseStart_6666155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666219 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 2, 2, 2]
def baseStart_6666219 : Nat := 118140960795 + 6666219 * 2 ^ 59
def prefixEnd_6666219 : Nat := 4983230072969 + 3 ^ 40 * 6666219 * 2
def baseEnd_6666219 : Nat := 3422974495134359121205123

theorem tailTrace_6666219 : CollatzResearch.WordTrace tailWord_6666219 prefixEnd_6666219 3422974495134359121205123 := by
  unfold tailWord_6666219
  simp only [CollatzResearch.WordTrace]
  refine ⟨243136981436434537409729711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162091320957623024939819807 243136981436434537409729711)
  ·
    refine ⟨364705472154651806114594567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243136981436434537409729711 364705472154651806114594567)
    ·
      refine ⟨547058208231977709171891851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364705472154651806114594567 547058208231977709171891851)
      ·
        refine ⟨820587312347966563757837777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547058208231977709171891851 820587312347966563757837777)
        ·
          refine ⟨615440484260974922818378333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820587312347966563757837777 615440484260974922818378333)
          ·
            refine ⟨230790181597865596056891875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615440484260974922818378333 230790181597865596056891875)
            ·
              refine ⟨346185272396798394085337813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230790181597865596056891875 346185272396798394085337813)
              ·
                refine ⟨8113717321799962361375105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 346185272396798394085337813 8113717321799962361375105)
                ·
                  refine ⟨6085287991349971771031329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8113717321799962361375105 6085287991349971771031329)
                  ·
                    refine ⟨4563965993512478828273497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6085287991349971771031329 4563965993512478828273497)
                    ·
                      refine ⟨3422974495134359121205123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4563965993512478828273497 3422974495134359121205123)
                      ·
                        rfl

theorem cell23_6666219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 2, 2].length) (baseStart_6666219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666219 prefixEnd_6666219 := by exact prefixLift 6666219
  have htrace : WordTrace (prefixWord ++ tailWord_6666219) baseStart_6666219 baseEnd_6666219 := by
    simpa [prefixWord, tailWord_6666219, baseEnd_6666219] using wordTrace_append hprefix tailTrace_6666219
  have hstable : (prefixWord ++ tailWord_6666219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666219).length < 2 ^ (prefixWord ++ tailWord_6666219).sum := by decide
  have hdescent : baseEnd_6666219 < baseStart_6666219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666235 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 3]
def baseStart_6666235 : Nat := 118140960795 + 6666235 * 2 ^ 59
def prefixEnd_6666235 : Nat := 4983230072969 + 3 ^ 40 * 6666235 * 2
def baseEnd_6666235 : Nat := 3422982710824831058605049

theorem tailTrace_6666235 : CollatzResearch.WordTrace tailWord_6666235 prefixEnd_6666235 3422982710824831058605049 := by
  unfold tailWord_6666235
  simp only [CollatzResearch.WordTrace]
  refine ⟨243137565004376572142312159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162091710002917714761541439 243137565004376572142312159)
  ·
    refine ⟨364706347506564858213468239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243137565004376572142312159 364706347506564858213468239)
    ·
      refine ⟨547059521259847287320202359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364706347506564858213468239 547059521259847287320202359)
      ·
        refine ⟨820589281889770930980303539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547059521259847287320202359 820589281889770930980303539)
        ·
          refine ⟨1230883922834656396470455309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820589281889770930980303539 1230883922834656396470455309)
          ·
            refine ⟨461581471062996148676420741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1230883922834656396470455309 461581471062996148676420741)
            ·
              refine ⟨86546525824311777876828889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461581471062996148676420741 86546525824311777876828889)
              ·
                refine ⟨64909894368233833407621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86546525824311777876828889 64909894368233833407621667)
                ·
                  refine ⟨97364841552350750111432501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64909894368233833407621667 97364841552350750111432501)
                  ·
                    refine ⟨9127953895532882822946797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97364841552350750111432501 9127953895532882822946797)
                    ·
                      refine ⟨3422982710824831058605049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9127953895532882822946797 3422982710824831058605049)
                      ·
                        rfl

theorem cell23_6666235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 3].length) (baseStart_6666235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666235 prefixEnd_6666235 := by exact prefixLift 6666235
  have htrace : WordTrace (prefixWord ++ tailWord_6666235) baseStart_6666235 baseEnd_6666235 := by
    simpa [prefixWord, tailWord_6666235, baseEnd_6666235] using wordTrace_append hprefix tailTrace_6666235
  have hstable : (prefixWord ++ tailWord_6666235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666235).length < 2 ^ (prefixWord ++ tailWord_6666235).sum := by decide
  have hdescent : baseEnd_6666235 < baseStart_6666235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666312 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_6666312 : Nat := 118140960795 + 6666312 * 2 ^ 59
def prefixEnd_6666312 : Nat := 4983230072969 + 3 ^ 40 * 6666312 * 2
def baseEnd_6666312 : Nat := 3423022248835227257342195

theorem tailTrace_6666312 : CollatzResearch.WordTrace tailWord_6666312 prefixEnd_6666312 3423022248835227257342195 := by
  unfold tailWord_6666312
  simp only [CollatzResearch.WordTrace]
  refine ⟨121570186712548807146432595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162093582283398409528576793 121570186712548807146432595)
  ·
    refine ⟨182355280068823210719648893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121570186712548807146432595 182355280068823210719648893)
    ·
      refine ⟨68383230025808704019868335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182355280068823210719648893 68383230025808704019868335)
      ·
        refine ⟨102574845038713056029802503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68383230025808704019868335 102574845038713056029802503)
        ·
          refine ⟨153862267558069584044703755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102574845038713056029802503 153862267558069584044703755)
          ·
            refine ⟨230793401337104376067055633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153862267558069584044703755 230793401337104376067055633)
            ·
              refine ⟨173095051002828282050291725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230793401337104376067055633 173095051002828282050291725)
              ·
                refine ⟨64910644126060605768859397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173095051002828282050291725 64910644126060605768859397)
                ·
                  refine ⟨12170745773636363581661137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64910644126060605768859397 12170745773636363581661137)
                  ·
                    refine ⟨9128059330227272686245853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12170745773636363581661137 9128059330227272686245853)
                    ·
                      refine ⟨3423022248835227257342195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9128059330227272686245853 3423022248835227257342195)
                      ·
                        rfl

theorem cell23_6666312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_6666312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666312 prefixEnd_6666312 := by exact prefixLift 6666312
  have htrace : WordTrace (prefixWord ++ tailWord_6666312) baseStart_6666312 baseEnd_6666312 := by
    simpa [prefixWord, tailWord_6666312, baseEnd_6666312] using wordTrace_append hprefix tailTrace_6666312
  have hstable : (prefixWord ++ tailWord_6666312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666312).length < 2 ^ (prefixWord ++ tailWord_6666312).sum := by decide
  have hdescent : baseEnd_6666312 < baseStart_6666312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666319 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 1, 4]
def baseStart_6666319 : Nat := 118140960795 + 6666319 * 2 ^ 59
def prefixEnd_6666319 : Nat := 4983230072969 + 3 ^ 40 * 6666319 * 2
def baseEnd_6666319 : Nat := 1141008614399936243318221

theorem tailTrace_6666319 : CollatzResearch.WordTrace tailWord_6666319 prefixEnd_6666319 1141008614399936243318221 := by
  unfold tailWord_6666319
  simp only [CollatzResearch.WordTrace]
  refine ⟨243140628736072254488370011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162093752490714836325580007 243140628736072254488370011)
  ·
    refine ⟨364710943104108381732555017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243140628736072254488370011 364710943104108381732555017)
    ·
      refine ⟨273533207328081286299416263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364710943104108381732555017 273533207328081286299416263)
      ·
        refine ⟨410299810992121929449124395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273533207328081286299416263 410299810992121929449124395)
        ·
          refine ⟨615449716488182894173686593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410299810992121929449124395 615449716488182894173686593)
          ·
            refine ⟨461587287366137170630264945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615449716488182894173686593 461587287366137170630264945)
            ·
              refine ⟨346190465524602877972698709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461587287366137170630264945 346190465524602877972698709)
              ·
                refine ⟨4056919517866439976242563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 346190465524602877972698709 4056919517866439976242563)
                ·
                  refine ⟨6085379276799659964363845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056919517866439976242563 6085379276799659964363845)
                  ·
                    refine ⟨1141008614399936243318221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6085379276799659964363845 1141008614399936243318221)
                    ·
                      rfl

theorem cell23_6666319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 4].length) (baseStart_6666319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666319 prefixEnd_6666319 := by exact prefixLift 6666319
  have htrace : WordTrace (prefixWord ++ tailWord_6666319) baseStart_6666319 baseEnd_6666319 := by
    simpa [prefixWord, tailWord_6666319, baseEnd_6666319] using wordTrace_append hprefix tailTrace_6666319
  have hstable : (prefixWord ++ tailWord_6666319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666319).length < 2 ^ (prefixWord ++ tailWord_6666319).sum := by decide
  have hdescent : baseEnd_6666319 < baseStart_6666319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666335 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_6666335 : Nat := 118140960795 + 6666335 * 2 ^ 59
def prefixEnd_6666335 : Nat := 4983230072969 + 3 ^ 40 * 6666335 * 2
def baseEnd_6666335 : Nat := 3423034058890280667354589

theorem tailTrace_6666335 : CollatzResearch.WordTrace tailWord_6666335 prefixEnd_6666335 3423034058890280667354589 := by
  unfold tailWord_6666335
  simp only [CollatzResearch.WordTrace]
  refine ⟨243141212304014289220952459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162094141536009526147301639 243141212304014289220952459)
  ·
    refine ⟨364711818456021433831428689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243141212304014289220952459 364711818456021433831428689)
    ·
      refine ⟨273533863842016075373571517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364711818456021433831428689 273533863842016075373571517)
      ·
        refine ⟨102575198940756028265089319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273533863842016075373571517 102575198940756028265089319)
        ·
          refine ⟨153862798411134042397633979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102575198940756028265089319 153862798411134042397633979)
          ·
            refine ⟨230794197616701063596450969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153862798411134042397633979 230794197616701063596450969)
            ·
              refine ⟨173095648212525797697338227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230794197616701063596450969 173095648212525797697338227)
              ·
                refine ⟨259643472318788696546007341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173095648212525797697338227 259643472318788696546007341)
                ·
                  refine ⟨97366302119545761204752753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259643472318788696546007341 97366302119545761204752753)
                  ·
                    refine ⟨73024726589659320903564565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97366302119545761204752753 73024726589659320903564565)
                    ·
                      refine ⟨3423034058890280667354589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73024726589659320903564565 3423034058890280667354589)
                      ·
                        rfl

theorem cell23_6666335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_6666335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666335 prefixEnd_6666335 := by exact prefixLift 6666335
  have htrace : WordTrace (prefixWord ++ tailWord_6666335) baseStart_6666335 baseEnd_6666335 := by
    simpa [prefixWord, tailWord_6666335, baseEnd_6666335] using wordTrace_append hprefix tailTrace_6666335
  have hstable : (prefixWord ++ tailWord_6666335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666335).length < 2 ^ (prefixWord ++ tailWord_6666335).sum := by decide
  have hdescent : baseEnd_6666335 < baseStart_6666335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666376 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6666376 : Nat := 118140960795 + 6666376 * 2 ^ 59
def prefixEnd_6666376 : Nat := 4983230072969 + 3 ^ 40 * 6666376 * 2
def baseEnd_6666376 : Nat := 3423055111597115006941901

theorem tailTrace_6666376 : CollatzResearch.WordTrace tailWord_6666376 prefixEnd_6666376 3423055111597115006941901 := by
  unfold tailWord_6666376
  simp only [CollatzResearch.WordTrace]
  refine ⟨121571353848432876611597491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162095138464577168815463321 121571353848432876611597491)
  ·
    refine ⟨182357030772649314917396237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121571353848432876611597491 182357030772649314917396237)
    ·
      refine ⟨68383886539743493094023589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182357030772649314917396237 68383886539743493094023589)
      ·
        refine ⟨12821978726201904955129423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68383886539743493094023589 12821978726201904955129423)
        ·
          refine ⟨19232968089302857432694135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821978726201904955129423 19232968089302857432694135)
          ·
            refine ⟨28849452133954286149041203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19232968089302857432694135 28849452133954286149041203)
            ·
              refine ⟨43274178200931429223561805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28849452133954286149041203 43274178200931429223561805)
              ·
                refine ⟨16227816825349285958835677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43274178200931429223561805 16227816825349285958835677)
                ·
                  refine ⟨6085431309505982234563379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16227816825349285958835677 6085431309505982234563379)
                  ·
                    refine ⟨9128146964258973351845069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6085431309505982234563379 9128146964258973351845069)
                    ·
                      refine ⟨3423055111597115006941901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9128146964258973351845069 3423055111597115006941901)
                      ·
                        rfl

theorem cell23_6666376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6666376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666376 prefixEnd_6666376 := by exact prefixLift 6666376
  have htrace : WordTrace (prefixWord ++ tailWord_6666376) baseStart_6666376 baseEnd_6666376 := by
    simpa [prefixWord, tailWord_6666376, baseEnd_6666376] using wordTrace_append hprefix tailTrace_6666376
  have hstable : (prefixWord ++ tailWord_6666376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666376).length < 2 ^ (prefixWord ++ tailWord_6666376).sum := by decide
  have hdescent : baseEnd_6666376 < baseStart_6666376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666442 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_6666442 : Nat := 118140960795 + 6666442 * 2 ^ 59
def prefixEnd_6666442 : Nat := 4983230072969 + 3 ^ 40 * 6666442 * 2
def baseEnd_6666442 : Nat := 3423089001320311748716597

theorem tailTrace_6666442 : CollatzResearch.WordTrace tailWord_6666442 prefixEnd_6666442 3423089001320311748716597 := by
  unfold tailWord_6666442
  simp only [CollatzResearch.WordTrace]
  refine ⟨60786278728656661623774395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162096743276417764330065053 60786278728656661623774395)
  ·
    refine ⟨91179418092984992435661593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60786278728656661623774395 91179418092984992435661593)
    ·
      refine ⟨68384563569738744326746195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91179418092984992435661593 68384563569738744326746195)
      ·
        refine ⟨102576845354608116490119293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68384563569738744326746195 102576845354608116490119293)
        ·
          refine ⟨38466317007978043683794735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102576845354608116490119293 38466317007978043683794735)
          ·
            refine ⟨57699475511967065525692103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38466317007978043683794735 57699475511967065525692103)
            ·
              refine ⟨86549213267950598288538155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57699475511967065525692103 86549213267950598288538155)
              ·
                refine ⟨129823819901925897432807233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86549213267950598288538155 129823819901925897432807233)
                ·
                  refine ⟨97367864926444423074605425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129823819901925897432807233 97367864926444423074605425)
                  ·
                    refine ⟨73025898694833317305954069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97367864926444423074605425 73025898694833317305954069)
                    ·
                      refine ⟨3423089001320311748716597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73025898694833317305954069 3423089001320311748716597)
                      ·
                        rfl

theorem cell23_6666442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_6666442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666442 prefixEnd_6666442 := by exact prefixLift 6666442
  have htrace : WordTrace (prefixWord ++ tailWord_6666442) baseStart_6666442 baseEnd_6666442 := by
    simpa [prefixWord, tailWord_6666442, baseEnd_6666442] using wordTrace_append hprefix tailTrace_6666442
  have hstable : (prefixWord ++ tailWord_6666442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666442).length < 2 ^ (prefixWord ++ tailWord_6666442).sum := by decide
  have hdescent : baseEnd_6666442 < baseStart_6666442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666506 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_6666506 : Nat := 118140960795 + 6666506 * 2 ^ 59
def prefixEnd_6666506 : Nat := 4983230072969 + 3 ^ 40 * 6666506 * 2
def baseEnd_6666506 : Nat := 3423121864082199498316303

theorem tailTrace_6666506 : CollatzResearch.WordTrace tailWord_6666506 prefixEnd_6666506 3423121864082199498316303 := by
  unfold tailWord_6666506
  simp only [CollatzResearch.WordTrace]
  refine ⟨60786862296598696356356843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162098299457596523616951581 60786862296598696356356843)
  ·
    refine ⟨91180293444898044534535265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60786862296598696356356843 91180293444898044534535265)
    ·
      refine ⟨68385220083673533400901449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91180293444898044534535265 68385220083673533400901449)
      ·
        refine ⟨51288915062755150050676087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68385220083673533400901449 51288915062755150050676087)
        ·
          refine ⟨76933372594132725076014131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51288915062755150050676087 76933372594132725076014131)
          ·
            refine ⟨115400058891199087614021197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76933372594132725076014131 115400058891199087614021197)
            ·
              refine ⟨43275022084199657855257949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115400058891199087614021197 43275022084199657855257949)
              ·
                refine ⟨16228133281574871695721731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43275022084199657855257949 16228133281574871695721731)
                ·
                  refine ⟨24342199922362307543582597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16228133281574871695721731 24342199922362307543582597)
                  ·
                    refine ⟨4564162485442932664421737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24342199922362307543582597 4564162485442932664421737)
                    ·
                      refine ⟨3423121864082199498316303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564162485442932664421737 3423121864082199498316303)
                      ·
                        rfl

theorem cell23_6666506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_6666506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666506 prefixEnd_6666506 := by exact prefixLift 6666506
  have htrace : WordTrace (prefixWord ++ tailWord_6666506) baseStart_6666506 baseEnd_6666506 := by
    simpa [prefixWord, tailWord_6666506, baseEnd_6666506] using wordTrace_append hprefix tailTrace_6666506
  have hstable : (prefixWord ++ tailWord_6666506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666506).length < 2 ^ (prefixWord ++ tailWord_6666506).sum := by decide
  have hdescent : baseEnd_6666506 < baseStart_6666506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666546 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_6666546 : Nat := 118140960795 + 6666546 * 2 ^ 59
def prefixEnd_6666546 : Nat := 4983230072969 + 3 ^ 40 * 6666546 * 2
def baseEnd_6666546 : Nat := 380349155923153260201791

theorem tailTrace_6666546 : CollatzResearch.WordTrace tailWord_6666546 prefixEnd_6666546 380349155923153260201791 := by
  unfold tailWord_6666546
  simp only [CollatzResearch.WordTrace]
  refine ⟨60787227026562468064220873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162099272070833248171255661 60787227026562468064220873)
  ·
    refine ⟨45590420269921851048165655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60787227026562468064220873 45590420269921851048165655)
    ·
      refine ⟨68385630404882776572248483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45590420269921851048165655 68385630404882776572248483)
      ·
        refine ⟨102578445607324164858372725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68385630404882776572248483 102578445607324164858372725)
        ·
          refine ⟨9616729275686640455472443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102578445607324164858372725 9616729275686640455472443)
          ·
            refine ⟨14425093913529960683208665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616729275686640455472443 14425093913529960683208665)
            ·
              refine ⟨10818820435147470512406499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14425093913529960683208665 10818820435147470512406499)
              ·
                refine ⟨16228230652721205768609749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10818820435147470512406499 16228230652721205768609749)
                ·
                  refine ⟨380349155923153260201791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16228230652721205768609749 380349155923153260201791)
                  ·
                    rfl

theorem cell23_6666546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_6666546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666546 prefixEnd_6666546 := by exact prefixLift 6666546
  have htrace : WordTrace (prefixWord ++ tailWord_6666546) baseStart_6666546 baseEnd_6666546 := by
    simpa [prefixWord, tailWord_6666546, baseEnd_6666546] using wordTrace_append hprefix tailTrace_6666546
  have hstable : (prefixWord ++ tailWord_6666546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666546).length < 2 ^ (prefixWord ++ tailWord_6666546).sum := by decide
  have hdescent : baseEnd_6666546 < baseStart_6666546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666596 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_6666596 : Nat := 118140960795 + 6666596 * 2 ^ 59
def prefixEnd_6666596 : Nat := 4983230072969 + 3 ^ 40 * 6666596 * 2
def baseEnd_6666596 : Nat := 3423168077341104146190889

theorem tailTrace_6666596 : CollatzResearch.WordTrace tailWord_6666596 prefixEnd_6666596 3423168077341104146190889 := by
  unfold tailWord_6666596
  simp only [CollatzResearch.WordTrace]
  refine ⟨121575365878034365398101821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162100487837379153864135761 121575365878034365398101821)
  ·
    refine ⟨45590762204262887024288183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121575365878034365398101821 45590762204262887024288183)
    ·
      refine ⟨68386143306394330536432275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45590762204262887024288183 68386143306394330536432275)
      ·
        refine ⟨102579214959591495804648413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68386143306394330536432275 102579214959591495804648413)
        ·
          refine ⟨38467205609846810926743155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102579214959591495804648413 38467205609846810926743155)
          ·
            refine ⟨57700808414770216390114733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38467205609846810926743155 57700808414770216390114733)
            ·
              refine ⟨21637803155538831146293025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57700808414770216390114733 21637803155538831146293025)
              ·
                refine ⟨16228352366654123359719769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21637803155538831146293025 16228352366654123359719769)
                ·
                  refine ⟨12171264274990592519789827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16228352366654123359719769 12171264274990592519789827)
                  ·
                    refine ⟨18256896412485888779684741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12171264274990592519789827 18256896412485888779684741)
                    ·
                      refine ⟨3423168077341104146190889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18256896412485888779684741 3423168077341104146190889)
                      ·
                        rfl

theorem cell23_6666596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_6666596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666596 prefixEnd_6666596 := by exact prefixLift 6666596
  have htrace : WordTrace (prefixWord ++ tailWord_6666596) baseStart_6666596 baseEnd_6666596 := by
    simpa [prefixWord, tailWord_6666596, baseEnd_6666596] using wordTrace_append hprefix tailTrace_6666596
  have hstable : (prefixWord ++ tailWord_6666596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666596).length < 2 ^ (prefixWord ++ tailWord_6666596).sum := by decide
  have hdescent : baseEnd_6666596 < baseStart_6666596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666633 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_6666633 : Nat := 118140960795 + 6666633 * 2 ^ 59
def prefixEnd_6666633 : Nat := 4983230072969 + 3 ^ 40 * 6666633 * 2
def baseEnd_6666633 : Nat := 3423187076125320501428219

theorem tailTrace_6666633 : CollatzResearch.WordTrace tailWord_6666633 prefixEnd_6666633 3423187076125320501428219 := by
  unfold tailWord_6666633
  simp only [CollatzResearch.WordTrace]
  refine ⟨243152081256934686115300553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162101387504623124076867035 243152081256934686115300553)
  ·
    refine ⟨182364060942701014586475415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243152081256934686115300553 182364060942701014586475415)
    ·
      refine ⟨273546091414051521879713123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182364060942701014586475415 273546091414051521879713123)
      ·
        refine ⟨410319137121077282819569685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273546091414051521879713123 410319137121077282819569685)
        ·
          refine ⟨19233709552550497632167329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 410319137121077282819569685 19233709552550497632167329)
          ·
            refine ⟨14425282164412873224125497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19233709552550497632167329 14425282164412873224125497)
            ·
              refine ⟨10818961623309654918094123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14425282164412873224125497 10818961623309654918094123)
              ·
                refine ⟨16228442434964482377141185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10818961623309654918094123 16228442434964482377141185)
                ·
                  refine ⟨12171331826223361782855889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16228442434964482377141185 12171331826223361782855889)
                  ·
                    refine ⟨9128498869667521337141917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12171331826223361782855889 9128498869667521337141917)
                    ·
                      refine ⟨3423187076125320501428219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9128498869667521337141917 3423187076125320501428219)
                      ·
                        rfl

theorem cell23_6666633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_6666633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666633 prefixEnd_6666633 := by exact prefixLift 6666633
  have htrace : WordTrace (prefixWord ++ tailWord_6666633) baseStart_6666633 baseEnd_6666633 := by
    simpa [prefixWord, tailWord_6666633, baseEnd_6666633] using wordTrace_append hprefix tailTrace_6666633
  have hstable : (prefixWord ++ tailWord_6666633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666633).length < 2 ^ (prefixWord ++ tailWord_6666633).sum := by decide
  have hdescent : baseEnd_6666633 < baseStart_6666633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666653 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 6]
def baseStart_6666653 : Nat := 118140960795 + 6666653 * 2 ^ 59
def prefixEnd_6666653 : Nat := 4983230072969 + 3 ^ 40 * 6666653 * 2
def baseEnd_6666653 : Nat := 380355260637601158130903

theorem tailTrace_6666653 : CollatzResearch.WordTrace tailWord_6666653 prefixEnd_6666653 380355260637601158130903 := by
  unfold tailWord_6666653
  simp only [CollatzResearch.WordTrace]
  refine ⟨243152810716862229531028613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162101873811241486354019075 243152810716862229531028613)
  ·
    refine ⟨45591152009411668037067865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243152810716862229531028613 45591152009411668037067865)
    ·
      refine ⟨34193364007058751027800899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45591152009411668037067865 34193364007058751027800899)
      ·
        refine ⟨51290046010588126541701349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34193364007058751027800899 51290046010588126541701349)
        ·
          refine ⟨9616883626985273726569003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51290046010588126541701349 9616883626985273726569003)
          ·
            refine ⟨14425325440477910589853505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616883626985273726569003 14425325440477910589853505)
            ·
              refine ⟨10818994080358432942390129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14425325440477910589853505 10818994080358432942390129)
              ·
                refine ⟨8114245560268824706792597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10818994080358432942390129 8114245560268824706792597)
                ·
                  refine ⟨380355260637601158130903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8114245560268824706792597 380355260637601158130903)
                  ·
                    rfl

theorem cell23_6666653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_6666653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666653 prefixEnd_6666653 := by exact prefixLift 6666653
  have htrace : WordTrace (prefixWord ++ tailWord_6666653) baseStart_6666653 baseEnd_6666653 := by
    simpa [prefixWord, tailWord_6666653, baseEnd_6666653] using wordTrace_append hprefix tailTrace_6666653
  have hstable : (prefixWord ++ tailWord_6666653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666653).length < 2 ^ (prefixWord ++ tailWord_6666653).sum := by decide
  have hdescent : baseEnd_6666653 < baseStart_6666653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666657 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 1, 4]
def baseStart_6666657 : Nat := 118140960795 + 6666657 * 2 ^ 59
def prefixEnd_6666657 : Nat := 4983230072969 + 3 ^ 40 * 6666657 * 2
def baseEnd_6666657 : Nat := 1141066466553676135842703

theorem tailTrace_6666657 : CollatzResearch.WordTrace tailWord_6666657 prefixEnd_6666657 1141066466553676135842703 := by
  unfold tailWord_6666657
  simp only [CollatzResearch.WordTrace]
  refine ⟨243152956608847738214174225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162101971072565158809449483 243152956608847738214174225)
  ·
    refine ⟨182364717456635803660630669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243152956608847738214174225 182364717456635803660630669)
    ·
      refine ⟨68386769046238426372736501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182364717456635803660630669 68386769046238426372736501)
      ·
        refine ⟨6411259598084852472444047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68386769046238426372736501 6411259598084852472444047)
        ·
          refine ⟨9616889397127278708666071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411259598084852472444047 9616889397127278708666071)
          ·
            refine ⟨14425334095690918062999107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616889397127278708666071 14425334095690918062999107)
            ·
              refine ⟨21638001143536377094498661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14425334095690918062999107 21638001143536377094498661)
              ·
                refine ⟨4057125214413070705218499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21638001143536377094498661 4057125214413070705218499)
                ·
                  refine ⟨6085687821619606057827749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057125214413070705218499 6085687821619606057827749)
                  ·
                    refine ⟨1141066466553676135842703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6085687821619606057827749 1141066466553676135842703)
                    ·
                      rfl

theorem cell23_6666657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_6666657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666657 prefixEnd_6666657 := by exact prefixLift 6666657
  have htrace : WordTrace (prefixWord ++ tailWord_6666657) baseStart_6666657 baseEnd_6666657 := by
    simpa [prefixWord, tailWord_6666657, baseEnd_6666657] using wordTrace_append hprefix tailTrace_6666657
  have hstable : (prefixWord ++ tailWord_6666657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666657).length < 2 ^ (prefixWord ++ tailWord_6666657).sum := by decide
  have hdescent : baseEnd_6666657 < baseStart_6666657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666696 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_6666696 : Nat := 118140960795 + 6666696 * 2 ^ 59
def prefixEnd_6666696 : Nat := 4983230072969 + 3 ^ 40 * 6666696 * 2
def baseEnd_6666696 : Nat := 1141073141802184584980143

theorem tailTrace_6666696 : CollatzResearch.WordTrace tailWord_6666696 prefixEnd_6666696 1141073141802184584980143 := by
  unfold tailWord_6666696
  simp only [CollatzResearch.WordTrace]
  refine ⟨121577189527853223937421971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162102919370470965249895961 121577189527853223937421971)
  ·
    refine ⟨182365784291779835906132957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121577189527853223937421971 182365784291779835906132957)
    ·
      refine ⟨68387169109417438464799859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182365784291779835906132957 68387169109417438464799859)
      ·
        refine ⟨102580753664126157697199789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68387169109417438464799859 102580753664126157697199789)
        ·
          refine ⟨38467782624047309136449921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102580753664126157697199789 38467782624047309136449921)
          ·
            refine ⟨28850836968035481852337441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38467782624047309136449921 28850836968035481852337441)
            ·
              refine ⟨21638127726026611389253081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28850836968035481852337441 21638127726026611389253081)
              ·
                refine ⟨16228595794519958541939811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21638127726026611389253081 16228595794519958541939811)
                ·
                  refine ⟨24342893691779937812909717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16228595794519958541939811 24342893691779937812909717)
                  ·
                    refine ⟨1141073141802184584980143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24342893691779937812909717 1141073141802184584980143)
                    ·
                      rfl

theorem cell23_6666696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_6666696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666696 prefixEnd_6666696 := by exact prefixLift 6666696
  have htrace : WordTrace (prefixWord ++ tailWord_6666696) baseStart_6666696 baseEnd_6666696 := by
    simpa [prefixWord, tailWord_6666696, baseEnd_6666696] using wordTrace_append hprefix tailTrace_6666696
  have hstable : (prefixWord ++ tailWord_6666696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666696).length < 2 ^ (prefixWord ++ tailWord_6666696).sum := by decide
  have hdescent : baseEnd_6666696 < baseStart_6666696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666699 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_6666699 : Nat := 118140960795 + 6666699 * 2 ^ 59
def prefixEnd_6666699 : Nat := 4983230072969 + 3 ^ 40 * 6666699 * 2
def baseEnd_6666699 : Nat := 3423220965848517243202915

theorem tailTrace_6666699 : CollatzResearch.WordTrace tailWord_6666699 prefixEnd_6666699 3423220965848517243202915 := by
  unfold tailWord_6666699
  simp only [CollatzResearch.WordTrace]
  refine ⟨243154488474695579387203151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162102992316463719591468767 243154488474695579387203151)
  ·
    refine ⟨364731732712043369080804727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243154488474695579387203151 364731732712043369080804727)
    ·
      refine ⟨547097599068065053621207091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364731732712043369080804727 547097599068065053621207091)
      ·
        refine ⟨820646398602097580431810637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547097599068065053621207091 820646398602097580431810637)
        ·
          refine ⟨307742399475786592661928989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 820646398602097580431810637 307742399475786592661928989)
          ·
            refine ⟨115403399803419972248223371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307742399475786592661928989 115403399803419972248223371)
            ·
              refine ⟨173105099705129958372335057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115403399803419972248223371 173105099705129958372335057)
              ·
                refine ⟨129828824778847468779251293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173105099705129958372335057 129828824778847468779251293)
                ·
                  refine ⟨48685809292067800792219235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129828824778847468779251293 48685809292067800792219235)
                  ·
                    refine ⟨73028713938101701188328853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48685809292067800792219235 73028713938101701188328853)
                    ·
                      refine ⟨3423220965848517243202915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73028713938101701188328853 3423220965848517243202915)
                      ·
                        rfl

theorem cell23_6666699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_6666699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666699 prefixEnd_6666699 := by exact prefixLift 6666699
  have htrace : WordTrace (prefixWord ++ tailWord_6666699) baseStart_6666699 baseEnd_6666699 := by
    simpa [prefixWord, tailWord_6666699, baseEnd_6666699] using wordTrace_append hprefix tailTrace_6666699
  have hstable : (prefixWord ++ tailWord_6666699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666699).length < 2 ^ (prefixWord ++ tailWord_6666699).sum := by decide
  have hdescent : baseEnd_6666699 < baseStart_6666699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666703 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 7, 2, 2]
def baseStart_6666703 : Nat := 118140960795 + 6666703 * 2 ^ 59
def prefixEnd_6666703 : Nat := 4983230072969 + 3 ^ 40 * 6666703 * 2
def baseEnd_6666703 : Nat := 3423223019771135227552897

theorem tailTrace_6666703 : CollatzResearch.WordTrace tailWord_6666703 prefixEnd_6666703 3423223019771135227552897 := by
  unfold tailWord_6666703
  simp only [CollatzResearch.WordTrace]
  refine ⟨243154634366681088070348763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162103089577787392046899175 243154634366681088070348763)
  ·
    refine ⟨364731951550021632105523145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243154634366681088070348763 364731951550021632105523145)
    ·
      refine ⟨273548963662516224079142359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364731951550021632105523145 273548963662516224079142359)
      ·
        refine ⟨410323445493774336118713539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273548963662516224079142359 410323445493774336118713539)
        ·
          refine ⟨615485168240661504178070309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410323445493774336118713539 615485168240661504178070309)
          ·
            refine ⟨115403469045124032033388183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 615485168240661504178070309 115403469045124032033388183)
            ·
              refine ⟨173105203567686048050082275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115403469045124032033388183 173105203567686048050082275)
              ·
                refine ⟨259657805351529072075123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173105203567686048050082275 259657805351529072075123413)
                ·
                  refine ⟨6085729812926462626760705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259657805351529072075123413 6085729812926462626760705)
                  ·
                    refine ⟨4564297359694846970070529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6085729812926462626760705 4564297359694846970070529)
                    ·
                      refine ⟨3423223019771135227552897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564297359694846970070529 3423223019771135227552897)
                      ·
                        rfl

theorem cell23_6666703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 2, 2].length) (baseStart_6666703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666703 prefixEnd_6666703 := by exact prefixLift 6666703
  have htrace : WordTrace (prefixWord ++ tailWord_6666703) baseStart_6666703 baseEnd_6666703 := by
    simpa [prefixWord, tailWord_6666703, baseEnd_6666703] using wordTrace_append hprefix tailTrace_6666703
  have hstable : (prefixWord ++ tailWord_6666703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666703).length < 2 ^ (prefixWord ++ tailWord_6666703).sum := by decide
  have hdescent : baseEnd_6666703 < baseStart_6666703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666720 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 3, 2, 2]
def baseStart_6666720 : Nat := 118140960795 + 6666720 * 2 ^ 59
def prefixEnd_6666720 : Nat := 4983230072969 + 3 ^ 40 * 6666720 * 2
def baseEnd_6666720 : Nat := 3423231748942261661040319

theorem tailTrace_6666720 : CollatzResearch.WordTrace tailWord_6666720 prefixEnd_6666720 3423231748942261661040319 := by
  unfold tailWord_6666720
  simp only [CollatzResearch.WordTrace]
  refine ⟨121577627203809749986858807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162103502938412999982478409 121577627203809749986858807)
  ·
    refine ⟨182366440805714624980288211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121577627203809749986858807 182366440805714624980288211)
    ·
      refine ⟨273549661208571937470432317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182366440805714624980288211 273549661208571937470432317)
      ·
        refine ⟨102581122953214476551412119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273549661208571937470432317 102581122953214476551412119)
        ·
          refine ⟨153871684429821714827118179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102581122953214476551412119 153871684429821714827118179)
          ·
            refine ⟨230807526644732572240677269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153871684429821714827118179 230807526644732572240677269)
            ·
              refine ⟨10819102811471839323781747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 230807526644732572240677269 10819102811471839323781747)
              ·
                refine ⟨16228654217207758985672621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10819102811471839323781747 16228654217207758985672621)
                ·
                  refine ⟨6085745331452909619627233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16228654217207758985672621 6085745331452909619627233)
                  ·
                    refine ⟨4564308998589682214720425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6085745331452909619627233 4564308998589682214720425)
                    ·
                      refine ⟨3423231748942261661040319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564308998589682214720425 3423231748942261661040319)
                      ·
                        rfl

theorem cell23_6666720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_6666720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666720 prefixEnd_6666720 := by exact prefixLift 6666720
  have htrace : WordTrace (prefixWord ++ tailWord_6666720) baseStart_6666720 baseEnd_6666720 := by
    simpa [prefixWord, tailWord_6666720, baseEnd_6666720] using wordTrace_append hprefix tailTrace_6666720
  have hstable : (prefixWord ++ tailWord_6666720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666720).length < 2 ^ (prefixWord ++ tailWord_6666720).sum := by decide
  have hdescent : baseEnd_6666720 < baseStart_6666720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666723 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6666723 : Nat := 118140960795 + 6666723 * 2 ^ 59
def prefixEnd_6666723 : Nat := 4983230072969 + 3 ^ 40 * 6666723 * 2
def baseEnd_6666723 : Nat := 3423233289384225149302805

theorem tailTrace_6666723 : CollatzResearch.WordTrace tailWord_6666723 prefixEnd_6666723 3423233289384225149302805 := by
  unfold tailWord_6666723
  simp only [CollatzResearch.WordTrace]
  refine ⟨243155363826608631486076823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162103575884405754324051215 243155363826608631486076823)
  ·
    refine ⟨364733045739912947229115235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243155363826608631486076823 364733045739912947229115235)
    ·
      refine ⟨547099568609869420843672853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364733045739912947229115235 547099568609869420843672853)
      ·
        refine ⟨25645292278587629102047165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 547099568609869420843672853 25645292278587629102047165)
        ·
          refine ⟨9616984604470360913267687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25645292278587629102047165 9616984604470360913267687)
          ·
            refine ⟨14425476906705541369901531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616984604470360913267687 14425476906705541369901531)
            ·
              refine ⟨21638215360058312054852297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14425476906705541369901531 21638215360058312054852297)
              ·
                refine ⟨16228661520043734041139223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21638215360058312054852297 16228661520043734041139223)
                ·
                  refine ⟨24342992280065601061708835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16228661520043734041139223 24342992280065601061708835)
                  ·
                    refine ⟨36514488420098401592563253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24342992280065601061708835 36514488420098401592563253)
                    ·
                      refine ⟨3423233289384225149302805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36514488420098401592563253 3423233289384225149302805)
                      ·
                        rfl

theorem cell23_6666723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6666723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666723 prefixEnd_6666723 := by exact prefixLift 6666723
  have htrace : WordTrace (prefixWord ++ tailWord_6666723) baseStart_6666723 baseEnd_6666723 := by
    simpa [prefixWord, tailWord_6666723, baseEnd_6666723] using wordTrace_append hprefix tailTrace_6666723
  have hstable : (prefixWord ++ tailWord_6666723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666723).length < 2 ^ (prefixWord ++ tailWord_6666723).sum := by decide
  have hdescent : baseEnd_6666723 < baseStart_6666723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666729 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_6666729 : Nat := 118140960795 + 6666729 * 2 ^ 59
def prefixEnd_6666729 : Nat := 4983230072969 + 3 ^ 40 * 6666729 * 2
def baseEnd_6666729 : Nat := 3423236370268152125827777

theorem tailTrace_6666729 : CollatzResearch.WordTrace tailWord_6666729 prefixEnd_6666729 3423236370268152125827777 := by
  unfold tailWord_6666729
  simp only [CollatzResearch.WordTrace]
  refine ⟨243155582664586894510795241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162103721776391263007196827 243155582664586894510795241)
  ·
    refine ⟨182366686998440170883096431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243155582664586894510795241 182366686998440170883096431)
    ·
      refine ⟨273550030497660256324644647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182366686998440170883096431 273550030497660256324644647)
      ·
        refine ⟨410325045746490384486966971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273550030497660256324644647 410325045746490384486966971)
        ·
          refine ⟨615487568619735576730450457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410325045746490384486966971 615487568619735576730450457)
          ·
            refine ⟨461615676464801682547837843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615487568619735576730450457 461615676464801682547837843)
            ·
              refine ⟨692423514697202523821756765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461615676464801682547837843 692423514697202523821756765)
              ·
                refine ⟨259658818011450946433158787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692423514697202523821756765 259658818011450946433158787)
                ·
                  refine ⟨389488227017176419649738181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259658818011450946433158787 389488227017176419649738181)
                  ·
                    refine ⟨73029042565720578684325909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 389488227017176419649738181 73029042565720578684325909)
                    ·
                      refine ⟨3423236370268152125827777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73029042565720578684325909 3423236370268152125827777)
                      ·
                        rfl

theorem cell23_6666729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_6666729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666729 prefixEnd_6666729 := by exact prefixLift 6666729
  have htrace : WordTrace (prefixWord ++ tailWord_6666729) baseStart_6666729 baseEnd_6666729 := by
    simpa [prefixWord, tailWord_6666729, baseEnd_6666729] using wordTrace_append hprefix tailTrace_6666729
  have hstable : (prefixWord ++ tailWord_6666729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666729).length < 2 ^ (prefixWord ++ tailWord_6666729).sum := by decide
  have hdescent : baseEnd_6666729 < baseStart_6666729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666733 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6666733 : Nat := 118140960795 + 6666733 * 2 ^ 59
def prefixEnd_6666733 : Nat := 4983230072969 + 3 ^ 40 * 6666733 * 2
def baseEnd_6666733 : Nat := 3423238424190770110177759

theorem tailTrace_6666733 : CollatzResearch.WordTrace tailWord_6666733 prefixEnd_6666733 3423238424190770110177759 := by
  unfold tailWord_6666733
  simp only [CollatzResearch.WordTrace]
  refine ⟨243155728556572403193940853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162103819037714935462627235 243155728556572403193940853)
  ·
    refine ⟨22795849552178662799431955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243155728556572403193940853 22795849552178662799431955)
    ·
      refine ⟨34193774328267994199147933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22795849552178662799431955 34193774328267994199147933)
      ·
        refine ⟨12822665373100497824680475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34193774328267994199147933 12822665373100497824680475)
        ·
          refine ⟨19233998059650746737020713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822665373100497824680475 19233998059650746737020713)
          ·
            refine ⟨14425498544738060052765535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19233998059650746737020713 14425498544738060052765535)
            ·
              refine ⟨21638247817107090079148303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14425498544738060052765535 21638247817107090079148303)
              ·
                refine ⟨32457371725660635118722455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21638247817107090079148303 32457371725660635118722455)
                ·
                  refine ⟨48686057588490952678083683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32457371725660635118722455 48686057588490952678083683)
                  ·
                    refine ⟨73029086382736429017125525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48686057588490952678083683 73029086382736429017125525)
                    ·
                      refine ⟨3423238424190770110177759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73029086382736429017125525 3423238424190770110177759)
                      ·
                        rfl

theorem cell23_6666733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6666733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666733 prefixEnd_6666733 := by exact prefixLift 6666733
  have htrace : WordTrace (prefixWord ++ tailWord_6666733) baseStart_6666733 baseEnd_6666733 := by
    simpa [prefixWord, tailWord_6666733, baseEnd_6666733] using wordTrace_append hprefix tailTrace_6666733
  have hstable : (prefixWord ++ tailWord_6666733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666733).length < 2 ^ (prefixWord ++ tailWord_6666733).sum := by decide
  have hdescent : baseEnd_6666733 < baseStart_6666733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666786 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_6666786 : Nat := 118140960795 + 6666786 * 2 ^ 59
def prefixEnd_6666786 : Nat := 4983230072969 + 3 ^ 40 * 6666786 * 2
def baseEnd_6666786 : Nat := 1141088546221819467605005

theorem tailTrace_6666786 : CollatzResearch.WordTrace tailWord_6666786 prefixEnd_6666786 1141088546221819467605005 := by
  unfold tailWord_6666786
  simp only [CollatzResearch.WordTrace]
  refine ⟨60789415406345098311405053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162105107750253595497080141 60789415406345098311405053)
  ·
    refine ⟨22796030777379411866776895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60789415406345098311405053 22796030777379411866776895)
    ·
      refine ⟨34194046166069117800165343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22796030777379411866776895 34194046166069117800165343)
      ·
        refine ⟨51291069249103676700248015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34194046166069117800165343 51291069249103676700248015)
        ·
          refine ⟨76936603873655515050372023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51291069249103676700248015 76936603873655515050372023)
          ·
            refine ⟨115404905810483272575558035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76936603873655515050372023 115404905810483272575558035)
            ·
              refine ⟨173107358715724908863337053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115404905810483272575558035 173107358715724908863337053)
              ·
                refine ⟨64915259518396840823751395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173107358715724908863337053 64915259518396840823751395)
                ·
                  refine ⟨97372889277595261235627093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64915259518396840823751395 97372889277595261235627093)
                  ·
                    refine ⟨1141088546221819467605005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97372889277595261235627093 1141088546221819467605005)
                    ·
                      rfl

theorem cell23_6666786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_6666786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666786 prefixEnd_6666786 := by exact prefixLift 6666786
  have htrace : WordTrace (prefixWord ++ tailWord_6666786) baseStart_6666786 baseEnd_6666786 := by
    simpa [prefixWord, tailWord_6666786, baseEnd_6666786] using wordTrace_append hprefix tailTrace_6666786
  have hstable : (prefixWord ++ tailWord_6666786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666786).length < 2 ^ (prefixWord ++ tailWord_6666786).sum := by decide
  have hdescent : baseEnd_6666786 < baseStart_6666786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666787 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 2, 1, 3]
def baseStart_6666787 : Nat := 118140960795 + 6666787 * 2 ^ 59
def prefixEnd_6666787 : Nat := 4983230072969 + 3 ^ 40 * 6666787 * 2
def baseEnd_6666787 : Nat := 3423266152146112898902511

theorem tailTrace_6666787 : CollatzResearch.WordTrace tailWord_6666787 prefixEnd_6666787 3423266152146112898902511 := by
  unfold tailWord_6666787
  simp only [CollatzResearch.WordTrace]
  refine ⟨243157698098376770416406615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162105132065584513610937743 243157698098376770416406615)
  ·
    refine ⟨364736547147565155624609923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243157698098376770416406615 364736547147565155624609923)
    ·
      refine ⟨547104820721347733436914885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364736547147565155624609923 547104820721347733436914885)
      ·
        refine ⟨102582153885252700019421541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 547104820721347733436914885 102582153885252700019421541)
        ·
          refine ⟨19234153853484881253641539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102582153885252700019421541 19234153853484881253641539)
          ·
            refine ⟨28851230780227321880462309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19234153853484881253641539 28851230780227321880462309)
            ·
              refine ⟨5409605771292622852586683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28851230780227321880462309 5409605771292622852586683)
              ·
                refine ⟨8114408656938934278880025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409605771292622852586683 8114408656938934278880025)
                ·
                  refine ⟨6085806492704200709160019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8114408656938934278880025 6085806492704200709160019)
                  ·
                    refine ⟨9128709739056301063740029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6085806492704200709160019 9128709739056301063740029)
                    ·
                      refine ⟨3423266152146112898902511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9128709739056301063740029 3423266152146112898902511)
                      ·
                        rfl

theorem cell23_6666787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_6666787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666787 prefixEnd_6666787 := by exact prefixLift 6666787
  have htrace : WordTrace (prefixWord ++ tailWord_6666787) baseStart_6666787 baseEnd_6666787 := by
    simpa [prefixWord, tailWord_6666787, baseEnd_6666787] using wordTrace_append hprefix tailTrace_6666787
  have hstable : (prefixWord ++ tailWord_6666787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666787).length < 2 ^ (prefixWord ++ tailWord_6666787).sum := by decide
  have hdescent : baseEnd_6666787 < baseStart_6666787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666791 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6666791 : Nat := 118140960795 + 6666791 * 2 ^ 59
def prefixEnd_6666791 : Nat := 4983230072969 + 3 ^ 40 * 6666791 * 2
def baseEnd_6666791 : Nat := 3423268206068730883252493

theorem tailTrace_6666791 : CollatzResearch.WordTrace tailWord_6666791 prefixEnd_6666791 3423268206068730883252493 := by
  unfold tailWord_6666791
  simp only [CollatzResearch.WordTrace]
  refine ⟨243157843990362279099552227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162105229326908186066368151 243157843990362279099552227)
  ·
    refine ⟨364736765985543418649328341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243157843990362279099552227 364736765985543418649328341)
    ·
      refine ⟨8548517952786173874593633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 364736765985543418649328341 8548517952786173874593633)
      ·
        refine ⟨6411388464589630405945225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8548517952786173874593633 6411388464589630405945225)
        ·
          refine ⟨4808541348442222804458919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6411388464589630405945225 4808541348442222804458919)
          ·
            refine ⟨7212812022663334206688379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808541348442222804458919 7212812022663334206688379)
            ·
              refine ⟨10819218033995001310032569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7212812022663334206688379 10819218033995001310032569)
              ·
                refine ⟨8114413525496250982524427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10819218033995001310032569 8114413525496250982524427)
                ·
                  refine ⟨12171620288244376473786641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8114413525496250982524427 12171620288244376473786641)
                  ·
                    refine ⟨9128715216183282355339981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12171620288244376473786641 9128715216183282355339981)
                    ·
                      refine ⟨3423268206068730883252493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9128715216183282355339981 3423268206068730883252493)
                      ·
                        rfl

theorem cell23_6666791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6666791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666791 prefixEnd_6666791 := by exact prefixLift 6666791
  have htrace : WordTrace (prefixWord ++ tailWord_6666791) baseStart_6666791 baseEnd_6666791 := by
    simpa [prefixWord, tailWord_6666791, baseEnd_6666791] using wordTrace_append hprefix tailTrace_6666791
  have hstable : (prefixWord ++ tailWord_6666791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666791).length < 2 ^ (prefixWord ++ tailWord_6666791).sum := by decide
  have hdescent : baseEnd_6666791 < baseStart_6666791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666810 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2]
def baseStart_6666810 : Nat := 118140960795 + 6666810 * 2 ^ 59
def prefixEnd_6666810 : Nat := 4983230072969 + 3 ^ 40 * 6666810 * 2
def baseEnd_6666810 : Nat := 3423277962201166308914905

theorem tailTrace_6666810 : CollatzResearch.WordTrace tailWord_6666810 prefixEnd_6666810 3423277962201166308914905 := by
  unfold tailWord_6666810
  simp only [CollatzResearch.WordTrace]
  refine ⟨60789634244323361336123471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162105691318195630229662589 60789634244323361336123471)
  ·
    refine ⟨91184451366485042004185207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60789634244323361336123471 91184451366485042004185207)
    ·
      refine ⟨136776677049727563006277811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91184451366485042004185207 136776677049727563006277811)
      ·
        refine ⟨205165015574591344509416717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136776677049727563006277811 205165015574591344509416717)
        ·
          refine ⟨76936880840471754191031269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205165015574591344509416717 76936880840471754191031269)
          ·
            refine ⟨14425665157588453910818363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76936880840471754191031269 14425665157588453910818363)
            ·
              refine ⟨21638497736382680866227545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14425665157588453910818363 21638497736382680866227545)
              ·
                refine ⟨16228873302287010649670659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21638497736382680866227545 16228873302287010649670659)
                ·
                  refine ⟨24343309953430515974505989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16228873302287010649670659 24343309953430515974505989)
                  ·
                    refine ⟨4564370616268221745219873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24343309953430515974505989 4564370616268221745219873)
                    ·
                      refine ⟨3423277962201166308914905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564370616268221745219873 3423277962201166308914905)
                      ·
                        rfl

theorem cell23_6666810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_6666810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666810 prefixEnd_6666810 := by exact prefixLift 6666810
  have htrace : WordTrace (prefixWord ++ tailWord_6666810) baseStart_6666810 baseEnd_6666810 := by
    simpa [prefixWord, tailWord_6666810, baseEnd_6666810] using wordTrace_append hprefix tailTrace_6666810
  have hstable : (prefixWord ++ tailWord_6666810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666810).length < 2 ^ (prefixWord ++ tailWord_6666810).sum := by decide
  have hdescent : baseEnd_6666810 < baseStart_6666810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666813 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_6666813 : Nat := 118140960795 + 6666813 * 2 ^ 59
def prefixEnd_6666813 : Nat := 4983230072969 + 3 ^ 40 * 6666813 * 2
def baseEnd_6666813 : Nat := 3423279502643129797177391

theorem tailTrace_6666813 : CollatzResearch.WordTrace tailWord_6666813 prefixEnd_6666813 3423279502643129797177391 := by
  unfold tailWord_6666813
  simp only [CollatzResearch.WordTrace]
  refine ⟨243158646396282576856853093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162105764264188384571235395 243158646396282576856853093)
  ·
    refine ⟨45592246199302983160659955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243158646396282576856853093 45592246199302983160659955)
    ·
      refine ⟨68388369298954474740989933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45592246199302983160659955 68388369298954474740989933)
      ·
        refine ⟨25645638487107928027871225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68388369298954474740989933 25645638487107928027871225)
        ·
          refine ⟨19234228865330946020903419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25645638487107928027871225 19234228865330946020903419)
          ·
            refine ⟨28851343297996419031355129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19234228865330946020903419 28851343297996419031355129)
            ·
              refine ⟨21638507473497314273516347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28851343297996419031355129 21638507473497314273516347)
              ·
                refine ⟨32457761210245971410274521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21638507473497314273516347 32457761210245971410274521)
                ·
                  refine ⟨24343320907684478557705891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32457761210245971410274521 24343320907684478557705891)
                  ·
                    refine ⟨36514981361526717836558837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24343320907684478557705891 36514981361526717836558837)
                    ·
                      refine ⟨3423279502643129797177391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36514981361526717836558837 3423279502643129797177391)
                      ·
                        rfl

theorem cell23_6666813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_6666813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666813 prefixEnd_6666813 := by exact prefixLift 6666813
  have htrace : WordTrace (prefixWord ++ tailWord_6666813) baseStart_6666813 baseEnd_6666813 := by
    simpa [prefixWord, tailWord_6666813, baseEnd_6666813] using wordTrace_append hprefix tailTrace_6666813
  have hstable : (prefixWord ++ tailWord_6666813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666813).length < 2 ^ (prefixWord ++ tailWord_6666813).sum := by decide
  have hdescent : baseEnd_6666813 < baseStart_6666813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666863 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 2, 5]
def baseStart_6666863 : Nat := 118140960795 + 6666863 * 2 ^ 59
def prefixEnd_6666863 : Nat := 4983230072969 + 3 ^ 40 * 6666863 * 2
def baseEnd_6666863 : Nat := 1141101725558618200517387

theorem tailTrace_6666863 : CollatzResearch.WordTrace tailWord_6666863 prefixEnd_6666863 1141101725558618200517387 := by
  unfold tailWord_6666863
  simp only [CollatzResearch.WordTrace]
  refine ⟨243160470046101435396173243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162106980030734290264115495 243160470046101435396173243)
  ·
    refine ⟨364740705069152153094259865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243160470046101435396173243 364740705069152153094259865)
    ·
      refine ⟨273555528801864114820694899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364740705069152153094259865 273555528801864114820694899)
      ·
        refine ⟨410333293202796172231042349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273555528801864114820694899 410333293202796172231042349)
        ·
          refine ⟨153874984951048564586640881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410333293202796172231042349 153874984951048564586640881)
          ·
            refine ⟨115406238713286423439980661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153874984951048564586640881 115406238713286423439980661)
            ·
              refine ⟨10819334879370602197498187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115406238713286423439980661 10819334879370602197498187)
              ·
                refine ⟨16229002319055903296247281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10819334879370602197498187 16229002319055903296247281)
                ·
                  refine ⟨12171751739291927472185461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16229002319055903296247281 12171751739291927472185461)
                  ·
                    refine ⟨1141101725558618200517387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12171751739291927472185461 1141101725558618200517387)
                    ·
                      rfl

theorem cell23_6666863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_6666863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666863 prefixEnd_6666863 := by exact prefixLift 6666863
  have htrace : WordTrace (prefixWord ++ tailWord_6666863) baseStart_6666863 baseEnd_6666863 := by
    simpa [prefixWord, tailWord_6666863, baseEnd_6666863] using wordTrace_append hprefix tailTrace_6666863
  have hstable : (prefixWord ++ tailWord_6666863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666863).length < 2 ^ (prefixWord ++ tailWord_6666863).sum := by decide
  have hdescent : baseEnd_6666863 < baseStart_6666863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666883 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 4]
def baseStart_6666883 : Nat := 118140960795 + 6666883 * 2 ^ 59
def prefixEnd_6666883 : Nat := 4983230072969 + 3 ^ 40 * 6666883 * 2
def baseEnd_6666883 : Nat := 3423315446288944523302069

theorem tailTrace_6666883 : CollatzResearch.WordTrace tailWord_6666883 prefixEnd_6666883 3423315446288944523302069 := by
  unfold tailWord_6666883
  simp only [CollatzResearch.WordTrace]
  refine ⟨243161199506028978811901303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162107466337352652541267535 243161199506028978811901303)
  ·
    refine ⟨364741799259043468217851955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243161199506028978811901303 364741799259043468217851955)
    ·
      refine ⟨547112698888565202326777933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364741799259043468217851955 547112698888565202326777933)
      ·
        refine ⟨205167262083211950872541725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547112698888565202326777933 205167262083211950872541725)
        ·
          refine ⟨76937723281204481577203147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205167262083211950872541725 76937723281204481577203147)
          ·
            refine ⟨115406584921806722365804721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76937723281204481577203147 115406584921806722365804721)
            ·
              refine ⟨86554938691355041774353541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115406584921806722365804721 86554938691355041774353541)
              ·
                refine ⟨16229051004629070332691289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86554938691355041774353541 16229051004629070332691289)
                ·
                  refine ⟨12171788253471802749518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16229051004629070332691289 12171788253471802749518467)
                  ·
                    refine ⟨18257682380207704124277701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12171788253471802749518467 18257682380207704124277701)
                    ·
                      refine ⟨3423315446288944523302069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18257682380207704124277701 3423315446288944523302069)
                      ·
                        rfl

theorem cell23_6666883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_6666883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666883 prefixEnd_6666883 := by exact prefixLift 6666883
  have htrace : WordTrace (prefixWord ++ tailWord_6666883) baseStart_6666883 baseEnd_6666883 := by
    simpa [prefixWord, tailWord_6666883, baseEnd_6666883] using wordTrace_append hprefix tailTrace_6666883
  have hstable : (prefixWord ++ tailWord_6666883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666883).length < 2 ^ (prefixWord ++ tailWord_6666883).sum := by decide
  have hdescent : baseEnd_6666883 < baseStart_6666883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666900 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6666900 : Nat := 118140960795 + 6666900 * 2 ^ 59
def prefixEnd_6666900 : Nat := 4983230072969 + 3 ^ 40 * 6666900 * 2
def baseEnd_6666900 : Nat := 3423324175460070956789491

theorem tailTrace_6666900 : CollatzResearch.WordTrace tailWord_6666900 prefixEnd_6666900 3423324175460070956789491 := by
  unfold tailWord_6666900
  simp only [CollatzResearch.WordTrace]
  refine ⟨121580909773483695357635077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162107879697978260476846769 121580909773483695357635077)
  ·
    refine ⟨22796420582528192879556577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121580909773483695357635077 22796420582528192879556577)
    ·
      refine ⟨17097315436896144659667433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22796420582528192879556577 17097315436896144659667433)
      ·
        refine ⟨12822986577672108494750575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17097315436896144659667433 12822986577672108494750575)
        ·
          refine ⟨19234479866508162742125863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822986577672108494750575 19234479866508162742125863)
          ·
            refine ⟨28851719799762244113188795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19234479866508162742125863 28851719799762244113188795)
            ·
              refine ⟨43277579699643366169783193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28851719799762244113188795 43277579699643366169783193)
              ·
                refine ⟨32458184774732524627337395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43277579699643366169783193 32458184774732524627337395)
                ·
                  refine ⟨48687277162098786941006093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32458184774732524627337395 48687277162098786941006093)
                  ·
                    refine ⟨18257728935787045102877285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48687277162098786941006093 18257728935787045102877285)
                    ·
                      refine ⟨3423324175460070956789491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18257728935787045102877285 3423324175460070956789491)
                      ·
                        rfl

theorem cell23_6666900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6666900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666900 prefixEnd_6666900 := by exact prefixLift 6666900
  have htrace : WordTrace (prefixWord ++ tailWord_6666900) baseStart_6666900 baseEnd_6666900 := by
    simpa [prefixWord, tailWord_6666900, baseEnd_6666900] using wordTrace_append hprefix tailTrace_6666900
  have hstable : (prefixWord ++ tailWord_6666900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666900).length < 2 ^ (prefixWord ++ tailWord_6666900).sum := by decide
  have hdescent : baseEnd_6666900 < baseStart_6666900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666903 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_6666903 : Nat := 118140960795 + 6666903 * 2 ^ 59
def prefixEnd_6666903 : Nat := 4983230072969 + 3 ^ 40 * 6666903 * 2
def baseEnd_6666903 : Nat := 3423325715902034445051977

theorem tailTrace_6666903 : CollatzResearch.WordTrace tailWord_6666903 prefixEnd_6666903 3423325715902034445051977 := by
  unfold tailWord_6666903
  simp only [CollatzResearch.WordTrace]
  refine ⟨243161928965956522227629363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162107952643971014818419575 243161928965956522227629363)
  ·
    refine ⟨364742893448934783341444045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243161928965956522227629363 364742893448934783341444045)
    ·
      refine ⟨136778585043350543753041517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364742893448934783341444045 136778585043350543753041517)
      ·
        refine ⟨51291969391256453907390569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136778585043350543753041517 51291969391256453907390569)
        ·
          refine ⟨38468977043442340430542927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51291969391256453907390569 38468977043442340430542927)
          ·
            refine ⟨57703465565163510645814391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38468977043442340430542927 57703465565163510645814391)
            ·
              refine ⟨86555198347745265968721587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57703465565163510645814391 86555198347745265968721587)
              ·
                refine ⟨129832797521617898953082381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86555198347745265968721587 129832797521617898953082381)
                ·
                  refine ⟨48687299070606712107405893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129832797521617898953082381 48687299070606712107405893)
                  ·
                    refine ⟨9128868575738758520138605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48687299070606712107405893 9128868575738758520138605)
                    ·
                      refine ⟨3423325715902034445051977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9128868575738758520138605 3423325715902034445051977)
                      ·
                        rfl

theorem cell23_6666903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_6666903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666903 prefixEnd_6666903 := by exact prefixLift 6666903
  have htrace : WordTrace (prefixWord ++ tailWord_6666903) baseStart_6666903 baseEnd_6666903 := by
    simpa [prefixWord, tailWord_6666903, baseEnd_6666903] using wordTrace_append hprefix tailTrace_6666903
  have hstable : (prefixWord ++ tailWord_6666903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666903).length < 2 ^ (prefixWord ++ tailWord_6666903).sum := by decide
  have hdescent : baseEnd_6666903 < baseStart_6666903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666927 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 1, 4]
def baseStart_6666927 : Nat := 118140960795 + 6666927 * 2 ^ 59
def prefixEnd_6666927 : Nat := 4983230072969 + 3 ^ 40 * 6666927 * 2
def baseEnd_6666927 : Nat := 1141112679812580783717289

theorem tailTrace_6666927 : CollatzResearch.WordTrace tailWord_6666927 prefixEnd_6666927 1141112679812580783717289 := by
  unfold tailWord_6666927
  simp only [CollatzResearch.WordTrace]
  refine ⟨243162804317869574326503035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162108536211913049551002023 243162804317869574326503035)
  ·
    refine ⟨364744206476804361489754553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243162804317869574326503035 364744206476804361489754553)
    ·
      refine ⟨273558154857603271117315915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364744206476804361489754553 273558154857603271117315915)
      ·
        refine ⟨410337232286404906675973873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273558154857603271117315915 410337232286404906675973873)
        ·
          refine ⟨307752924214803680006980405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410337232286404906675973873 307752924214803680006980405)
          ·
            refine ⟨28851836645137845000654413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307752924214803680006980405 28851836645137845000654413)
            ·
              refine ⟨10819438741926691875245405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28851836645137845000654413 10819438741926691875245405)
              ·
                refine ⟨4057289528222509453217027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10819438741926691875245405 4057289528222509453217027)
                ·
                  refine ⟨6085934292333764179825541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057289528222509453217027 6085934292333764179825541)
                  ·
                    refine ⟨1141112679812580783717289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6085934292333764179825541 1141112679812580783717289)
                    ·
                      rfl

theorem cell23_6666927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 4].length) (baseStart_6666927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666927 prefixEnd_6666927 := by exact prefixLift 6666927
  have htrace : WordTrace (prefixWord ++ tailWord_6666927) baseStart_6666927 baseEnd_6666927 := by
    simpa [prefixWord, tailWord_6666927, baseEnd_6666927] using wordTrace_append hprefix tailTrace_6666927
  have hstable : (prefixWord ++ tailWord_6666927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666927).length < 2 ^ (prefixWord ++ tailWord_6666927).sum := by decide
  have hdescent : baseEnd_6666927 < baseStart_6666927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666934 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6666934 : Nat := 118140960795 + 6666934 * 2 ^ 59
def prefixEnd_6666934 : Nat := 4983230072969 + 3 ^ 40 * 6666934 * 2
def baseEnd_6666934 : Nat := 3423341633802323823764335

theorem tailTrace_6666934 : CollatzResearch.WordTrace tailWord_6666934 prefixEnd_6666934 3423341633802323823764335 := by
  unfold tailWord_6666934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197691226802763407625491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162108706419229476348005237 15197691226802763407625491)
  ·
    refine ⟨22796536840204145111438237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15197691226802763407625491 22796536840204145111438237)
    ·
      refine ⟨8548701315076554416789339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22796536840204145111438237 8548701315076554416789339)
      ·
        refine ⟨12823051972614831625184009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8548701315076554416789339 12823051972614831625184009)
        ·
          refine ⟨9617288979461123718888007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12823051972614831625184009 9617288979461123718888007)
          ·
            refine ⟨14425933469191685578332011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617288979461123718888007 14425933469191685578332011)
            ·
              refine ⟨21638900203787528367498017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14425933469191685578332011 21638900203787528367498017)
              ·
                refine ⟨16229175152840646275623513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21638900203787528367498017 16229175152840646275623513)
                ·
                  refine ⟨12171881364630484706717635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16229175152840646275623513 12171881364630484706717635)
                  ·
                    refine ⟨18257822046945727060076453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12171881364630484706717635 18257822046945727060076453)
                    ·
                      refine ⟨3423341633802323823764335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18257822046945727060076453 3423341633802323823764335)
                      ·
                        rfl

theorem cell23_6666934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6666934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666934 prefixEnd_6666934 := by exact prefixLift 6666934
  have htrace : WordTrace (prefixWord ++ tailWord_6666934) baseStart_6666934 baseEnd_6666934 := by
    simpa [prefixWord, tailWord_6666934, baseEnd_6666934] using wordTrace_append hprefix tailTrace_6666934
  have hstable : (prefixWord ++ tailWord_6666934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666934).length < 2 ^ (prefixWord ++ tailWord_6666934).sum := by decide
  have hdescent : baseEnd_6666934 < baseStart_6666934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666944 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 1, 4]
def baseStart_6666944 : Nat := 118140960795 + 6666944 * 2 ^ 59
def prefixEnd_6666944 : Nat := 4983230072969 + 3 ^ 40 * 6666944 * 2
def baseEnd_6666944 : Nat := 1141115589536289594879763

theorem tailTrace_6666944 : CollatzResearch.WordTrace tailWord_6666944 prefixEnd_6666944 1141115589536289594879763 := by
  unfold tailWord_6666944
  simp only [CollatzResearch.WordTrace]
  refine ⟨121581712179403993114935943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162108949572538657486581257 121581712179403993114935943)
  ·
    refine ⟨182372568269105989672403915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121581712179403993114935943 182372568269105989672403915)
    ·
      refine ⟨273558852403658984508605873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182372568269105989672403915 273558852403658984508605873)
      ·
        refine ⟨205169139302744238381454405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273558852403658984508605873 205169139302744238381454405)
        ·
          refine ⟨38469213619264544696522701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205169139302744238381454405 38469213619264544696522701)
          ·
            refine ⟨14425955107224204261196013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38469213619264544696522701 14425955107224204261196013)
            ·
              refine ⟨5409733165209076597948505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14425955107224204261196013 5409733165209076597948505)
              ·
                refine ⟨4057299873906807448461379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409733165209076597948505 4057299873906807448461379)
                ·
                  refine ⟨6085949810860211172692069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057299873906807448461379 6085949810860211172692069)
                  ·
                    refine ⟨1141115589536289594879763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6085949810860211172692069 1141115589536289594879763)
                    ·
                      rfl

theorem cell23_6666944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 4].length) (baseStart_6666944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666944 prefixEnd_6666944 := by exact prefixLift 6666944
  have htrace : WordTrace (prefixWord ++ tailWord_6666944) baseStart_6666944 baseEnd_6666944 := by
    simpa [prefixWord, tailWord_6666944, baseEnd_6666944] using wordTrace_append hprefix tailTrace_6666944
  have hstable : (prefixWord ++ tailWord_6666944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666944).length < 2 ^ (prefixWord ++ tailWord_6666944).sum := by decide
  have hdescent : baseEnd_6666944 < baseStart_6666944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6666977 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_6666977 : Nat := 118140960795 + 6666977 * 2 ^ 59
def prefixEnd_6666977 : Nat := 4983230072969 + 3 ^ 40 * 6666977 * 2
def baseEnd_6666977 : Nat := 3423363713470467155526637

theorem tailTrace_6666977 : CollatzResearch.WordTrace tailWord_6666977 prefixEnd_6666977 3423363713470467155526637 := by
  unfold tailWord_6666977
  simp only [CollatzResearch.WordTrace]
  refine ⟨243164627967688432865823185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162109751978458955243882123 243164627967688432865823185)
  ·
    refine ⟨182373470975766324649367389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243164627967688432865823185 182373470975766324649367389)
    ·
      refine ⟨68390051615912371743512771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182373470975766324649367389 68390051615912371743512771)
      ·
        refine ⟨102585077423868557615269157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68390051615912371743512771 102585077423868557615269157)
        ·
          refine ⟨19234702016975354552862967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102585077423868557615269157 19234702016975354552862967)
          ·
            refine ⟨28852053025463031829294451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19234702016975354552862967 28852053025463031829294451)
            ·
              refine ⟨43278079538194547743941677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28852053025463031829294451 43278079538194547743941677)
              ·
                refine ⟨16229279826822955403978129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43278079538194547743941677 16229279826822955403978129)
                ·
                  refine ⟨12171959870117216552983597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16229279826822955403978129 12171959870117216552983597)
                  ·
                    refine ⟨4564484951293956207368849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12171959870117216552983597 4564484951293956207368849)
                    ·
                      refine ⟨3423363713470467155526637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564484951293956207368849 3423363713470467155526637)
                      ·
                        rfl

theorem cell23_6666977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_6666977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6666977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6666977 prefixEnd_6666977 := by exact prefixLift 6666977
  have htrace : WordTrace (prefixWord ++ tailWord_6666977) baseStart_6666977 baseEnd_6666977 := by
    simpa [prefixWord, tailWord_6666977, baseEnd_6666977] using wordTrace_append hprefix tailTrace_6666977
  have hstable : (prefixWord ++ tailWord_6666977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6666977).length < 2 ^ (prefixWord ++ tailWord_6666977).sum := by decide
  have hdescent : baseEnd_6666977 < baseStart_6666977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6666977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667007 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 3, 2, 2]
def baseStart_6667007 : Nat := 118140960795 + 6667007 * 2 ^ 59
def prefixEnd_6667007 : Nat := 4983230072969 + 3 ^ 40 * 6667007 * 2
def baseEnd_6667007 : Nat := 3423379117890102038151499

theorem tailTrace_6667007 : CollatzResearch.WordTrace tailWord_6667007 prefixEnd_6667007 3423379117890102038151499 := by
  unfold tailWord_6667007
  simp only [CollatzResearch.WordTrace]
  refine ⟨243165722157579747989415275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162110481438386498659610183 243165722157579747989415275)
  ·
    refine ⟨364748583236369621984122913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243165722157579747989415275 364748583236369621984122913)
    ·
      refine ⟨273561437427277216488092185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364748583236369621984122913 273561437427277216488092185)
      ·
        refine ⟨205171078070457912366069139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273561437427277216488092185 205171078070457912366069139)
        ·
          refine ⟨307756617105686868549103709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205171078070457912366069139 307756617105686868549103709)
          ·
            refine ⟨115408731414632575705913891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307756617105686868549103709 115408731414632575705913891)
            ·
              refine ⟨173113097121948863558870837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115408731414632575705913891 173113097121948863558870837)
              ·
                refine ⟨16229352855182705958644141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173113097121948863558870837 16229352855182705958644141)
                ·
                  refine ⟨6086007320693514734491553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16229352855182705958644141 6086007320693514734491553)
                  ·
                    refine ⟨4564505490520136050868665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6086007320693514734491553 4564505490520136050868665)
                    ·
                      refine ⟨3423379117890102038151499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564505490520136050868665 3423379117890102038151499)
                      ·
                        rfl

theorem cell23_6667007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_6667007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667007 prefixEnd_6667007 := by exact prefixLift 6667007
  have htrace : WordTrace (prefixWord ++ tailWord_6667007) baseStart_6667007 baseEnd_6667007 := by
    simpa [prefixWord, tailWord_6667007, baseEnd_6667007] using wordTrace_append hprefix tailTrace_6667007
  have hstable : (prefixWord ++ tailWord_6667007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667007).length < 2 ^ (prefixWord ++ tailWord_6667007).sum := by decide
  have hdescent : baseEnd_6667007 < baseStart_6667007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667041 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6667041 : Nat := 118140960795 + 6667041 * 2 ^ 59
def prefixEnd_6667041 : Nat := 4983230072969 + 3 ^ 40 * 6667041 * 2
def baseEnd_6667041 : Nat := 3423396576232354905126343

theorem tailTrace_6667041 : CollatzResearch.WordTrace tailWord_6667041 prefixEnd_6667041 3423396576232354905126343 := by
  unfold tailWord_6667041
  simp only [CollatzResearch.WordTrace]
  refine ⟨243166962239456571796152977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162111308159637714530768651 243166962239456571796152977)
  ·
    refine ⟨182375221679592428847114733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243166962239456571796152977 182375221679592428847114733)
    ·
      refine ⟨68390708129847160817668025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182375221679592428847114733 68390708129847160817668025)
      ·
        refine ⟨51293031097385370613251019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68390708129847160817668025 51293031097385370613251019)
        ·
          refine ⟨76939546646078055919876529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51293031097385370613251019 76939546646078055919876529)
          ·
            refine ⟨57704659984558541939907397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76939546646078055919876529 57704659984558541939907397)
            ·
              refine ⟨10819623747104726613732637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57704659984558541939907397 10819623747104726613732637)
              ·
                refine ⟨4057358905164272480149739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10819623747104726613732637 4057358905164272480149739)
                ·
                  refine ⟨6086038357746408720224609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057358905164272480149739 6086038357746408720224609)
                  ·
                    refine ⟨4564528768309806540168457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6086038357746408720224609 4564528768309806540168457)
                    ·
                      refine ⟨3423396576232354905126343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564528768309806540168457 3423396576232354905126343)
                      ·
                        rfl

theorem cell23_6667041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6667041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667041 prefixEnd_6667041 := by exact prefixLift 6667041
  have htrace : WordTrace (prefixWord ++ tailWord_6667041) baseStart_6667041 baseEnd_6667041 := by
    simpa [prefixWord, tailWord_6667041, baseEnd_6667041] using wordTrace_append hprefix tailTrace_6667041
  have hstable : (prefixWord ++ tailWord_6667041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667041).length < 2 ^ (prefixWord ++ tailWord_6667041).sum := by decide
  have hdescent : baseEnd_6667041 < baseStart_6667041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667044 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_6667044 : Nat := 118140960795 + 6667044 * 2 ^ 59
def prefixEnd_6667044 : Nat := 4983230072969 + 3 ^ 40 * 6667044 * 2
def baseEnd_6667044 : Nat := 3423398116674318393388829

theorem tailTrace_6667044 : CollatzResearch.WordTrace tailWord_6667044 prefixEnd_6667044 3423398116674318393388829 := by
  unfold tailWord_6667044
  simp only [CollatzResearch.WordTrace]
  refine ⟨121583535829222851654256093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162111381105630468872341457 121583535829222851654256093)
  ·
    refine ⟨45593825935958569370346035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121583535829222851654256093 45593825935958569370346035)
    ·
      refine ⟨68390738903937854055519053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45593825935958569370346035 68390738903937854055519053)
      ·
        refine ⟨25646527088976695270819645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68390738903937854055519053 25646527088976695270819645)
        ·
          refine ⟨9617447658366260726557367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25646527088976695270819645 9617447658366260726557367)
          ·
            refine ⟨14426171487549391089836051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617447658366260726557367 14426171487549391089836051)
            ·
              refine ⟨21639257231324086634754077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14426171487549391089836051 21639257231324086634754077)
              ·
                refine ⟨8114721461746532488032779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21639257231324086634754077 8114721461746532488032779)
                ·
                  refine ⟨12172082192619798732049169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8114721461746532488032779 12172082192619798732049169)
                  ·
                    refine ⟨9129061644464849049036877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12172082192619798732049169 9129061644464849049036877)
                    ·
                      refine ⟨3423398116674318393388829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129061644464849049036877 3423398116674318393388829)
                      ·
                        rfl

theorem cell23_6667044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_6667044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667044 prefixEnd_6667044 := by exact prefixLift 6667044
  have htrace : WordTrace (prefixWord ++ tailWord_6667044) baseStart_6667044 baseEnd_6667044 := by
    simpa [prefixWord, tailWord_6667044, baseEnd_6667044] using wordTrace_append hprefix tailTrace_6667044
  have hstable : (prefixWord ++ tailWord_6667044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667044).length < 2 ^ (prefixWord ++ tailWord_6667044).sum := by decide
  have hdescent : baseEnd_6667044 < baseStart_6667044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667057 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_6667057 : Nat := 118140960795 + 6667057 * 2 ^ 59
def prefixEnd_6667057 : Nat := 4983230072969 + 3 ^ 40 * 6667057 * 2
def baseEnd_6667057 : Nat := 3423404791922826842526269

theorem tailTrace_6667057 : CollatzResearch.WordTrace tailWord_6667057 prefixEnd_6667057 3423404791922826842526269 := by
  unfold tailWord_6667057
  simp only [CollatzResearch.WordTrace]
  refine ⟨243167545807398606528735425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162111697204932404352490283 243167545807398606528735425)
  ·
    refine ⟨182375659355548954896551569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243167545807398606528735425 182375659355548954896551569)
    ·
      refine ⟨136781744516661716172413677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182375659355548954896551569 136781744516661716172413677)
      ·
        refine ⟨51293154193748143564655129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136781744516661716172413677 51293154193748143564655129)
        ·
          refine ⟨38469865645311107673491347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51293154193748143564655129 38469865645311107673491347)
          ·
            refine ⟨57704798467966661510237021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38469865645311107673491347 57704798467966661510237021)
            ·
              refine ⟨21639299425487498066338883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57704798467966661510237021 21639299425487498066338883)
              ·
                refine ⟨32458949138231247099508325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21639299425487498066338883 32458949138231247099508325)
                ·
                  refine ⟨6086052963418358831157811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32458949138231247099508325 6086052963418358831157811)
                  ·
                    refine ⟨9129079445127538246736717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6086052963418358831157811 9129079445127538246736717)
                    ·
                      refine ⟨3423404791922826842526269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129079445127538246736717 3423404791922826842526269)
                      ·
                        rfl

theorem cell23_6667057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_6667057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667057 prefixEnd_6667057 := by exact prefixLift 6667057
  have htrace : WordTrace (prefixWord ++ tailWord_6667057) baseStart_6667057 baseEnd_6667057 := by
    simpa [prefixWord, tailWord_6667057, baseEnd_6667057] using wordTrace_append hprefix tailTrace_6667057
  have hstable : (prefixWord ++ tailWord_6667057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667057).length < 2 ^ (prefixWord ++ tailWord_6667057).sum := by decide
  have hdescent : baseEnd_6667057 < baseStart_6667057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667078 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6667078 : Nat := 118140960795 + 6667078 * 2 ^ 59
def prefixEnd_6667078 : Nat := 4983230072969 + 3 ^ 40 * 6667078 * 2
def baseEnd_6667078 : Nat := 3423415575016571260363673

theorem tailTrace_6667078 : CollatzResearch.WordTrace tailWord_6667078 prefixEnd_6667078 3423415575016571260363673 := by
  unfold tailWord_6667078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599009741885078972351559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162112207826881684743499925 7599009741885078972351559)
  ·
    refine ⟨11398514612827618458527339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599009741885078972351559 11398514612827618458527339)
    ·
      refine ⟨17097771919241427687791009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11398514612827618458527339 17097771919241427687791009)
      ·
        refine ⟨12823328939431070765843257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17097771919241427687791009 12823328939431070765843257)
        ·
          refine ⟨9617496704573303074382443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12823328939431070765843257 9617496704573303074382443)
          ·
            refine ⟨14426245056859954611573665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617496704573303074382443 14426245056859954611573665)
            ·
              refine ⟨10819683792644965958680249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14426245056859954611573665 10819683792644965958680249)
              ·
                refine ⟨8114762844483724469010187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10819683792644965958680249 8114762844483724469010187)
                ·
                  refine ⟨12172144266725586703515281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8114762844483724469010187 12172144266725586703515281)
                  ·
                    refine ⟨9129108200044190027636461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12172144266725586703515281 9129108200044190027636461)
                    ·
                      refine ⟨3423415575016571260363673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129108200044190027636461 3423415575016571260363673)
                      ·
                        rfl

theorem cell23_6667078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6667078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667078 prefixEnd_6667078 := by exact prefixLift 6667078
  have htrace : WordTrace (prefixWord ++ tailWord_6667078) baseStart_6667078 baseEnd_6667078 := by
    simpa [prefixWord, tailWord_6667078, baseEnd_6667078] using wordTrace_append hprefix tailTrace_6667078
  have hstable : (prefixWord ++ tailWord_6667078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667078).length < 2 ^ (prefixWord ++ tailWord_6667078).sum := by decide
  have hdescent : baseEnd_6667078 < baseStart_6667078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667083 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_6667083 : Nat := 118140960795 + 6667083 * 2 ^ 59
def prefixEnd_6667083 : Nat := 4983230072969 + 3 ^ 40 * 6667083 * 2
def baseEnd_6667083 : Nat := 3423418142419843740801149

theorem tailTrace_6667083 : CollatzResearch.WordTrace tailWord_6667083 prefixEnd_6667083 3423418142419843740801149 := by
  unfold tailWord_6667083
  simp only [CollatzResearch.WordTrace]
  refine ⟨243168494105304412969181903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162112329403536275312787935 243168494105304412969181903)
  ·
    refine ⟨364752741157956619453772855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243168494105304412969181903 364752741157956619453772855)
    ·
      refine ⟨547129111736934929180659283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364752741157956619453772855 547129111736934929180659283)
      ·
        refine ⟨820693667605402393770988925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547129111736934929180659283 820693667605402393770988925)
        ·
          refine ⟨307760125352025897664120847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 820693667605402393770988925 307760125352025897664120847)
          ·
            refine ⟨461640188028038846496181271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307760125352025897664120847 461640188028038846496181271)
            ·
              refine ⟨692460282042058269744271907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461640188028038846496181271 692460282042058269744271907)
              ·
                refine ⟨1038690423063087404616407861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692460282042058269744271907 1038690423063087404616407861)
                ·
                  refine ⟨97377227162164444182788237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038690423063087404616407861 97377227162164444182788237)
                  ·
                    refine ⟨36516460185811666568545589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97377227162164444182788237 36516460185811666568545589)
                    ·
                      refine ⟨3423418142419843740801149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36516460185811666568545589 3423418142419843740801149)
                      ·
                        rfl

theorem cell23_6667083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_6667083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667083 prefixEnd_6667083 := by exact prefixLift 6667083
  have htrace : WordTrace (prefixWord ++ tailWord_6667083) baseStart_6667083 baseEnd_6667083 := by
    simpa [prefixWord, tailWord_6667083, baseEnd_6667083] using wordTrace_append hprefix tailTrace_6667083
  have hstable : (prefixWord ++ tailWord_6667083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667083).length < 2 ^ (prefixWord ++ tailWord_6667083).sum := by decide
  have hdescent : baseEnd_6667083 < baseStart_6667083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667084 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 1, 3, 2]
def baseStart_6667084 : Nat := 118140960795 + 6667084 * 2 ^ 59
def prefixEnd_6667084 : Nat := 4983230072969 + 3 ^ 40 * 6667084 * 2
def baseEnd_6667084 : Nat := 3423418655900498236888645

theorem tailTrace_6667084 : CollatzResearch.WordTrace tailWord_6667084 prefixEnd_6667084 3423418655900498236888645 := by
  unfold tailWord_6667084
  simp only [CollatzResearch.WordTrace]
  refine ⟨121584265289150395069984153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162112353718867193426645537 121584265289150395069984153)
  ·
    refine ⟨91188198966862796302488115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121584265289150395069984153 91188198966862796302488115)
    ·
      refine ⟨136782298450294194453732173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91188198966862796302488115 136782298450294194453732173)
      ·
        refine ⟨51293361918860322920149565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136782298450294194453732173 51293361918860322920149565)
        ·
          refine ⟨19235010719572621095056087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51293361918860322920149565 19235010719572621095056087)
          ·
            refine ⟨28852516079358931642584131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19235010719572621095056087 28852516079358931642584131)
            ·
              refine ⟨43278774119038397463876197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28852516079358931642584131 43278774119038397463876197)
              ·
                refine ⟨8114770147319699524476787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43278774119038397463876197 8114770147319699524476787)
                ·
                  refine ⟨12172155220979549286715181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8114770147319699524476787 12172155220979549286715181)
                  ·
                    refine ⟨4564558207867330982518193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12172155220979549286715181 4564558207867330982518193)
                    ·
                      refine ⟨3423418655900498236888645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564558207867330982518193 3423418655900498236888645)
                      ·
                        rfl

theorem cell23_6667084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_6667084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667084 prefixEnd_6667084 := by exact prefixLift 6667084
  have htrace : WordTrace (prefixWord ++ tailWord_6667084) baseStart_6667084 baseEnd_6667084 := by
    simpa [prefixWord, tailWord_6667084, baseEnd_6667084] using wordTrace_append hprefix tailTrace_6667084
  have hstable : (prefixWord ++ tailWord_6667084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667084).length < 2 ^ (prefixWord ++ tailWord_6667084).sum := by decide
  have hdescent : baseEnd_6667084 < baseStart_6667084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667120 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 7]
def baseStart_6667120 : Nat := 118140960795 + 6667120 * 2 ^ 59
def prefixEnd_6667120 : Nat := 4983230072969 + 3 ^ 40 * 6667120 * 2
def baseEnd_6667120 : Nat := 380381904578228899559831

theorem tailTrace_6667120 : CollatzResearch.WordTrace tailWord_6667120 prefixEnd_6667120 380381904578228899559831 := by
  unfold tailWord_6667120
  simp only [CollatzResearch.WordTrace]
  refine ⟨121584921803085184144139407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162113229070780245525519209 121584921803085184144139407)
  ·
    refine ⟨182377382704627776216209111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121584921803085184144139407 182377382704627776216209111)
    ·
      refine ⟨273566074056941664324313667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182377382704627776216209111 273566074056941664324313667)
      ·
        refine ⟨410349111085412496486470501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273566074056941664324313667 410349111085412496486470501)
        ·
          refine ⟨76940458328514843091213219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410349111085412496486470501 76940458328514843091213219)
          ·
            refine ⟨115410687492772264636819829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76940458328514843091213219 115410687492772264636819829)
            ·
              refine ⟨10819751952447399809701859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115410687492772264636819829 10819751952447399809701859)
              ·
                refine ⟨16229627928671099714552789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10819751952447399809701859 16229627928671099714552789)
                ·
                  refine ⟨380381904578228899559831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16229627928671099714552789 380381904578228899559831)
                  ·
                    rfl

theorem cell23_6667120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_6667120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667120 prefixEnd_6667120 := by exact prefixLift 6667120
  have htrace : WordTrace (prefixWord ++ tailWord_6667120) baseStart_6667120 baseEnd_6667120 := by
    simpa [prefixWord, tailWord_6667120, baseEnd_6667120] using wordTrace_append hprefix tailTrace_6667120
  have hstable : (prefixWord ++ tailWord_6667120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667120).length < 2 ^ (prefixWord ++ tailWord_6667120).sum := by decide
  have hdescent : baseEnd_6667120 < baseStart_6667120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667130 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_6667130 : Nat := 118140960795 + 6667130 * 2 ^ 59
def prefixEnd_6667130 : Nat := 4983230072969 + 3 ^ 40 * 6667130 * 2
def baseEnd_6667130 : Nat := 3423442276010605056913433

theorem tailTrace_6667130 : CollatzResearch.WordTrace tailWord_6667130 prefixEnd_6667130 3423442276010605056913433 := by
  unfold tailWord_6667130
  simp only [CollatzResearch.WordTrace]
  refine ⟨60792552084033534999035711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162113472224089426664095229 60792552084033534999035711)
  ·
    refine ⟨91188828126050302498553567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60792552084033534999035711 91188828126050302498553567)
    ·
      refine ⟨136783242189075453747830351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91188828126050302498553567 136783242189075453747830351)
      ·
        refine ⟨205174863283613180621745527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136783242189075453747830351 205174863283613180621745527)
        ·
          refine ⟨307762294925419770932618291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205174863283613180621745527 307762294925419770932618291)
          ·
            refine ⟨461643442388129656398927437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307762294925419770932618291 461643442388129656398927437)
            ·
              refine ⟨173116290895548621149597789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461643442388129656398927437 173116290895548621149597789)
              ·
                refine ⟨64918609085830732931099171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173116290895548621149597789 64918609085830732931099171)
                ·
                  refine ⟨97377913628746099396648757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64918609085830732931099171 97377913628746099396648757)
                  ·
                    refine ⟨9129179402694946818435821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97377913628746099396648757 9129179402694946818435821)
                    ·
                      refine ⟨3423442276010605056913433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129179402694946818435821 3423442276010605056913433)
                      ·
                        rfl

theorem cell23_6667130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_6667130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667130 prefixEnd_6667130 := by exact prefixLift 6667130
  have htrace : WordTrace (prefixWord ++ tailWord_6667130) baseStart_6667130 baseEnd_6667130 := by
    simpa [prefixWord, tailWord_6667130, baseEnd_6667130] using wordTrace_append hprefix tailTrace_6667130
  have hstable : (prefixWord ++ tailWord_6667130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667130).length < 2 ^ (prefixWord ++ tailWord_6667130).sum := by decide
  have hdescent : baseEnd_6667130 < baseStart_6667130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667131 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 2, 2, 2]
def baseStart_6667131 : Nat := 118140960795 + 6667131 * 2 ^ 59
def prefixEnd_6667131 : Nat := 4983230072969 + 3 ^ 40 * 6667131 * 2
def baseEnd_6667131 : Nat := 3423442789491259553000929

theorem tailTrace_6667131 : CollatzResearch.WordTrace tailWord_6667131 prefixEnd_6667131 3423442789491259553000929 := by
  unfold tailWord_6667131
  simp only [CollatzResearch.WordTrace]
  refine ⟨243170244809130517166929247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162113496539420344777952831 243170244809130517166929247)
  ·
    refine ⟨364755367213695775750393871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243170244809130517166929247 364755367213695775750393871)
    ·
      refine ⟨547133050820543663625590807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364755367213695775750393871 547133050820543663625590807)
      ·
        refine ⟨820699576230815495438386211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547133050820543663625590807 820699576230815495438386211)
        ·
          refine ⟨1231049364346223243157579317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820699576230815495438386211 1231049364346223243157579317)
          ·
            refine ⟨115410877907458429046023061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1231049364346223243157579317 115410877907458429046023061)
            ·
              refine ⟨5409884901912113861532331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115410877907458429046023061 5409884901912113861532331)
              ·
                refine ⟨8114827352868170792298497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409884901912113861532331 8114827352868170792298497)
                ·
                  refine ⟨6086120514651128094223873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8114827352868170792298497 6086120514651128094223873)
                  ·
                    refine ⟨4564590385988346070667905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6086120514651128094223873 4564590385988346070667905)
                    ·
                      refine ⟨3423442789491259553000929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564590385988346070667905 3423442789491259553000929)
                      ·
                        rfl

theorem cell23_6667131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 2, 2].length) (baseStart_6667131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667131 prefixEnd_6667131 := by exact prefixLift 6667131
  have htrace : WordTrace (prefixWord ++ tailWord_6667131) baseStart_6667131 baseEnd_6667131 := by
    simpa [prefixWord, tailWord_6667131, baseEnd_6667131] using wordTrace_append hprefix tailTrace_6667131
  have hstable : (prefixWord ++ tailWord_6667131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667131).length < 2 ^ (prefixWord ++ tailWord_6667131).sum := by decide
  have hdescent : baseEnd_6667131 < baseStart_6667131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667167 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 2, 5]
def baseStart_6667167 : Nat := 118140960795 + 6667167 * 2 ^ 59
def prefixEnd_6667167 : Nat := 4983230072969 + 3 ^ 40 * 6667167 * 2
def baseEnd_6667167 : Nat := 1141153758264940470716921

theorem tailTrace_6667167 : CollatzResearch.WordTrace tailWord_6667167 prefixEnd_6667167 1141153758264940470716921 := by
  unfold tailWord_6667167
  simp only [CollatzResearch.WordTrace]
  refine ⟨243171557837000095315239755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162114371891333396876826503 243171557837000095315239755)
  ·
    refine ⟨364757336755500142972859633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243171557837000095315239755 364757336755500142972859633)
    ·
      refine ⟨273568002566625107229644725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364757336755500142972859633 273568002566625107229644725)
      ·
        refine ⟨25647000240621103802779193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273568002566625107229644725 25647000240621103802779193)
        ·
          refine ⟨19235250180465827852084395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25647000240621103802779193 19235250180465827852084395)
          ·
            refine ⟨28852875270698741778126593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19235250180465827852084395 28852875270698741778126593)
            ·
              refine ⟨21639656453024056333594945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28852875270698741778126593 21639656453024056333594945)
              ·
                refine ⟨16229742339768042250196209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21639656453024056333594945 16229742339768042250196209)
                ·
                  refine ⟨12172306754826031687647157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16229742339768042250196209 12172306754826031687647157)
                  ·
                    refine ⟨1141153758264940470716921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12172306754826031687647157 1141153758264940470716921)
                    ·
                      rfl

theorem cell23_6667167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_6667167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667167 prefixEnd_6667167 := by exact prefixLift 6667167
  have htrace : WordTrace (prefixWord ++ tailWord_6667167) baseStart_6667167 baseEnd_6667167 := by
    simpa [prefixWord, tailWord_6667167, baseEnd_6667167] using wordTrace_append hprefix tailTrace_6667167
  have hstable : (prefixWord ++ tailWord_6667167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667167).length < 2 ^ (prefixWord ++ tailWord_6667167).sum := by decide
  have hdescent : baseEnd_6667167 < baseStart_6667167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667181 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6667181 : Nat := 118140960795 + 6667181 * 2 ^ 59
def prefixEnd_6667181 : Nat := 4983230072969 + 3 ^ 40 * 6667181 * 2
def baseEnd_6667181 : Nat := 3423468463523984357375699

theorem tailTrace_6667181 : CollatzResearch.WordTrace tailWord_6667181 prefixEnd_6667181 3423468463523984357375699 := by
  unfold tailWord_6667181
  simp only [CollatzResearch.WordTrace]
  refine ⟨243172068458949375706249397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162114712305966250470832931 243172068458949375706249397)
  ·
    refine ⟨22797381418026503972460881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243172068458949375706249397 22797381418026503972460881)
    ·
      refine ⟨17098036063519877979345661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22797381418026503972460881 17098036063519877979345661)
      ·
        refine ⟨6411763523819954242254623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17098036063519877979345661 6411763523819954242254623)
        ·
          refine ⟨9617645285729931363381935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411763523819954242254623 9617645285729931363381935)
          ·
            refine ⟨14426467928594897045072903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617645285729931363381935 14426467928594897045072903)
            ·
              refine ⟨21639701892892345567609355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14426467928594897045072903 21639701892892345567609355)
              ·
                refine ⟨32459552839338518351414033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21639701892892345567609355 32459552839338518351414033)
                ·
                  refine ⟨24344664629503888763560525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32459552839338518351414033 24344664629503888763560525)
                  ·
                    refine ⟨9129249236063958286335197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24344664629503888763560525 9129249236063958286335197)
                    ·
                      refine ⟨3423468463523984357375699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129249236063958286335197 3423468463523984357375699)
                      ·
                        rfl

theorem cell23_6667181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6667181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667181 prefixEnd_6667181 := by exact prefixLift 6667181
  have htrace : WordTrace (prefixWord ++ tailWord_6667181) baseStart_6667181 baseEnd_6667181 := by
    simpa [prefixWord, tailWord_6667181, baseEnd_6667181] using wordTrace_append hprefix tailTrace_6667181
  have hstable : (prefixWord ++ tailWord_6667181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667181).length < 2 ^ (prefixWord ++ tailWord_6667181).sum := by decide
  have hdescent : baseEnd_6667181 < baseStart_6667181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667210 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_6667210 : Nat := 118140960795 + 6667210 * 2 ^ 59
def prefixEnd_6667210 : Nat := 4983230072969 + 3 ^ 40 * 6667210 * 2
def baseEnd_6667210 : Nat := 380387039384773860434785

theorem tailTrace_6667210 : CollatzResearch.WordTrace tailWord_6667210 prefixEnd_6667210 380387039384773860434785 := by
  unfold tailWord_6667210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60793281543961078414763771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162115417450562875772703389 60793281543961078414763771)
  ·
    refine ⟨91189922315941617622145657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60793281543961078414763771 91189922315941617622145657)
    ·
      refine ⟨68392441736956213216609243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91189922315941617622145657 68392441736956213216609243)
      ·
        refine ⟨102588662605434319824913865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68392441736956213216609243 102588662605434319824913865)
        ·
          refine ⟨76941496954075739868685399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102588662605434319824913865 76941496954075739868685399)
          ·
            refine ⟨115412245431113609803028099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76941496954075739868685399 115412245431113609803028099)
            ·
              refine ⟨173118368146670414704542149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115412245431113609803028099 173118368146670414704542149)
              ·
                refine ⟨32459694027500702757101653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173118368146670414704542149 32459694027500702757101653)
                ·
                  refine ⟨380387039384773860434785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32459694027500702757101653 380387039384773860434785)
                  ·
                    rfl

theorem cell23_6667210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_6667210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667210 prefixEnd_6667210 := by exact prefixLift 6667210
  have htrace : WordTrace (prefixWord ++ tailWord_6667210) baseStart_6667210 baseEnd_6667210 := by
    simpa [prefixWord, tailWord_6667210, baseEnd_6667210] using wordTrace_append hprefix tailTrace_6667210
  have hstable : (prefixWord ++ tailWord_6667210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667210).length < 2 ^ (prefixWord ++ tailWord_6667210).sum := by decide
  have hdescent : baseEnd_6667210 < baseStart_6667210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667274 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_6667274 : Nat := 118140960795 + 6667274 * 2 ^ 59
def prefixEnd_6667274 : Nat := 4983230072969 + 3 ^ 40 * 6667274 * 2
def baseEnd_6667274 : Nat := 1141172072408284164504257

theorem tailTrace_6667274 : CollatzResearch.WordTrace tailWord_6667274 prefixEnd_6667274 1141172072408284164504257 := by
  unfold tailWord_6667274
  simp only [CollatzResearch.WordTrace]
  refine ⟨60793865111903113147346219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162116973631741635059589917 60793865111903113147346219)
  ·
    refine ⟨91190797667854669721019329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60793865111903113147346219 91190797667854669721019329)
    ·
      refine ⟨68393098250891002290764497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91190797667854669721019329 68393098250891002290764497)
      ·
        refine ⟨51294823688168251718073373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68393098250891002290764497 51294823688168251718073373)
        ·
          refine ⟨19235558883063094394277515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51294823688168251718073373 19235558883063094394277515)
          ·
            refine ⟨28853338324594641591416273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19235558883063094394277515 28853338324594641591416273)
            ·
              refine ⟨21640003743445981193562205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28853338324594641591416273 21640003743445981193562205)
              ·
                refine ⟨8115001403792242947585827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21640003743445981193562205 8115001403792242947585827)
                ·
                  refine ⟨12172502105688364421378741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8115001403792242947585827 12172502105688364421378741)
                  ·
                    refine ⟨1141172072408284164504257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12172502105688364421378741 1141172072408284164504257)
                    ·
                      rfl

theorem cell23_6667274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_6667274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667274 prefixEnd_6667274 := by exact prefixLift 6667274
  have htrace : WordTrace (prefixWord ++ tailWord_6667274) baseStart_6667274 baseEnd_6667274 := by
    simpa [prefixWord, tailWord_6667274, baseEnd_6667274] using wordTrace_append hprefix tailTrace_6667274
  have hstable : (prefixWord ++ tailWord_6667274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667274).length < 2 ^ (prefixWord ++ tailWord_6667274).sum := by decide
  have hdescent : baseEnd_6667274 < baseStart_6667274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667282 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6667282 : Nat := 118140960795 + 6667282 * 2 ^ 59
def prefixEnd_6667282 : Nat := 4983230072969 + 3 ^ 40 * 6667282 * 2
def baseEnd_6667282 : Nat := 1141173441690029487404245

theorem tailTrace_6667282 : CollatzResearch.WordTrace tailWord_6667282 prefixEnd_6667282 1141173441690029487404245 := by
  unfold tailWord_6667282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60793938057895867488919025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162117168154388979970450733 60793938057895867488919025)
  ·
    refine ⟨45595453543421900616689269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60793938057895867488919025 45595453543421900616689269)
    ·
      refine ⟨4274573769695803182814619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45595453543421900616689269 4274573769695803182814619)
      ·
        refine ⟨6411860654543704774221929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274573769695803182814619 6411860654543704774221929)
        ·
          refine ⟨4808895490907778580666447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6411860654543704774221929 4808895490907778580666447)
          ·
            refine ⟨7213343236361667870999671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808895490907778580666447 7213343236361667870999671)
            ·
              refine ⟨10820014854542501806499507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7213343236361667870999671 10820014854542501806499507)
              ·
                refine ⟨16230022281813752709749261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10820014854542501806499507 16230022281813752709749261)
                ·
                  refine ⟨6086258355680157266155973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16230022281813752709749261 6086258355680157266155973)
                  ·
                    refine ⟨1141173441690029487404245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6086258355680157266155973 1141173441690029487404245)
                    ·
                      rfl

theorem cell23_6667282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6667282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667282 prefixEnd_6667282 := by exact prefixLift 6667282
  have htrace : WordTrace (prefixWord ++ tailWord_6667282) baseStart_6667282 baseEnd_6667282 := by
    simpa [prefixWord, tailWord_6667282, baseEnd_6667282] using wordTrace_append hprefix tailTrace_6667282
  have hstable : (prefixWord ++ tailWord_6667282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667282).length < 2 ^ (prefixWord ++ tailWord_6667282).sum := by decide
  have hdescent : baseEnd_6667282 < baseStart_6667282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667307 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4]
def baseStart_6667307 : Nat := 118140960795 + 6667307 * 2 ^ 59
def prefixEnd_6667307 : Nat := 4983230072969 + 3 ^ 40 * 6667307 * 2
def baseEnd_6667307 : Nat := 3423533162086450864400119

theorem tailTrace_6667307 : CollatzResearch.WordTrace tailWord_6667307 prefixEnd_6667307 3423533162086450864400119 := by
  unfold tailWord_6667307
  simp only [CollatzResearch.WordTrace]
  refine ⟨243176664056492899225336175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162117776037661932816890783 243176664056492899225336175)
  ·
    refine ⟨364764996084739348838004263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243176664056492899225336175 364764996084739348838004263)
    ·
      refine ⟨547147494127109023257006395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364764996084739348838004263 547147494127109023257006395)
      ·
        refine ⟨820721241190663534885509593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547147494127109023257006395 820721241190663534885509593)
        ·
          refine ⟨615540930892997651164132195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820721241190663534885509593 615540930892997651164132195)
          ·
            refine ⟨923311396339496476746198293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615540930892997651164132195 923311396339496476746198293)
            ·
              refine ⟨43280221703413897347478045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 923311396339496476746198293 43280221703413897347478045)
              ·
                refine ⟨16230083138780211505304267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43280221703413897347478045 16230083138780211505304267)
                ·
                  refine ⟨24345124708170317257956401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16230083138780211505304267 24345124708170317257956401)
                  ·
                    refine ⟨18258843531127737943467301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24345124708170317257956401 18258843531127737943467301)
                    ·
                      refine ⟨3423533162086450864400119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18258843531127737943467301 3423533162086450864400119)
                      ·
                        rfl

theorem cell23_6667307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].length) (baseStart_6667307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667307 prefixEnd_6667307 := by exact prefixLift 6667307
  have htrace : WordTrace (prefixWord ++ tailWord_6667307) baseStart_6667307 baseEnd_6667307 := by
    simpa [prefixWord, tailWord_6667307, baseEnd_6667307] using wordTrace_append hprefix tailTrace_6667307
  have hstable : (prefixWord ++ tailWord_6667307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667307).length < 2 ^ (prefixWord ++ tailWord_6667307).sum := by decide
  have hdescent : baseEnd_6667307 < baseStart_6667307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667314 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_6667314 : Nat := 118140960795 + 6667314 * 2 ^ 59
def prefixEnd_6667314 : Nat := 4983230072969 + 3 ^ 40 * 6667314 * 2
def baseEnd_6667314 : Nat := 3423536756451032337012587

theorem tailTrace_6667314 : CollatzResearch.WordTrace tailWord_6667314 prefixEnd_6667314 3423536756451032337012587 := by
  unfold tailWord_6667314
  simp only [CollatzResearch.WordTrace]
  refine ⟨60794229841866884855210249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162117946244978359613893997 60794229841866884855210249)
  ·
    refine ⟨45595672381400163641407687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60794229841866884855210249 45595672381400163641407687)
    ·
      refine ⟨68393508572100245462111531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45595672381400163641407687 68393508572100245462111531)
      ·
        refine ⟨102590262858150368193167297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68393508572100245462111531 102590262858150368193167297)
        ·
          refine ⟨76942697143612776144875473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102590262858150368193167297 76942697143612776144875473)
          ·
            refine ⟨57707022857709582108656605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76942697143612776144875473 57707022857709582108656605)
            ·
              refine ⟨21640133571641093290746227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57707022857709582108656605 21640133571641093290746227)
              ·
                refine ⟨32460200357461639936119341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21640133571641093290746227 32460200357461639936119341)
                ·
                  refine ⟨12172575134048114976044753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32460200357461639936119341 12172575134048114976044753)
                  ·
                    refine ⟨9129431350536086232033565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12172575134048114976044753 9129431350536086232033565)
                    ·
                      refine ⟨3423536756451032337012587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129431350536086232033565 3423536756451032337012587)
                      ·
                        rfl

theorem cell23_6667314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_6667314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667314 prefixEnd_6667314 := by exact prefixLift 6667314
  have htrace : WordTrace (prefixWord ++ tailWord_6667314) baseStart_6667314 baseEnd_6667314 := by
    simpa [prefixWord, tailWord_6667314, baseEnd_6667314] using wordTrace_append hprefix tailTrace_6667314
  have hstable : (prefixWord ++ tailWord_6667314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667314).length < 2 ^ (prefixWord ++ tailWord_6667314).sum := by decide
  have hdescent : baseEnd_6667314 < baseStart_6667314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667324 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_6667324 : Nat := 118140960795 + 6667324 * 2 ^ 59
def prefixEnd_6667324 : Nat := 4983230072969 + 3 ^ 40 * 6667324 * 2
def baseEnd_6667324 : Nat := 3423541891257577297887541

theorem tailTrace_6667324 : CollatzResearch.WordTrace tailWord_6667324 prefixEnd_6667324 3423541891257577297887541 := by
  unfold tailWord_6667324
  simp only [CollatzResearch.WordTrace]
  refine ⟨121588642048715655564352513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162118189398287540752470017 121588642048715655564352513)
  ·
    refine ⟨91191481536536741673264385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121588642048715655564352513 91191481536536741673264385)
    ·
      refine ⟨68393611152402556254948289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91191481536536741673264385 68393611152402556254948289)
      ·
        refine ⟨51295208364301917191211217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68393611152402556254948289 51295208364301917191211217)
        ·
          refine ⟨38471406273226437893408413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51295208364301917191211217 38471406273226437893408413)
          ·
            refine ⟨14426777352459914210028155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38471406273226437893408413 14426777352459914210028155)
            ·
              refine ⟨21640166028689871315042233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14426777352459914210028155 21640166028689871315042233)
              ·
                refine ⟨16230124521517403486281675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21640166028689871315042233 16230124521517403486281675)
                ·
                  refine ⟨24345186782276105229422513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16230124521517403486281675 24345186782276105229422513)
                  ·
                    refine ⟨18258890086707078922066885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24345186782276105229422513 18258890086707078922066885)
                    ·
                      refine ⟨3423541891257577297887541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18258890086707078922066885 3423541891257577297887541)
                      ·
                        rfl

theorem cell23_6667324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_6667324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667324 prefixEnd_6667324 := by exact prefixLift 6667324
  have htrace : WordTrace (prefixWord ++ tailWord_6667324) baseStart_6667324 baseEnd_6667324 := by
    simpa [prefixWord, tailWord_6667324, baseEnd_6667324] using wordTrace_append hprefix tailTrace_6667324
  have hstable : (prefixWord ++ tailWord_6667324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667324).length < 2 ^ (prefixWord ++ tailWord_6667324).sum := by decide
  have hdescent : baseEnd_6667324 < baseStart_6667324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667328 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 1, 2, 2]
def baseStart_6667328 : Nat := 118140960795 + 6667328 * 2 ^ 59
def prefixEnd_6667328 : Nat := 4983230072969 + 3 ^ 40 * 6667328 * 2
def baseEnd_6667328 : Nat := 3423543945180195282237523

theorem tailTrace_6667328 : CollatzResearch.WordTrace tailWord_6667328 prefixEnd_6667328 3423543945180195282237523 := by
  unfold tailWord_6667328
  simp only [CollatzResearch.WordTrace]
  refine ⟨121588714994708409905925319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162118286659611213207900425 121588714994708409905925319)
  ·
    refine ⟨182383072492062614858887979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121588714994708409905925319 182383072492062614858887979)
    ·
      refine ⟨273574608738093922288331969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182383072492062614858887979 273574608738093922288331969)
      ·
        refine ⟨205180956553570441716248977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273574608738093922288331969 205180956553570441716248977)
        ·
          refine ⟨153885717415177831287186733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205180956553570441716248977 153885717415177831287186733)
          ·
            refine ⟨57707144030691686732695025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153885717415177831287186733 57707144030691686732695025)
            ·
              refine ⟨43280358023018765049521269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57707144030691686732695025 43280358023018765049521269)
              ·
                refine ⟨4057533564658009223392619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43280358023018765049521269 4057533564658009223392619)
                ·
                  refine ⟨6086300346987013835088929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057533564658009223392619 6086300346987013835088929)
                  ·
                    refine ⟨4564725260240260376316697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6086300346987013835088929 4564725260240260376316697)
                    ·
                      refine ⟨3423543945180195282237523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564725260240260376316697 3423543945180195282237523)
                      ·
                        rfl

theorem cell23_6667328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_6667328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667328 prefixEnd_6667328 := by exact prefixLift 6667328
  have htrace : WordTrace (prefixWord ++ tailWord_6667328) baseStart_6667328 baseEnd_6667328 := by
    simpa [prefixWord, tailWord_6667328, baseEnd_6667328] using wordTrace_append hprefix tailTrace_6667328
  have hstable : (prefixWord ++ tailWord_6667328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667328).length < 2 ^ (prefixWord ++ tailWord_6667328).sum := by decide
  have hdescent : baseEnd_6667328 < baseStart_6667328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667331 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 1, 2, 3]
def baseStart_6667331 : Nat := 118140960795 + 6667331 * 2 ^ 59
def prefixEnd_6667331 : Nat := 4983230072969 + 3 ^ 40 * 6667331 * 2
def baseEnd_6667331 : Nat := 3423545485622158770500009

theorem tailTrace_6667331 : CollatzResearch.WordTrace tailWord_6667331 prefixEnd_6667331 3423545485622158770500009 := by
  unfold tailWord_6667331
  simp only [CollatzResearch.WordTrace]
  refine ⟨243177539408405951324209847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162118359605603967549473231 243177539408405951324209847)
  ·
    refine ⟨364766309112608926986314771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243177539408405951324209847 364766309112608926986314771)
    ·
      refine ⟨547149463668913390479472157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364766309112608926986314771 547149463668913390479472157)
      ·
        refine ⟨205181048875842521429802059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547149463668913390479472157 205181048875842521429802059)
        ·
          refine ⟨307771573313763782144703089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205181048875842521429802059 307771573313763782144703089)
          ·
            refine ⟨230828679985322836608527317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307771573313763782144703089 230828679985322836608527317)
            ·
              refine ⟨5410047187156003983012359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230828679985322836608527317 5410047187156003983012359)
              ·
                refine ⟨8115070780734005974518539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410047187156003983012359 8115070780734005974518539)
                ·
                  refine ⟨12172606171101008961777809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8115070780734005974518539 12172606171101008961777809)
                  ·
                    refine ⟨9129454628325756721333357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12172606171101008961777809 9129454628325756721333357)
                    ·
                      refine ⟨3423545485622158770500009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129454628325756721333357 3423545485622158770500009)
                      ·
                        rfl

theorem cell23_6667331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_6667331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667331 prefixEnd_6667331 := by exact prefixLift 6667331
  have htrace : WordTrace (prefixWord ++ tailWord_6667331) baseStart_6667331 baseEnd_6667331 := by
    simpa [prefixWord, tailWord_6667331, baseEnd_6667331] using wordTrace_append hprefix tailTrace_6667331
  have hstable : (prefixWord ++ tailWord_6667331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667331).length < 2 ^ (prefixWord ++ tailWord_6667331).sum := by decide
  have hdescent : baseEnd_6667331 < baseStart_6667331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667334 : List Nat := [6, 1, 1, 1, 1, 13]
def baseStart_6667334 : Nat := 118140960795 + 6667334 * 2 ^ 59
def prefixEnd_6667334 : Nat := 4983230072969 + 3 ^ 40 * 6667334 * 2
def baseEnd_6667334 : Nat := 14088670889152766496965

theorem tailTrace_6667334 : CollatzResearch.WordTrace tailWord_6667334 prefixEnd_6667334 14088670889152766496965 := by
  unfold tailWord_6667334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599301525856096338642783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162118432551596721891046037 7599301525856096338642783)
  ·
    refine ⟨11398952288784144507964175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599301525856096338642783 11398952288784144507964175)
    ·
      refine ⟨17098428433176216761946263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11398952288784144507964175 17098428433176216761946263)
      ·
        refine ⟨25647642649764325142919395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17098428433176216761946263 25647642649764325142919395)
        ·
          refine ⟨38471463974646487714379093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25647642649764325142919395 38471463974646487714379093)
          ·
            refine ⟨14088670889152766496965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38471463974646487714379093 14088670889152766496965)
            ·
              rfl

theorem cell23_6667334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 13].length) (baseStart_6667334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667334 prefixEnd_6667334 := by exact prefixLift 6667334
  have htrace : WordTrace (prefixWord ++ tailWord_6667334) baseStart_6667334 baseEnd_6667334 := by
    simpa [prefixWord, tailWord_6667334, baseEnd_6667334] using wordTrace_append hprefix tailTrace_6667334
  have hstable : (prefixWord ++ tailWord_6667334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667334).length < 2 ^ (prefixWord ++ tailWord_6667334).sum := by decide
  have hdescent : baseEnd_6667334 < baseStart_6667334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667344 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 4, 1, 3]
def baseStart_6667344 : Nat := 118140960795 + 6667344 * 2 ^ 59
def prefixEnd_6667344 : Nat := 4983230072969 + 3 ^ 40 * 6667344 * 2
def baseEnd_6667344 : Nat := 3423552160870667219637449

theorem tailTrace_6667344 : CollatzResearch.WordTrace tailWord_6667344 prefixEnd_6667344 3423552160870667219637449 := by
  unfold tailWord_6667344
  simp only [CollatzResearch.WordTrace]
  refine ⟨121589006778679427272216543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162118675704905903029622057 121589006778679427272216543)
  ·
    refine ⟨182383510168019140908324815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121589006778679427272216543 182383510168019140908324815)
    ·
      refine ⟨273575265252028711362487223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182383510168019140908324815 273575265252028711362487223)
      ·
        refine ⟨410362897878043067043730835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273575265252028711362487223 410362897878043067043730835)
        ·
          refine ⟨615544346817064600565596253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410362897878043067043730835 615544346817064600565596253)
          ·
            refine ⟨230829130056399225212098595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615544346817064600565596253 230829130056399225212098595)
            ·
              refine ⟨346243695084598837818147893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230829130056399225212098595 346243695084598837818147893)
              ·
                refine ⟨32460346414181141045451365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346243695084598837818147893 32460346414181141045451365)
                ·
                  refine ⟨6086314952658963946022131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32460346414181141045451365 6086314952658963946022131)
                  ·
                    refine ⟨9129472428988445919033197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6086314952658963946022131 9129472428988445919033197)
                    ·
                      refine ⟨3423552160870667219637449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129472428988445919033197 3423552160870667219637449)
                      ·
                        rfl

theorem cell23_6667344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_6667344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667344 prefixEnd_6667344 := by exact prefixLift 6667344
  have htrace : WordTrace (prefixWord ++ tailWord_6667344) baseStart_6667344 baseEnd_6667344 := by
    simpa [prefixWord, tailWord_6667344, baseEnd_6667344] using wordTrace_append hprefix tailTrace_6667344
  have hstable : (prefixWord ++ tailWord_6667344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667344).length < 2 ^ (prefixWord ++ tailWord_6667344).sum := by decide
  have hdescent : baseEnd_6667344 < baseStart_6667344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667345 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 1, 2, 2]
def baseStart_6667345 : Nat := 118140960795 + 6667345 * 2 ^ 59
def prefixEnd_6667345 : Nat := 4983230072969 + 3 ^ 40 * 6667345 * 2
def baseEnd_6667345 : Nat := 3423552674351321715724945

theorem tailTrace_6667345 : CollatzResearch.WordTrace tailWord_6667345 prefixEnd_6667345 3423552674351321715724945 := by
  unfold tailWord_6667345
  simp only [CollatzResearch.WordTrace]
  refine ⟨243178050030355231715219489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162118700020236821143479659 243178050030355231715219489)
  ·
    refine ⟨182383537522766423786414617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243178050030355231715219489 182383537522766423786414617)
    ·
      refine ⟨136787653142074817839810963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182383537522766423786414617 136787653142074817839810963)
      ·
        refine ⟨205181479713112226759716445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136787653142074817839810963 205181479713112226759716445)
        ·
          refine ⟨76943054892417085034893667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205181479713112226759716445 76943054892417085034893667)
          ·
            refine ⟨115414582338625627552340501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76943054892417085034893667 115414582338625627552340501)
            ·
              refine ⟨5410058547123076291515961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115414582338625627552340501 5410058547123076291515961)
              ·
                refine ⟨4057543910342307218636971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5410058547123076291515961 4057543910342307218636971)
                ·
                  refine ⟨6086315865513460827955457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057543910342307218636971 6086315865513460827955457)
                  ·
                    refine ⟨4564736899135095620966593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6086315865513460827955457 4564736899135095620966593)
                    ·
                      refine ⟨3423552674351321715724945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564736899135095620966593 3423552674351321715724945)
                      ·
                        rfl

theorem cell23_6667345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_6667345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667345 prefixEnd_6667345 := by exact prefixLift 6667345
  have htrace : WordTrace (prefixWord ++ tailWord_6667345) baseStart_6667345 baseEnd_6667345 := by
    simpa [prefixWord, tailWord_6667345, baseEnd_6667345] using wordTrace_append hprefix tailTrace_6667345
  have hstable : (prefixWord ++ tailWord_6667345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667345).length < 2 ^ (prefixWord ++ tailWord_6667345).sum := by decide
  have hdescent : baseEnd_6667345 < baseStart_6667345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667358 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6667358 : Nat := 118140960795 + 6667358 * 2 ^ 59
def prefixEnd_6667358 : Nat := 4983230072969 + 3 ^ 40 * 6667358 * 2
def baseEnd_6667358 : Nat := 3423559349599830164862385

theorem tailTrace_6667358 : CollatzResearch.WordTrace tailWord_6667358 prefixEnd_6667358 3423559349599830164862385 := by
  unfold tailWord_6667358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30397315522413516866930341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162119016119538756623628485 30397315522413516866930341)
  ·
    refine ⟨5699496660452534412549439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30397315522413516866930341 5699496660452534412549439)
    ·
      refine ⟨8549244990678801618824159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699496660452534412549439 8549244990678801618824159)
      ·
        refine ⟨12823867486018202428236239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549244990678801618824159 12823867486018202428236239)
        ·
          refine ⟨19235801229027303642354359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12823867486018202428236239 19235801229027303642354359)
          ·
            refine ⟨28853701843540955463531539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19235801229027303642354359 28853701843540955463531539)
            ·
              refine ⟨43280552765311433195297309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28853701843540955463531539 43280552765311433195297309)
              ·
                refine ⟨16230207286991787448236491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43280552765311433195297309 16230207286991787448236491)
                ·
                  refine ⟨24345310930487681172354737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16230207286991787448236491 24345310930487681172354737)
                  ·
                    refine ⟨18258983197865760879266053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24345310930487681172354737 18258983197865760879266053)
                    ·
                      refine ⟨3423559349599830164862385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18258983197865760879266053 3423559349599830164862385)
                      ·
                        rfl

theorem cell23_6667358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6667358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667358 prefixEnd_6667358 := by exact prefixLift 6667358
  have htrace : WordTrace (prefixWord ++ tailWord_6667358) baseStart_6667358 baseEnd_6667358 := by
    simpa [prefixWord, tailWord_6667358, baseEnd_6667358] using wordTrace_append hprefix tailTrace_6667358
  have hstable : (prefixWord ++ tailWord_6667358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667358).length < 2 ^ (prefixWord ++ tailWord_6667358).sum := by decide
  have hdescent : baseEnd_6667358 < baseStart_6667358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667361 : List Nat := [1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_6667361 : Nat := 118140960795 + 6667361 * 2 ^ 59
def prefixEnd_6667361 : Nat := 4983230072969 + 3 ^ 40 * 6667361 * 2
def baseEnd_6667361 : Nat := 3423560890041793653124871

theorem tailTrace_6667361 : CollatzResearch.WordTrace tailWord_6667361 prefixEnd_6667361 3423560890041793653124871 := by
  unfold tailWord_6667361
  simp only [CollatzResearch.WordTrace]
  refine ⟨243178633598297266447801937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162119089065531510965201291 243178633598297266447801937)
  ·
    refine ⟨182383975198722949835851453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243178633598297266447801937 182383975198722949835851453)
    ·
      refine ⟨68393990699521106188444295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182383975198722949835851453 68393990699521106188444295)
      ·
        refine ⟨102590986049281659282666443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68393990699521106188444295 102590986049281659282666443)
        ·
          refine ⟨153886479073922488923999665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102590986049281659282666443 153886479073922488923999665)
          ·
            refine ⟨115414859305441866692999749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153886479073922488923999665 115414859305441866692999749)
            ·
              refine ⟨21640286119770350004937453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115414859305441866692999749 21640286119770350004937453)
              ·
                refine ⟨8115107294913881251851545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21640286119770350004937453 8115107294913881251851545)
                ·
                  refine ⟨6086330471185410938888659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8115107294913881251851545 6086330471185410938888659)
                  ·
                    refine ⟨9129495706778116408332989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6086330471185410938888659 9129495706778116408332989)
                    ·
                      refine ⟨3423560890041793653124871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129495706778116408332989 3423560890041793653124871)
                      ·
                        rfl

theorem cell23_6667361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_6667361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667361 prefixEnd_6667361 := by exact prefixLift 6667361
  have htrace : WordTrace (prefixWord ++ tailWord_6667361) baseStart_6667361 baseEnd_6667361 := by
    simpa [prefixWord, tailWord_6667361, baseEnd_6667361] using wordTrace_append hprefix tailTrace_6667361
  have hstable : (prefixWord ++ tailWord_6667361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667361).length < 2 ^ (prefixWord ++ tailWord_6667361).sum := by decide
  have hdescent : baseEnd_6667361 < baseStart_6667361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667387 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5]
def baseStart_6667387 : Nat := 118140960795 + 6667387 * 2 ^ 59
def prefixEnd_6667387 : Nat := 4983230072969 + 3 ^ 40 * 6667387 * 2
def baseEnd_6667387 : Nat := 3423574240538810551399751

theorem tailTrace_6667387 : CollatzResearch.WordTrace tailWord_6667387 prefixEnd_6667387 3423574240538810551399751 := by
  unfold tailWord_6667387
  simp only [CollatzResearch.WordTrace]
  refine ⟨243179581896203072888248415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162119721264135381925498943 243179581896203072888248415)
  ·
    refine ⟨364769372844304609332372623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243179581896203072888248415 364769372844304609332372623)
    ·
      refine ⟨547154059266456913998558935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364769372844304609332372623 547154059266456913998558935)
      ·
        refine ⟨820731088899685370997838403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547154059266456913998558935 820731088899685370997838403)
        ·
          refine ⟨1231096633349528056496757605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820731088899685370997838403 1231096633349528056496757605)
          ·
            refine ⟨230830618753036510593142051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1231096633349528056496757605 230830618753036510593142051)
            ·
              refine ⟨346245928129554765889713077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230830618753036510593142051 346245928129554765889713077)
              ·
                refine ⟨32460555762145759302160601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346245928129554765889713077 32460555762145759302160601)
                ·
                  refine ⟨24345416821609319476620451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32460555762145759302160601 24345416821609319476620451)
                  ·
                    refine ⟨36518125232413979214930677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24345416821609319476620451 36518125232413979214930677)
                    ·
                      refine ⟨3423574240538810551399751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36518125232413979214930677 3423574240538810551399751)
                      ·
                        rfl

theorem cell23_6667387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_6667387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667387 prefixEnd_6667387 := by exact prefixLift 6667387
  have htrace : WordTrace (prefixWord ++ tailWord_6667387) baseStart_6667387 baseEnd_6667387 := by
    simpa [prefixWord, tailWord_6667387, baseEnd_6667387] using wordTrace_append hprefix tailTrace_6667387
  have hstable : (prefixWord ++ tailWord_6667387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667387).length < 2 ^ (prefixWord ++ tailWord_6667387).sum := by decide
  have hdescent : baseEnd_6667387 < baseStart_6667387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667418 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6667418 : Nat := 118140960795 + 6667418 * 2 ^ 59
def prefixEnd_6667418 : Nat := 4983230072969 + 3 ^ 40 * 6667418 * 2
def baseEnd_6667418 : Nat := 3423590158439099930112109

theorem tailTrace_6667418 : CollatzResearch.WordTrace tailWord_6667418 prefixEnd_6667418 3423590158439099930112109 := by
  unfold tailWord_6667418
  simp only [CollatzResearch.WordTrace]
  refine ⟨60795178139772691295656727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162120475039393843455084605 60795178139772691295656727)
  ·
    refine ⟨91192767209659036943485091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60795178139772691295656727 91192767209659036943485091)
    ·
      refine ⟨136789150814488555415227637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91192767209659036943485091 136789150814488555415227637)
      ·
        refine ⟨12823982888858302070177591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136789150814488555415227637 12823982888858302070177591)
        ·
          refine ⟨19235974333287453105266387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12823982888858302070177591 19235974333287453105266387)
          ·
            refine ⟨28853961499931179657899581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19235974333287453105266387 28853961499931179657899581)
            ·
              refine ⟨10820235562474192371712343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28853961499931179657899581 10820235562474192371712343)
              ·
                refine ⟨16230353343711288557568515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10820235562474192371712343 16230353343711288557568515)
                ·
                  refine ⟨24345530015566932836352773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16230353343711288557568515 24345530015566932836352773)
                  ·
                    refine ⟨4564786877918799906816145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24345530015566932836352773 4564786877918799906816145)
                    ·
                      refine ⟨3423590158439099930112109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564786877918799906816145 3423590158439099930112109)
                      ·
                        rfl

theorem cell23_6667418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6667418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667418 prefixEnd_6667418 := by exact prefixLift 6667418
  have htrace : WordTrace (prefixWord ++ tailWord_6667418) baseStart_6667418 baseEnd_6667418 := by
    simpa [prefixWord, tailWord_6667418, baseEnd_6667418] using wordTrace_append hprefix tailTrace_6667418
  have hstable : (prefixWord ++ tailWord_6667418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667418).length < 2 ^ (prefixWord ++ tailWord_6667418).sum := by decide
  have hdescent : baseEnd_6667418 < baseStart_6667418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667467 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 8]
def baseStart_6667467 : Nat := 118140960795 + 6667467 * 2 ^ 59
def prefixEnd_6667467 : Nat := 4983230072969 + 3 ^ 40 * 6667467 * 2
def baseEnd_6667467 : Nat := 1141205106330390079466461

theorem tailTrace_6667467 : CollatzResearch.WordTrace tailWord_6667467 prefixEnd_6667467 1141205106330390079466461 := by
  unfold tailWord_6667467
  simp only [CollatzResearch.WordTrace]
  refine ⟨243182499735913246551160655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162121666490608831034107103 243182499735913246551160655)
  ·
    refine ⟨364773749603869869826740983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243182499735913246551160655 364773749603869869826740983)
    ·
      refine ⟨547160624405804804740111475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364773749603869869826740983 547160624405804804740111475)
      ·
        refine ⟨820740936608707207110167213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547160624405804804740111475 820740936608707207110167213)
        ·
          refine ⟨307777851228265202666312705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 820740936608707207110167213 307777851228265202666312705)
          ·
            refine ⟨230833388421198901999734529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307777851228265202666312705 230833388421198901999734529)
            ·
              refine ⟨173125041315899176499800897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230833388421198901999734529 173125041315899176499800897)
              ·
                refine ⟨129843780986924382374850673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173125041315899176499800897 129843780986924382374850673)
                ·
                  refine ⟨97382835740193286781138005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129843780986924382374850673 97382835740193286781138005)
                  ·
                    refine ⟨1141205106330390079466461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97382835740193286781138005 1141205106330390079466461)
                    ·
                      rfl

theorem cell23_6667467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_6667467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667467 prefixEnd_6667467 := by exact prefixLift 6667467
  have htrace : WordTrace (prefixWord ++ tailWord_6667467) baseStart_6667467 baseEnd_6667467 := by
    simpa [prefixWord, tailWord_6667467, baseEnd_6667467] using wordTrace_append hprefix tailTrace_6667467
  have hstable : (prefixWord ++ tailWord_6667467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667467).length < 2 ^ (prefixWord ++ tailWord_6667467).sum := by decide
  have hdescent : baseEnd_6667467 < baseStart_6667467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667469 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6667469 : Nat := 118140960795 + 6667469 * 2 ^ 59
def prefixEnd_6667469 : Nat := 4983230072969 + 3 ^ 40 * 6667469 * 2
def baseEnd_6667469 : Nat := 3423616345952479230574375

theorem tailTrace_6667469 : CollatzResearch.WordTrace tailWord_6667469 prefixEnd_6667469 3423616345952479230574375 := by
  unfold tailWord_6667469
  simp only [CollatzResearch.WordTrace]
  refine ⟨243182572681906000892733461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162121715121270667261822307 243182572681906000892733461)
  ·
    refine ⟨11399183094464343791846881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 243182572681906000892733461 11399183094464343791846881)
    ·
      refine ⟨8549387320848257843885161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11399183094464343791846881 8549387320848257843885161)
      ·
        refine ⟨6412040490636193382913871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8549387320848257843885161 6412040490636193382913871)
        ·
          refine ⟨9618060735954290074370807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6412040490636193382913871 9618060735954290074370807)
          ·
            refine ⟨14427091103931435111556211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618060735954290074370807 14427091103931435111556211)
            ·
              refine ⟨21640636655897152667334317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14427091103931435111556211 21640636655897152667334317)
              ·
                refine ⟨8115238745961432250250369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21640636655897152667334317 8115238745961432250250369)
                ·
                  refine ⟨6086429059471074187687777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8115238745961432250250369 6086429059471074187687777)
                  ·
                    refine ⟨4564821794603305640765833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6086429059471074187687777 4564821794603305640765833)
                    ·
                      refine ⟨3423616345952479230574375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4564821794603305640765833 3423616345952479230574375)
                      ·
                        rfl

theorem cell23_6667469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6667469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667469 prefixEnd_6667469 := by exact prefixLift 6667469
  have htrace : WordTrace (prefixWord ++ tailWord_6667469) baseStart_6667469 baseEnd_6667469 := by
    simpa [prefixWord, tailWord_6667469, baseEnd_6667469] using wordTrace_append hprefix tailTrace_6667469
  have hstable : (prefixWord ++ tailWord_6667469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667469).length < 2 ^ (prefixWord ++ tailWord_6667469).sum := by decide
  have hdescent : baseEnd_6667469 < baseStart_6667469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667565 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 6]
def baseStart_6667565 : Nat := 118140960795 + 6667565 * 2 ^ 59
def prefixEnd_6667565 : Nat := 4983230072969 + 3 ^ 40 * 6667565 * 2
def baseEnd_6667565 : Nat := 380407293343923428330437

theorem tailTrace_6667565 : CollatzResearch.WordTrace tailWord_6667565 prefixEnd_6667565 380407293343923428330437 := by
  unfold tailWord_6667565
  simp only [CollatzResearch.WordTrace]
  refine ⟨243186074089558209288228149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162124049393038806192152099 243186074089558209288228149)
  ·
    refine ⟨22798694445896082120771389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243186074089558209288228149 22798694445896082120771389)
    ·
      refine ⟨8549510417211030795289271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22798694445896082120771389 8549510417211030795289271)
      ·
        refine ⟨12824265625816546192933907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549510417211030795289271 12824265625816546192933907)
        ·
          refine ⟨19236398438724819289400861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12824265625816546192933907 19236398438724819289400861)
          ·
            refine ⟨7213649414521807233525323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19236398438724819289400861 7213649414521807233525323)
            ·
              refine ⟨10820474121782710850287985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7213649414521807233525323 10820474121782710850287985)
              ·
                refine ⟨8115355591337033137715989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10820474121782710850287985 8115355591337033137715989)
                ·
                  refine ⟨380407293343923428330437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8115355591337033137715989 380407293343923428330437)
                  ·
                    rfl

theorem cell23_6667565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_6667565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667565 prefixEnd_6667565 := by exact prefixLift 6667565
  have htrace : WordTrace (prefixWord ++ tailWord_6667565) baseStart_6667565 baseEnd_6667565 := by
    simpa [prefixWord, tailWord_6667565, baseEnd_6667565] using wordTrace_append hprefix tailTrace_6667565
  have hstable : (prefixWord ++ tailWord_6667565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667565).length < 2 ^ (prefixWord ++ tailWord_6667565).sum := by decide
  have hdescent : baseEnd_6667565 < baseStart_6667565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667591 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 1, 6]
def baseStart_6667591 : Nat := 118140960795 + 6667591 * 2 ^ 59
def prefixEnd_6667591 : Nat := 4983230072969 + 3 ^ 40 * 6667591 * 2
def baseEnd_6667591 : Nat := 1141226330197442584416271

theorem tailTrace_6667591 : CollatzResearch.WordTrace tailWord_6667591 prefixEnd_6667591 1141226330197442584416271 := by
  unfold tailWord_6667591
  simp only [CollatzResearch.WordTrace]
  refine ⟨243187022387464015728674627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162124681591642677152449751 243187022387464015728674627)
  ·
    refine ⟨364780533581196023593011941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243187022387464015728674627 364780533581196023593011941)
    ·
      refine ⟨68396350046474254423689739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364780533581196023593011941 68396350046474254423689739)
      ·
        refine ⟨102594525069711381635534609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68396350046474254423689739 102594525069711381635534609)
        ·
          refine ⟨76945893802283536226650957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102594525069711381635534609 76945893802283536226650957)
          ·
            refine ⟨28854710175856326084994109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76945893802283536226650957 28854710175856326084994109)
            ·
              refine ⟨10820516315946122281872791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28854710175856326084994109 10820516315946122281872791)
              ·
                refine ⟨16230774473919183422809187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10820516315946122281872791 16230774473919183422809187)
                ·
                  refine ⟨24346161710878775134213781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16230774473919183422809187 24346161710878775134213781)
                  ·
                    refine ⟨1141226330197442584416271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24346161710878775134213781 1141226330197442584416271)
                    ·
                      rfl

theorem cell23_6667591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_6667591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667591 prefixEnd_6667591 := by exact prefixLift 6667591
  have htrace : WordTrace (prefixWord ++ tailWord_6667591) baseStart_6667591 baseEnd_6667591 := by
    simpa [prefixWord, tailWord_6667591, baseEnd_6667591] using wordTrace_append hprefix tailTrace_6667591
  have hstable : (prefixWord ++ tailWord_6667591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667591).length < 2 ^ (prefixWord ++ tailWord_6667591).sum := by decide
  have hdescent : baseEnd_6667591 < baseStart_6667591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667598 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_6667598 : Nat := 118140960795 + 6667598 * 2 ^ 59
def prefixEnd_6667598 : Nat := 4983230072969 + 3 ^ 40 * 6667598 * 2
def baseEnd_6667598 : Nat := 3423682584956909225861281

theorem tailTrace_6667598 : CollatzResearch.WordTrace tailWord_6667598 prefixEnd_6667598 3423682584956909225861281 := by
  unfold tailWord_6667598
  simp only [CollatzResearch.WordTrace]
  refine ⟨30398409712304831990522431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162124851798959103949452965 30398409712304831990522431)
  ·
    refine ⟨45597614568457247985783647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30398409712304831990522431 45597614568457247985783647)
    ·
      refine ⟨68396421852685871978675471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45597614568457247985783647 68396421852685871978675471)
      ·
        refine ⟨102594632779028807968013207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68396421852685871978675471 102594632779028807968013207)
        ·
          refine ⟨153891949168543211952019811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102594632779028807968013207 153891949168543211952019811)
          ·
            refine ⟨230837923752814817928029717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153891949168543211952019811 230837923752814817928029717)
            ·
              refine ⟨10820527675913194590376393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 230837923752814817928029717 10820527675913194590376393)
              ·
                refine ⟨8115395756934895942782295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10820527675913194590376393 8115395756934895942782295)
                ·
                  refine ⟨12173093635402343914173443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8115395756934895942782295 12173093635402343914173443)
                  ·
                    refine ⟨18259640453103515871260165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12173093635402343914173443 18259640453103515871260165)
                    ·
                      refine ⟨3423682584956909225861281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18259640453103515871260165 3423682584956909225861281)
                      ·
                        rfl

theorem cell23_6667598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_6667598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667598 prefixEnd_6667598 := by exact prefixLift 6667598
  have htrace : WordTrace (prefixWord ++ tailWord_6667598) baseStart_6667598 baseEnd_6667598 := by
    simpa [prefixWord, tailWord_6667598, baseEnd_6667598] using wordTrace_append hprefix tailTrace_6667598
  have hstable : (prefixWord ++ tailWord_6667598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667598).length < 2 ^ (prefixWord ++ tailWord_6667598).sum := by decide
  have hdescent : baseEnd_6667598 < baseStart_6667598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667618 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6667618 : Nat := 118140960795 + 6667618 * 2 ^ 59
def prefixEnd_6667618 : Nat := 4983230072969 + 3 ^ 40 * 6667618 * 2
def baseEnd_6667618 : Nat := 3423692854569999147611189

theorem tailTrace_6667618 : CollatzResearch.WordTrace tailWord_6667618 prefixEnd_6667618 3423692854569999147611189 := by
  unfold tailWord_6667618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60797001789591549834976877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162125338105577466226605005 60797001789591549834976877)
  ·
    refine ⟨22798875671096831188116329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60797001789591549834976877 22798875671096831188116329)
    ·
      refine ⟨17099156753322623391087247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22798875671096831188116329 17099156753322623391087247)
      ·
        refine ⟨25648735129983935086630871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17099156753322623391087247 25648735129983935086630871)
        ·
          refine ⟨38473102694975902629946307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25648735129983935086630871 38473102694975902629946307)
          ·
            refine ⟨57709654042463853944919461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38473102694975902629946307 57709654042463853944919461)
            ·
              refine ⟨10820560132961972614672399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57709654042463853944919461 10820560132961972614672399)
              ·
                refine ⟨16230840199442958922008599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10820560132961972614672399 16230840199442958922008599)
                ·
                  refine ⟨24346260299164438383012899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16230840199442958922008599 24346260299164438383012899)
                  ·
                    refine ⟨36519390448746657574519349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24346260299164438383012899 36519390448746657574519349)
                    ·
                      refine ⟨3423692854569999147611189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36519390448746657574519349 3423692854569999147611189)
                      ·
                        rfl

theorem cell23_6667618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6667618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667618 prefixEnd_6667618 := by exact prefixLift 6667618
  have htrace : WordTrace (prefixWord ++ tailWord_6667618) baseStart_6667618 baseEnd_6667618 := by
    simpa [prefixWord, tailWord_6667618, baseEnd_6667618] using wordTrace_append hprefix tailTrace_6667618
  have hstable : (prefixWord ++ tailWord_6667618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667618).length < 2 ^ (prefixWord ++ tailWord_6667618).sum := by decide
  have hdescent : baseEnd_6667618 < baseStart_6667618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667682 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_6667682 : Nat := 118140960795 + 6667682 * 2 ^ 59
def prefixEnd_6667682 : Nat := 4983230072969 + 3 ^ 40 * 6667682 * 2
def baseEnd_6667682 : Nat := 3423725717331886897210895

theorem tailTrace_6667682 : CollatzResearch.WordTrace tailWord_6667682 prefixEnd_6667682 3423725717331886897210895 := by
  unfold tailWord_6667682
  simp only [CollatzResearch.WordTrace]
  refine ⟨60797585357533584567559325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162126894286756225513491533 60797585357533584567559325)
  ·
    refine ⟨22799094509075094212834747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60797585357533584567559325 22799094509075094212834747)
    ·
      refine ⟨34198641763612641319252121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22799094509075094212834747 34198641763612641319252121)
      ·
        refine ⟨25648981322709480989439091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34198641763612641319252121 25648981322709480989439091)
        ·
          refine ⟨38473471984064221484158637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25648981322709480989439091 38473471984064221484158637)
          ·
            refine ⟨14427551994024083056559489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38473471984064221484158637 14427551994024083056559489)
            ·
              refine ⟨10820663995518062292419617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14427551994024083056559489 10820663995518062292419617)
              ·
                refine ⟨8115497996638546719314713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10820663995518062292419617 8115497996638546719314713)
                ·
                  refine ⟨6086623497478910039486035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8115497996638546719314713 6086623497478910039486035)
                  ·
                    refine ⟨9129935246218365059229053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6086623497478910039486035 9129935246218365059229053)
                    ·
                      refine ⟨3423725717331886897210895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129935246218365059229053 3423725717331886897210895)
                      ·
                        rfl

theorem cell23_6667682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_6667682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667682 prefixEnd_6667682 := by exact prefixLift 6667682
  have htrace : WordTrace (prefixWord ++ tailWord_6667682) baseStart_6667682 baseEnd_6667682 := by
    simpa [prefixWord, tailWord_6667682, baseEnd_6667682] using wordTrace_append hprefix tailTrace_6667682
  have hstable : (prefixWord ++ tailWord_6667682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667682).length < 2 ^ (prefixWord ++ tailWord_6667682).sum := by decide
  have hdescent : baseEnd_6667682 < baseStart_6667682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667721 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_6667721 : Nat := 118140960795 + 6667721 * 2 ^ 59
def prefixEnd_6667721 : Nat := 4983230072969 + 3 ^ 40 * 6667721 * 2
def baseEnd_6667721 : Nat := 3423745743077412244623215

theorem tailTrace_6667721 : CollatzResearch.WordTrace tailWord_6667721 prefixEnd_6667721 3423745743077412244623215 := by
  unfold tailWord_6667721
  simp only [CollatzResearch.WordTrace]
  refine ⟨243191763876993047930907017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162127842584662031953938011 243191763876993047930907017)
  ·
    refine ⟨182393822907744785948180263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243191763876993047930907017 182393822907744785948180263)
    ·
      refine ⟨273590734361617178922270395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182393822907744785948180263 273590734361617178922270395)
      ·
        refine ⟨410386101542425768383405593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273590734361617178922270395 410386101542425768383405593)
        ·
          refine ⟨307789576156819326287554195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410386101542425768383405593 307789576156819326287554195)
          ·
            refine ⟨461684364235228989431331293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307789576156819326287554195 461684364235228989431331293)
            ·
              refine ⟨173131636588210871036749235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461684364235228989431331293 173131636588210871036749235)
              ·
                refine ⟨259697454882316306555123853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173131636588210871036749235 259697454882316306555123853)
                ·
                  refine ⟨97386545580868614958171445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259697454882316306555123853 97386545580868614958171445)
                  ·
                    refine ⟨9129988648206432652328573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97386545580868614958171445 9129988648206432652328573)
                    ·
                      refine ⟨3423745743077412244623215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9129988648206432652328573 3423745743077412244623215)
                      ·
                        rfl

theorem cell23_6667721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_6667721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667721 prefixEnd_6667721 := by exact prefixLift 6667721
  have htrace : WordTrace (prefixWord ++ tailWord_6667721) baseStart_6667721 baseEnd_6667721 := by
    simpa [prefixWord, tailWord_6667721, baseEnd_6667721] using wordTrace_append hprefix tailTrace_6667721
  have hstable : (prefixWord ++ tailWord_6667721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667721).length < 2 ^ (prefixWord ++ tailWord_6667721).sum := by decide
  have hdescent : baseEnd_6667721 < baseStart_6667721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667738 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_6667738 : Nat := 118140960795 + 6667738 * 2 ^ 59
def prefixEnd_6667738 : Nat := 4983230072969 + 3 ^ 40 * 6667738 * 2
def baseEnd_6667738 : Nat := 3423754472248538678110637

theorem tailTrace_6667738 : CollatzResearch.WordTrace tailWord_6667738 prefixEnd_6667738 3423754472248538678110637 := by
  unfold tailWord_6667738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60798095979482864958568967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162128255945287639889517245 60798095979482864958568967)
  ·
    refine ⟨91197143969224297437853451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60798095979482864958568967 91197143969224297437853451)
    ·
      refine ⟨136795715953836446156780177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91197143969224297437853451 136795715953836446156780177)
      ·
        refine ⟨102596786965377334617585133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136795715953836446156780177 102596786965377334617585133)
        ·
          refine ⟨38473795112016500481594425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102596786965377334617585133 38473795112016500481594425)
          ·
            refine ⟨28855346334012375361195819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38473795112016500481594425 28855346334012375361195819)
            ·
              refine ⟨43283019501018563041793729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28855346334012375361195819 43283019501018563041793729)
              ·
                refine ⟨32462264625763922281345297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43283019501018563041793729 32462264625763922281345297)
                ·
                  refine ⟨24346698469322941711008973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32462264625763922281345297 24346698469322941711008973)
                  ·
                    refine ⟨9130011925996103141628365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24346698469322941711008973 9130011925996103141628365)
                    ·
                      refine ⟨3423754472248538678110637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9130011925996103141628365 3423754472248538678110637)
                      ·
                        rfl

theorem cell23_6667738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_6667738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667738 prefixEnd_6667738 := by exact prefixLift 6667738
  have htrace : WordTrace (prefixWord ++ tailWord_6667738) baseStart_6667738 baseEnd_6667738 := by
    simpa [prefixWord, tailWord_6667738, baseEnd_6667738] using wordTrace_append hprefix tailTrace_6667738
  have hstable : (prefixWord ++ tailWord_6667738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667738).length < 2 ^ (prefixWord ++ tailWord_6667738).sum := by decide
  have hdescent : baseEnd_6667738 < baseStart_6667738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667748 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_6667748 : Nat := 118140960795 + 6667748 * 2 ^ 59
def prefixEnd_6667748 : Nat := 4983230072969 + 3 ^ 40 * 6667748 * 2
def baseEnd_6667748 : Nat := 3423759607055083638985591

theorem tailTrace_6667748 : CollatzResearch.WordTrace tailWord_6667748 prefixEnd_6667748 3423759607055083638985591 := by
  unfold tailWord_6667748
  simp only [CollatzResearch.WordTrace]
  refine ⟨121596374323947615771069949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162128499098596821028093265 121596374323947615771069949)
  ·
    refine ⟨45598640371480355914151231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121596374323947615771069949 45598640371480355914151231)
    ·
      refine ⟨68397960557220533871226847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45598640371480355914151231 68397960557220533871226847)
      ·
        refine ⟨102596940835830800806840271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68397960557220533871226847 102596940835830800806840271)
        ·
          refine ⟨153895411253746201210260407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102596940835830800806840271 153895411253746201210260407)
          ·
            refine ⟨230843116880619301815390611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153895411253746201210260407 230843116880619301815390611)
            ·
              refine ⟨346264675320928952723085917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230843116880619301815390611 346264675320928952723085917)
              ·
                refine ⟨129849253245348357271157219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346264675320928952723085917 129849253245348357271157219)
                ·
                  refine ⟨194773879868022535906735829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129849253245348357271157219 194773879868022535906735829)
                  ·
                    refine ⟨4565012809406778185314121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 194773879868022535906735829 4565012809406778185314121)
                    ·
                      refine ⟨3423759607055083638985591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565012809406778185314121 3423759607055083638985591)
                      ·
                        rfl

theorem cell23_6667748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_6667748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667748 prefixEnd_6667748 := by exact prefixLift 6667748
  have htrace : WordTrace (prefixWord ++ tailWord_6667748) baseStart_6667748 baseEnd_6667748 := by
    simpa [prefixWord, tailWord_6667748, baseEnd_6667748] using wordTrace_append hprefix tailTrace_6667748
  have hstable : (prefixWord ++ tailWord_6667748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667748).length < 2 ^ (prefixWord ++ tailWord_6667748).sum := by decide
  have hdescent : baseEnd_6667748 < baseStart_6667748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667781 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_6667781 : Nat := 118140960795 + 6667781 * 2 ^ 59
def prefixEnd_6667781 : Nat := 4983230072969 + 3 ^ 40 * 6667781 * 2
def baseEnd_6667781 : Nat := 3423776551916682009872939

theorem tailTrace_6667781 : CollatzResearch.WordTrace tailWord_6667781 prefixEnd_6667781 3423776551916682009872939 := by
  unfold tailWord_6667781
  simp only [CollatzResearch.WordTrace]
  refine ⟨243193952256775678178091197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162129301504517118785394131 243193952256775678178091197)
  ·
    refine ⟨91197732096290879316784199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243193952256775678178091197 91197732096290879316784199)
    ·
      refine ⟨136796598144436318975176299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91197732096290879316784199 136796598144436318975176299)
      ·
        refine ⟨205194897216654478462764449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136796598144436318975176299 205194897216654478462764449)
        ·
          refine ⟨153896172912490858847073337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205194897216654478462764449 153896172912490858847073337)
          ·
            refine ⟨115422129684368144135305003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153896172912490858847073337 115422129684368144135305003)
            ·
              refine ⟨173133194526552216202957505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115422129684368144135305003 173133194526552216202957505)
              ·
                refine ⟨129849895894914162152218129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173133194526552216202957505 129849895894914162152218129)
                ·
                  refine ⟨97387421921185621614163597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129849895894914162152218129 97387421921185621614163597)
                  ·
                    refine ⟨36520283220444608105311349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97387421921185621614163597 36520283220444608105311349)
                    ·
                      refine ⟨3423776551916682009872939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36520283220444608105311349 3423776551916682009872939)
                      ·
                        rfl

theorem cell23_6667781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_6667781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667781 prefixEnd_6667781 := by exact prefixLift 6667781
  have htrace : WordTrace (prefixWord ++ tailWord_6667781) baseStart_6667781 baseEnd_6667781 := by
    simpa [prefixWord, tailWord_6667781, baseEnd_6667781] using wordTrace_append hprefix tailTrace_6667781
  have hstable : (prefixWord ++ tailWord_6667781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667781).length < 2 ^ (prefixWord ++ tailWord_6667781).sum := by decide
  have hdescent : baseEnd_6667781 < baseStart_6667781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667791 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_6667791 : Nat := 118140960795 + 6667791 * 2 ^ 59
def prefixEnd_6667791 : Nat := 4983230072969 + 3 ^ 40 * 6667791 * 2
def baseEnd_6667791 : Nat := 3423781686723226970747893

theorem tailTrace_6667791 : CollatzResearch.WordTrace tailWord_6667791 prefixEnd_6667791 3423781686723226970747893 := by
  unfold tailWord_6667791
  simp only [CollatzResearch.WordTrace]
  refine ⟨243194316986739449885955227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162129544657826299923970151 243194316986739449885955227)
  ·
    refine ⟨364791475480109174828932841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243194316986739449885955227 364791475480109174828932841)
    ·
      refine ⟨273593606610081881121699631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364791475480109174828932841 273593606610081881121699631)
      ·
        refine ⟨410390409915122821682549447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273593606610081881121699631 410390409915122821682549447)
        ·
          refine ⟨615585614872684232523824171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410390409915122821682549447 615585614872684232523824171)
          ·
            refine ⟨923378422309026348785736257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615585614872684232523824171 923378422309026348785736257)
            ·
              refine ⟨692533816731769761589302193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923378422309026348785736257 692533816731769761589302193)
              ·
                refine ⟨519400362548827321191976645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692533816731769761589302193 519400362548827321191976645)
                ·
                  refine ⟨97387567977905122723495621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519400362548827321191976645 97387567977905122723495621)
                  ·
                    refine ⟨18260168995857210510655429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97387567977905122723495621 18260168995857210510655429)
                    ·
                      refine ⟨3423781686723226970747893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18260168995857210510655429 3423781686723226970747893)
                      ·
                        rfl

theorem cell23_6667791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_6667791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667791 prefixEnd_6667791 := by exact prefixLift 6667791
  have htrace : WordTrace (prefixWord ++ tailWord_6667791) baseStart_6667791 baseEnd_6667791 := by
    simpa [prefixWord, tailWord_6667791, baseEnd_6667791] using wordTrace_append hprefix tailTrace_6667791
  have hstable : (prefixWord ++ tailWord_6667791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667791).length < 2 ^ (prefixWord ++ tailWord_6667791).sum := by decide
  have hdescent : baseEnd_6667791 < baseStart_6667791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667898 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_6667898 : Nat := 118140960795 + 6667898 * 2 ^ 59
def prefixEnd_6667898 : Nat := 4983230072969 + 3 ^ 40 * 6667898 * 2
def baseEnd_6667898 : Nat := 3423836629153258052109901

theorem tailTrace_6667898 : CollatzResearch.WordTrace tailWord_6667898 prefixEnd_6667898 3423836629153258052109901 := by
  unfold tailWord_6667898
  simp only [CollatzResearch.WordTrace]
  refine ⟨60799554899337951790025087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162132146398234538106733565 60799554899337951790025087)
  ·
    refine ⟨91199332349006927685037631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60799554899337951790025087 91199332349006927685037631)
    ·
      refine ⟨136798998523510391527556447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91199332349006927685037631 136798998523510391527556447)
      ·
        refine ⟨205198497785265587291334671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136798998523510391527556447 205198497785265587291334671)
        ·
          refine ⟨307797746677898380937002007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205198497785265587291334671 307797746677898380937002007)
          ·
            refine ⟨461696620016847571405503011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307797746677898380937002007 461696620016847571405503011)
            ·
              refine ⟨692544930025271357108254517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461696620016847571405503011 692544930025271357108254517)
              ·
                refine ⟨64926087189869189728898861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692544930025271357108254517 64926087189869189728898861)
                ·
                  refine ⟨24347282696200946148337073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64926087189869189728898861 24347282696200946148337073)
                  ·
                    refine ⟨18260462022150709611252805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24347282696200946148337073 18260462022150709611252805)
                    ·
                      refine ⟨3423836629153258052109901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18260462022150709611252805 3423836629153258052109901)
                      ·
                        rfl

theorem cell23_6667898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_6667898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667898 prefixEnd_6667898 := by exact prefixLift 6667898
  have htrace : WordTrace (prefixWord ++ tailWord_6667898) baseStart_6667898 baseEnd_6667898 := by
    simpa [prefixWord, tailWord_6667898, baseEnd_6667898] using wordTrace_append hprefix tailTrace_6667898
  have hstable : (prefixWord ++ tailWord_6667898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667898).length < 2 ^ (prefixWord ++ tailWord_6667898).sum := by decide
  have hdescent : baseEnd_6667898 < baseStart_6667898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667922 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6667922 : Nat := 118140960795 + 6667922 * 2 ^ 59
def prefixEnd_6667922 : Nat := 4983230072969 + 3 ^ 40 * 6667922 * 2
def baseEnd_6667922 : Nat := 3423848952688965958209791

theorem tailTrace_6667922 : CollatzResearch.WordTrace tailWord_6667922 prefixEnd_6667922 3423848952688965958209791 := by
  unfold tailWord_6667922
  simp only [CollatzResearch.WordTrace]
  refine ⟨60799773737316214814743505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162132729966176572839316013 60799773737316214814743505)
  ·
    refine ⟨45599830302987161111057629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60799773737316214814743505 45599830302987161111057629)
    ·
      refine ⟨17099936363620185416646611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45599830302987161111057629 17099936363620185416646611)
      ·
        refine ⟨25649904545430278124969917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17099936363620185416646611 25649904545430278124969917)
        ·
          refine ⟨9618714204536354296863719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25649904545430278124969917 9618714204536354296863719)
          ·
            refine ⟨14428071306804531445295579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618714204536354296863719 14428071306804531445295579)
            ·
              refine ⟨21642106960206797167943369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14428071306804531445295579 21642106960206797167943369)
              ·
                refine ⟨16231580220155097875957527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21642106960206797167943369 16231580220155097875957527)
                ·
                  refine ⟨24347370330232646813936291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16231580220155097875957527 24347370330232646813936291)
                  ·
                    refine ⟨36521055495348970220904437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24347370330232646813936291 36521055495348970220904437)
                    ·
                      refine ⟨3423848952688965958209791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36521055495348970220904437 3423848952688965958209791)
                      ·
                        rfl

theorem cell23_6667922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6667922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667922 prefixEnd_6667922 := by exact prefixLift 6667922
  have htrace : WordTrace (prefixWord ++ tailWord_6667922) baseStart_6667922 baseEnd_6667922 := by
    simpa [prefixWord, tailWord_6667922, baseEnd_6667922] using wordTrace_append hprefix tailTrace_6667922
  have hstable : (prefixWord ++ tailWord_6667922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667922).length < 2 ^ (prefixWord ++ tailWord_6667922).sum := by decide
  have hdescent : baseEnd_6667922 < baseStart_6667922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667986 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_6667986 : Nat := 118140960795 + 6667986 * 2 ^ 59
def prefixEnd_6667986 : Nat := 4983230072969 + 3 ^ 40 * 6667986 * 2
def baseEnd_6667986 : Nat := 3423881815450853707809497

theorem tailTrace_6667986 : CollatzResearch.WordTrace tailWord_6667986 prefixEnd_6667986 3423881815450853707809497 := by
  unfold tailWord_6667986
  simp only [CollatzResearch.WordTrace]
  refine ⟨60800357305258249547325953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162134286147355332126202541 60800357305258249547325953)
  ·
    refine ⟨45600267978943687160494465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60800357305258249547325953 45600267978943687160494465)
    ·
      refine ⟨34200200984207765370370849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45600267978943687160494465 34200200984207765370370849)
      ·
        refine ⟨25650150738155824027778137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34200200984207765370370849 25650150738155824027778137)
        ·
          refine ⟨19237613053616868020833603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25650150738155824027778137 19237613053616868020833603)
          ·
            refine ⟨28856419580425302031250405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19237613053616868020833603 28856419580425302031250405)
            ·
              refine ⟨5410578671329744130859451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28856419580425302031250405 5410578671329744130859451)
              ·
                refine ⟨8115868006994616196289177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410578671329744130859451 8115868006994616196289177)
                ·
                  refine ⟨6086901005245962147216883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8115868006994616196289177 6086901005245962147216883)
                  ·
                    refine ⟨9130351507868943220825325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6086901005245962147216883 9130351507868943220825325)
                    ·
                      refine ⟨3423881815450853707809497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9130351507868943220825325 3423881815450853707809497)
                      ·
                        rfl

theorem cell23_6667986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_6667986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667986 prefixEnd_6667986 := by exact prefixLift 6667986
  have htrace : WordTrace (prefixWord ++ tailWord_6667986) baseStart_6667986 baseEnd_6667986 := by
    simpa [prefixWord, tailWord_6667986, baseEnd_6667986] using wordTrace_append hprefix tailTrace_6667986
  have hstable : (prefixWord ++ tailWord_6667986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667986).length < 2 ^ (prefixWord ++ tailWord_6667986).sum := by decide
  have hdescent : baseEnd_6667986 < baseStart_6667986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667990 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6667990 : Nat := 118140960795 + 6667990 * 2 ^ 59
def prefixEnd_6667990 : Nat := 4983230072969 + 3 ^ 40 * 6667990 * 2
def baseEnd_6667990 : Nat := 3423883869373471692159479

theorem tailTrace_6667990 : CollatzResearch.WordTrace tailWord_6667990 prefixEnd_6667990 3423883869373471692159479 := by
  unfold tailWord_6667990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15200098444563656679528089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162134383408679004581632949 15200098444563656679528089)
  ·
    refine ⟨11400073833422742509646067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15200098444563656679528089 11400073833422742509646067)
    ·
      refine ⟨17100110750134113764469101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11400073833422742509646067 17100110750134113764469101)
      ·
        refine ⟨6412541531300292661675913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17100110750134113764469101 6412541531300292661675913)
        ·
          refine ⟨4809406148475219496256935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6412541531300292661675913 4809406148475219496256935)
          ·
            refine ⟨7214109222712829244385403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809406148475219496256935 7214109222712829244385403)
            ·
              refine ⟨10821163834069243866578105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214109222712829244385403 10821163834069243866578105)
              ·
                refine ⟨8115872875551932899933579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10821163834069243866578105 8115872875551932899933579)
                ·
                  refine ⟨12173809313327899349900369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8115872875551932899933579 12173809313327899349900369)
                  ·
                    refine ⟨9130356984995924512425277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12173809313327899349900369 9130356984995924512425277)
                    ·
                      refine ⟨3423883869373471692159479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9130356984995924512425277 3423883869373471692159479)
                      ·
                        rfl

theorem cell23_6667990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6667990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667990 prefixEnd_6667990 := by exact prefixLift 6667990
  have htrace : WordTrace (prefixWord ++ tailWord_6667990) baseStart_6667990 baseEnd_6667990 := by
    simpa [prefixWord, tailWord_6667990, baseEnd_6667990] using wordTrace_append hprefix tailTrace_6667990
  have hstable : (prefixWord ++ tailWord_6667990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667990).length < 2 ^ (prefixWord ++ tailWord_6667990).sum := by decide
  have hdescent : baseEnd_6667990 < baseStart_6667990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667992 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 1, 4, 2]
def baseStart_6667992 : Nat := 118140960795 + 6667992 * 2 ^ 59
def prefixEnd_6667992 : Nat := 4983230072969 + 3 ^ 40 * 6667992 * 2
def baseEnd_6667992 : Nat := 3423884896334780684334469

theorem tailTrace_6667992 : CollatzResearch.WordTrace tailWord_6667992 prefixEnd_6667992 3423884896334780684334469 := by
  unfold tailWord_6667992
  simp only [CollatzResearch.WordTrace]
  refine ⟨121600824029505630607011115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162134432039340840809348153 121600824029505630607011115)
  ·
    refine ⟨182401236044258445910516673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121600824029505630607011115 182401236044258445910516673)
    ·
      refine ⟨136800927033193834432887505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182401236044258445910516673 136800927033193834432887505)
      ·
        refine ⟨102600695274895375824665629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136800927033193834432887505 102600695274895375824665629)
        ·
          refine ⟨38475260728085765934249611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102600695274895375824665629 38475260728085765934249611)
          ·
            refine ⟨57712891092128648901374417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38475260728085765934249611 57712891092128648901374417)
            ·
              refine ⟨43284668319096486676030813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57712891092128648901374417 43284668319096486676030813)
              ·
                refine ⟨16231750619661182503511555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43284668319096486676030813 16231750619661182503511555)
                ·
                  refine ⟨24347625929491773755267333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16231750619661182503511555 24347625929491773755267333)
                  ·
                    refine ⟨4565179861779707579112625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24347625929491773755267333 4565179861779707579112625)
                    ·
                      refine ⟨3423884896334780684334469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565179861779707579112625 3423884896334780684334469)
                      ·
                        rfl

theorem cell23_6667992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_6667992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667992 prefixEnd_6667992 := by exact prefixLift 6667992
  have htrace : WordTrace (prefixWord ++ tailWord_6667992) baseStart_6667992 baseEnd_6667992 := by
    simpa [prefixWord, tailWord_6667992, baseEnd_6667992] using wordTrace_append hprefix tailTrace_6667992
  have hstable : (prefixWord ++ tailWord_6667992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667992).length < 2 ^ (prefixWord ++ tailWord_6667992).sum := by decide
  have hdescent : baseEnd_6667992 < baseStart_6667992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6667996 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6667996 : Nat := 118140960795 + 6667996 * 2 ^ 59
def prefixEnd_6667996 : Nat := 4983230072969 + 3 ^ 40 * 6667996 * 2
def baseEnd_6667996 : Nat := 3423886950257398668684451

theorem tailTrace_6667996 : CollatzResearch.WordTrace tailWord_6667996 prefixEnd_6667996 3423886950257398668684451 := by
  unfold tailWord_6667996
  simp only [CollatzResearch.WordTrace]
  refine ⟨121600896975498384948583921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162134529300664513264778561 121600896975498384948583921)
  ·
    refine ⟨91200672731623788711437941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121600896975498384948583921 91200672731623788711437941)
    ·
      refine ⟨8550063068589730191697307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91200672731623788711437941 8550063068589730191697307)
      ·
        refine ⟨12825094602884595287545961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8550063068589730191697307 12825094602884595287545961)
        ·
          refine ⟨9618820952163446465659471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12825094602884595287545961 9618820952163446465659471)
          ·
            refine ⟨14428231428245169698489207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618820952163446465659471 14428231428245169698489207)
            ·
              refine ⟨21642347142367754547733811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14428231428245169698489207 21642347142367754547733811)
              ·
                refine ⟨32463520713551631821600717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21642347142367754547733811 32463520713551631821600717)
                ·
                  refine ⟨12173820267581861933100269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32463520713551631821600717 12173820267581861933100269)
                  ·
                    refine ⟨4565182600343198224912601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12173820267581861933100269 4565182600343198224912601)
                    ·
                      refine ⟨3423886950257398668684451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565182600343198224912601 3423886950257398668684451)
                      ·
                        rfl

theorem cell23_6667996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6667996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6667996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6667996 prefixEnd_6667996 := by exact prefixLift 6667996
  have htrace : WordTrace (prefixWord ++ tailWord_6667996) baseStart_6667996 baseEnd_6667996 := by
    simpa [prefixWord, tailWord_6667996, baseEnd_6667996] using wordTrace_append hprefix tailTrace_6667996
  have hstable : (prefixWord ++ tailWord_6667996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6667996).length < 2 ^ (prefixWord ++ tailWord_6667996).sum := by decide
  have hdescent : baseEnd_6667996 < baseStart_6667996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6667996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668042 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_6668042 : Nat := 118140960795 + 6668042 * 2 ^ 59
def prefixEnd_6668042 : Nat := 4983230072969 + 3 ^ 40 * 6668042 * 2
def baseEnd_6668042 : Nat := 3423910570367505488709239

theorem tailTrace_6668042 : CollatzResearch.WordTrace tailWord_6668042 prefixEnd_6668042 3423910570367505488709239 := by
  unfold tailWord_6668042
  simp only [CollatzResearch.WordTrace]
  refine ⟨60800867927207529938335595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162135647805886746502228253 60800867927207529938335595)
  ·
    refine ⟨91201301890811294907503393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60800867927207529938335595 91201301890811294907503393)
    ·
      refine ⟨68400976418108471180627545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91201301890811294907503393 68400976418108471180627545)
      ·
        refine ⟨51300732313581353385470659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68400976418108471180627545 51300732313581353385470659)
        ·
          refine ⟨76951098470372030078205989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51300732313581353385470659 76951098470372030078205989)
          ·
            refine ⟨14428330963194755639663623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76951098470372030078205989 14428330963194755639663623)
            ·
              refine ⟨21642496444792133459495435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14428330963194755639663623 21642496444792133459495435)
              ·
                refine ⟨32463744667188200189243153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21642496444792133459495435 32463744667188200189243153)
                ·
                  refine ⟨24347808500391150141932365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32463744667188200189243153 24347808500391150141932365)
                  ·
                    refine ⟨9130428187646681303224637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24347808500391150141932365 9130428187646681303224637)
                    ·
                      refine ⟨3423910570367505488709239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9130428187646681303224637 3423910570367505488709239)
                      ·
                        rfl

theorem cell23_6668042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_6668042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668042 prefixEnd_6668042 := by exact prefixLift 6668042
  have htrace : WordTrace (prefixWord ++ tailWord_6668042) baseStart_6668042 baseEnd_6668042 := by
    simpa [prefixWord, tailWord_6668042, baseEnd_6668042] using wordTrace_append hprefix tailTrace_6668042
  have hstable : (prefixWord ++ tailWord_6668042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668042).length < 2 ^ (prefixWord ++ tailWord_6668042).sum := by decide
  have hdescent : baseEnd_6668042 < baseStart_6668042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668092 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_6668092 : Nat := 118140960795 + 6668092 * 2 ^ 59
def prefixEnd_6668092 : Nat := 4983230072969 + 3 ^ 40 * 6668092 * 2
def baseEnd_6668092 : Nat := 1141312081466743431028003

theorem tailTrace_6668092 : CollatzResearch.WordTrace tailWord_6668092 prefixEnd_6668092 1141312081466743431028003 := by
  unfold tailWord_6668092
  simp only [CollatzResearch.WordTrace]
  refine ⟨121602647679324489146331265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162136863572432652195108353 121602647679324489146331265)
  ·
    refine ⟨91201985759493366859748449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121602647679324489146331265 91201985759493366859748449)
    ·
      refine ⟨68401489319620025144811337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91201985759493366859748449 68401489319620025144811337)
      ·
        refine ⟨51301116989715018858608503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68401489319620025144811337 51301116989715018858608503)
        ·
          refine ⟨76951675484572528287912755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51301116989715018858608503 76951675484572528287912755)
          ·
            refine ⟨115427513226858792431869133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76951675484572528287912755 115427513226858792431869133)
            ·
              refine ⟨43285317460072047161950925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115427513226858792431869133 43285317460072047161950925)
              ·
                refine ⟨16231994047527017685731597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43285317460072047161950925 16231994047527017685731597)
                ·
                  refine ⟨6086997767822631632149349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16231994047527017685731597 6086997767822631632149349)
                  ·
                    refine ⟨1141312081466743431028003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6086997767822631632149349 1141312081466743431028003)
                    ·
                      rfl

theorem cell23_6668092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_6668092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668092 prefixEnd_6668092 := by exact prefixLift 6668092
  have htrace : WordTrace (prefixWord ++ tailWord_6668092) baseStart_6668092 baseEnd_6668092 := by
    simpa [prefixWord, tailWord_6668092, baseEnd_6668092] using wordTrace_append hprefix tailTrace_6668092
  have hstable : (prefixWord ++ tailWord_6668092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668092).length < 2 ^ (prefixWord ++ tailWord_6668092).sum := by decide
  have hdescent : baseEnd_6668092 < baseStart_6668092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668155 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4]
def baseStart_6668155 : Nat := 118140960795 + 6668155 * 2 ^ 59
def prefixEnd_6668155 : Nat := 4983230072969 + 3 ^ 40 * 6668155 * 2
def baseEnd_6668155 : Nat := 3423968593681463546596219

theorem tailTrace_6668155 : CollatzResearch.WordTrace tailWord_6668155 prefixEnd_6668155 3423968593681463546596219 := by
  unfold tailWord_6668155
  simp only [CollatzResearch.WordTrace]
  refine ⟨243207593157420740052205919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162138395438280493368137279 243207593157420740052205919)
  ·
    refine ⟨364811389736131110078308879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243207593157420740052205919 364811389736131110078308879)
    ·
      refine ⟨547217084604196665117463319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364811389736131110078308879 547217084604196665117463319)
      ·
        refine ⟨820825626906294997676194979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547217084604196665117463319 820825626906294997676194979)
        ·
          refine ⟨1231238440359442496514292469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820825626906294997676194979 1231238440359442496514292469)
          ·
            refine ⟨115428603783697734048214919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1231238440359442496514292469 115428603783697734048214919)
            ·
              refine ⟨173142905675546601072322379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115428603783697734048214919 173142905675546601072322379)
              ·
                refine ⟨259714358513319901608483569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173142905675546601072322379 259714358513319901608483569)
                ·
                  refine ⟨194785768884989926206362677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259714358513319901608483569 194785768884989926206362677)
                  ·
                    refine ⟨18261165832967805581846501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194785768884989926206362677 18261165832967805581846501)
                    ·
                      refine ⟨3423968593681463546596219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18261165832967805581846501 3423968593681463546596219)
                      ·
                        rfl

theorem cell23_6668155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_6668155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668155 prefixEnd_6668155 := by exact prefixLift 6668155
  have htrace : WordTrace (prefixWord ++ tailWord_6668155) baseStart_6668155 baseEnd_6668155 := by
    simpa [prefixWord, tailWord_6668155, baseEnd_6668155] using wordTrace_append hprefix tailTrace_6668155
  have hstable : (prefixWord ++ tailWord_6668155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668155).length < 2 ^ (prefixWord ++ tailWord_6668155).sum := by decide
  have hdescent : baseEnd_6668155 < baseStart_6668155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668186 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_6668186 : Nat := 118140960795 + 6668186 * 2 ^ 59
def prefixEnd_6668186 : Nat := 4983230072969 + 3 ^ 40 * 6668186 * 2
def baseEnd_6668186 : Nat := 1141328170527250975102859

theorem tailTrace_6668186 : CollatzResearch.WordTrace tailWord_6668186 prefixEnd_6668186 1141328170527250975102859 := by
  unfold tailWord_6668186
  simp only [CollatzResearch.WordTrace]
  refine ⟨60802180955077108086646103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162139149213538954897722941 60802180955077108086646103)
  ·
    refine ⟨91203271432615662129969155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60802180955077108086646103 91203271432615662129969155)
    ·
      refine ⟨136804907148923493194953733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91203271432615662129969155 136804907148923493194953733)
      ·
        refine ⟨25650920090423154974053825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136804907148923493194953733 25650920090423154974053825)
        ·
          refine ⟨19238190067817366230540369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25650920090423154974053825 19238190067817366230540369)
          ·
            refine ⟨14428642550863024672905277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19238190067817366230540369 14428642550863024672905277)
            ·
              refine ⟨5410740956573634252339479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14428642550863024672905277 5410740956573634252339479)
              ·
                refine ⟨8116111434860451378509219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410740956573634252339479 8116111434860451378509219)
                ·
                  refine ⟨12174167152290677067763829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8116111434860451378509219 12174167152290677067763829)
                  ·
                    refine ⟨1141328170527250975102859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12174167152290677067763829 1141328170527250975102859)
                    ·
                      rfl

theorem cell23_6668186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_6668186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668186 prefixEnd_6668186 := by exact prefixLift 6668186
  have htrace : WordTrace (prefixWord ++ tailWord_6668186) baseStart_6668186 baseEnd_6668186 := by
    simpa [prefixWord, tailWord_6668186, baseEnd_6668186] using wordTrace_append hprefix tailTrace_6668186
  have hstable : (prefixWord ++ tailWord_6668186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668186).length < 2 ^ (prefixWord ++ tailWord_6668186).sum := by decide
  have hdescent : baseEnd_6668186 < baseStart_6668186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668209 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6668209 : Nat := 118140960795 + 6668209 * 2 ^ 59
def prefixEnd_6668209 : Nat := 4983230072969 + 3 ^ 40 * 6668209 * 2
def baseEnd_6668209 : Nat := 3423996321636806335320971

theorem tailTrace_6668209 : CollatzResearch.WordTrace tailWord_6668209 prefixEnd_6668209 3423996321636806335320971 := by
  unfold tailWord_6668209
  simp only [CollatzResearch.WordTrace]
  refine ⟨243209562699225107274671681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162139708466150071516447787 243209562699225107274671681)
  ·
    refine ⟨182407172024418830456003761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243209562699225107274671681 182407172024418830456003761)
    ·
      refine ⟨136805379018314122842002821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182407172024418830456003761 136805379018314122842002821)
      ·
        refine ⟨25651008565933898032875529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136805379018314122842002821 25651008565933898032875529)
        ·
          refine ⟨19238256424450423524656647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25651008565933898032875529 19238256424450423524656647)
          ·
            refine ⟨28857384636675635286984971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19238256424450423524656647 28857384636675635286984971)
            ·
              refine ⟨43286076955013452930477457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28857384636675635286984971 43286076955013452930477457)
              ·
                refine ⟨32464557716260089697858093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43286076955013452930477457 32464557716260089697858093)
                ·
                  refine ⟨12174209143597533636696785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32464557716260089697858093 12174209143597533636696785)
                  ·
                    refine ⟨9130656857698150227522589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12174209143597533636696785 9130656857698150227522589)
                    ·
                      refine ⟨3423996321636806335320971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9130656857698150227522589 3423996321636806335320971)
                      ·
                        rfl

theorem cell23_6668209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6668209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668209 prefixEnd_6668209 := by exact prefixLift 6668209
  have htrace : WordTrace (prefixWord ++ tailWord_6668209) baseStart_6668209 baseEnd_6668209 := by
    simpa [prefixWord, tailWord_6668209, baseEnd_6668209] using wordTrace_append hprefix tailTrace_6668209
  have hstable : (prefixWord ++ tailWord_6668209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668209).length < 2 ^ (prefixWord ++ tailWord_6668209).sum := by decide
  have hdescent : baseEnd_6668209 < baseStart_6668209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668239 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 3]
def baseStart_6668239 : Nat := 118140960795 + 6668239 * 2 ^ 59
def prefixEnd_6668239 : Nat := 4983230072969 + 3 ^ 40 * 6668239 * 2
def baseEnd_6668239 : Nat := 3424011726056441217945833

theorem tailTrace_6668239 : CollatzResearch.WordTrace tailWord_6668239 prefixEnd_6668239 3424011726056441217945833 := by
  unfold tailWord_6668239
  simp only [CollatzResearch.WordTrace]
  refine ⟨243210656889116422398263771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162140437926077614932175847 243210656889116422398263771)
  ·
    refine ⟨364815985333674633597395657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243210656889116422398263771 364815985333674633597395657)
    ·
      refine ⟨273611989000255975198046743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364815985333674633597395657 273611989000255975198046743)
      ·
        refine ⟨410417983500383962797070115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273611989000255975198046743 410417983500383962797070115)
        ·
          refine ⟨615626975250575944195605173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410417983500383962797070115 615626975250575944195605173)
          ·
            refine ⟨57715028929741494768337985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 615626975250575944195605173 57715028929741494768337985)
            ·
              refine ⟨43286271697306121076253489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57715028929741494768337985 43286271697306121076253489)
              ·
                refine ⟨32464703772979590807190117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43286271697306121076253489 32464703772979590807190117)
                ·
                  refine ⟨6087131957433673276348147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32464703772979590807190117 6087131957433673276348147)
                  ·
                    refine ⟨9130697936150509914522221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6087131957433673276348147 9130697936150509914522221)
                    ·
                      refine ⟨3424011726056441217945833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9130697936150509914522221 3424011726056441217945833)
                      ·
                        rfl

theorem cell23_6668239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_6668239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668239 prefixEnd_6668239 := by exact prefixLift 6668239
  have htrace : WordTrace (prefixWord ++ tailWord_6668239) baseStart_6668239 baseEnd_6668239 := by
    simpa [prefixWord, tailWord_6668239, baseEnd_6668239] using wordTrace_append hprefix tailTrace_6668239
  have hstable : (prefixWord ++ tailWord_6668239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668239).length < 2 ^ (prefixWord ++ tailWord_6668239).sum := by decide
  have hdescent : baseEnd_6668239 < baseStart_6668239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668272 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_6668272 : Nat := 118140960795 + 6668272 * 2 ^ 59
def prefixEnd_6668272 : Nat := 4983230072969 + 3 ^ 40 * 6668272 * 2
def baseEnd_6668272 : Nat := 1141342890306013196277727

theorem tailTrace_6668272 : CollatzResearch.WordTrace tailWord_6668272 prefixEnd_6668272 1141342890306013196277727 := by
  unfold tailWord_6668272
  simp only [CollatzResearch.WordTrace]
  refine ⟨121605930248998434517107535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162141240331997912689476713 121605930248998434517107535)
  ·
    refine ⟨182408895373497651775661303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121605930248998434517107535 182408895373497651775661303)
    ·
      refine ⟨273613343060246477663491955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182408895373497651775661303 273613343060246477663491955)
      ·
        refine ⟨410420014590369716495237933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273613343060246477663491955 410420014590369716495237933)
        ·
          refine ⟨153907505471388643685714225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410420014590369716495237933 153907505471388643685714225)
          ·
            refine ⟨115430629103541482764285669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153907505471388643685714225 115430629103541482764285669)
            ·
              refine ⟨21643242956914028018303563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115430629103541482764285669 21643242956914028018303563)
              ·
                refine ⟨32464864435371042027455345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21643242956914028018303563 32464864435371042027455345)
                ·
                  refine ⟨24348648326528281520591509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32464864435371042027455345 24348648326528281520591509)
                  ·
                    refine ⟨1141342890306013196277727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24348648326528281520591509 1141342890306013196277727)
                    ·
                      rfl

theorem cell23_6668272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_6668272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668272 prefixEnd_6668272 := by exact prefixLift 6668272
  have htrace : WordTrace (prefixWord ++ tailWord_6668272) baseStart_6668272 baseEnd_6668272 := by
    simpa [prefixWord, tailWord_6668272, baseEnd_6668272] using wordTrace_append hprefix tailTrace_6668272
  have hstable : (prefixWord ++ tailWord_6668272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668272).length < 2 ^ (prefixWord ++ tailWord_6668272).sum := by decide
  have hdescent : baseEnd_6668272 < baseStart_6668272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668273 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 1, 3, 3]
def baseStart_6668273 : Nat := 118140960795 + 6668273 * 2 ^ 59
def prefixEnd_6668273 : Nat := 4983230072969 + 3 ^ 40 * 6668273 * 2
def baseEnd_6668273 : Nat := 3424029184398694084920677

theorem tailTrace_6668273 : CollatzResearch.WordTrace tailWord_6668273 prefixEnd_6668273 3424029184398694084920677 := by
  unfold tailWord_6668273
  simp only [CollatzResearch.WordTrace]
  refine ⟨243211896970993246205001473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162141264647328830803334315 243211896970993246205001473)
  ·
    refine ⟨182408922728244934653751105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243211896970993246205001473 182408922728244934653751105)
    ·
      refine ⟨136806692046183700990313329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182408922728244934653751105 136806692046183700990313329)
      ·
        refine ⟨102605019034637775742734997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136806692046183700990313329 102605019034637775742734997)
        ·
          refine ⟨4809610267248645737940703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102605019034637775742734997 4809610267248645737940703)
          ·
            refine ⟨7214415400872968606911055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809610267248645737940703 7214415400872968606911055)
            ·
              refine ⟨10821623101309452910366583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214415400872968606911055 10821623101309452910366583)
              ·
                refine ⟨16232434651964179365549875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10821623101309452910366583 16232434651964179365549875)
                ·
                  refine ⟨24348651977946269048324813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16232434651964179365549875 24348651977946269048324813)
                  ·
                    refine ⟨9130744491729850893121805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24348651977946269048324813 9130744491729850893121805)
                    ·
                      refine ⟨3424029184398694084920677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9130744491729850893121805 3424029184398694084920677)
                      ·
                        rfl

theorem cell23_6668273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_6668273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668273 prefixEnd_6668273 := by exact prefixLift 6668273
  have htrace : WordTrace (prefixWord ++ tailWord_6668273) baseStart_6668273 baseEnd_6668273 := by
    simpa [prefixWord, tailWord_6668273, baseEnd_6668273] using wordTrace_append hprefix tailTrace_6668273
  have hstable : (prefixWord ++ tailWord_6668273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668273).length < 2 ^ (prefixWord ++ tailWord_6668273).sum := by decide
  have hdescent : baseEnd_6668273 < baseStart_6668273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668296 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_6668296 : Nat := 118140960795 + 6668296 * 2 ^ 59
def prefixEnd_6668296 : Nat := 4983230072969 + 3 ^ 40 * 6668296 * 2
def baseEnd_6668296 : Nat := 3424040994453747494933071

theorem tailTrace_6668296 : CollatzResearch.WordTrace tailWord_6668296 prefixEnd_6668296 3424040994453747494933071 := by
  unfold tailWord_6668296
  simp only [CollatzResearch.WordTrace]
  refine ⟨121606367924954960566544371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162141823899939947422059161 121606367924954960566544371)
  ·
    refine ⟨182409551887432440849816557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121606367924954960566544371 182409551887432440849816557)
    ·
      refine ⟨68403581957787165318681209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182409551887432440849816557 68403581957787165318681209)
      ·
        refine ⟨51302686468340373989010907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68403581957787165318681209 51302686468340373989010907)
        ·
          refine ⟨76954029702510560983516361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51302686468340373989010907 76954029702510560983516361)
          ·
            refine ⟨57715522276882920737637271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76954029702510560983516361 57715522276882920737637271)
            ·
              refine ⟨86573283415324381106455907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57715522276882920737637271 86573283415324381106455907)
              ·
                refine ⟨129859925122986571659683861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86573283415324381106455907 129859925122986571659683861)
                ·
                  refine ⟨6087183990139995546547681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129859925122986571659683861 6087183990139995546547681)
                  ·
                    refine ⟨4565387992604996659910761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6087183990139995546547681 4565387992604996659910761)
                    ·
                      refine ⟨3424040994453747494933071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565387992604996659910761 3424040994453747494933071)
                      ·
                        rfl

theorem cell23_6668296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_6668296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668296 prefixEnd_6668296 := by exact prefixLift 6668296
  have htrace : WordTrace (prefixWord ++ tailWord_6668296) baseStart_6668296 baseEnd_6668296 := by
    simpa [prefixWord, tailWord_6668296, baseEnd_6668296] using wordTrace_append hprefix tailTrace_6668296
  have hstable : (prefixWord ++ tailWord_6668296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668296).length < 2 ^ (prefixWord ++ tailWord_6668296).sum := by decide
  have hdescent : baseEnd_6668296 < baseStart_6668296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668312 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6668312 : Nat := 118140960795 + 6668312 * 2 ^ 59
def prefixEnd_6668312 : Nat := 4983230072969 + 3 ^ 40 * 6668312 * 2
def baseEnd_6668312 : Nat := 3424049210144219432332997

theorem tailTrace_6668312 : CollatzResearch.WordTrace tailWord_6668312 prefixEnd_6668312 3424049210144219432332997 := by
  unfold tailWord_6668312
  simp only [CollatzResearch.WordTrace]
  refine ⟨121606659708925977932835595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162142212945234637243780793 121606659708925977932835595)
  ·
    refine ⟨182409989563388966899253393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121606659708925977932835595 182409989563388966899253393)
    ·
      refine ⟨136807492172541725174440045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182409989563388966899253393 136807492172541725174440045)
      ·
        refine ⟨51302809564703146940415017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136807492172541725174440045 51302809564703146940415017)
        ·
          refine ⟨38477107173527360205311263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51302809564703146940415017 38477107173527360205311263)
          ·
            refine ⟨57715660760291040307966895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38477107173527360205311263 57715660760291040307966895)
            ·
              refine ⟨86573491140436560461950343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57715660760291040307966895 86573491140436560461950343)
              ·
                refine ⟨129860236710654840692925515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86573491140436560461950343 129860236710654840692925515)
                ·
                  refine ⟨194790355065982261039388273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129860236710654840692925515 194790355065982261039388273)
                  ·
                    refine ⟨146092766299486695779541205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194790355065982261039388273 146092766299486695779541205)
                    ·
                      refine ⟨3424049210144219432332997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146092766299486695779541205 3424049210144219432332997)
                      ·
                        rfl

theorem cell23_6668312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6668312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668312 prefixEnd_6668312 := by exact prefixLift 6668312
  have htrace : WordTrace (prefixWord ++ tailWord_6668312) baseStart_6668312 baseEnd_6668312 := by
    simpa [prefixWord, tailWord_6668312, baseEnd_6668312] using wordTrace_append hprefix tailTrace_6668312
  have hstable : (prefixWord ++ tailWord_6668312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668312).length < 2 ^ (prefixWord ++ tailWord_6668312).sum := by decide
  have hdescent : baseEnd_6668312 < baseStart_6668312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668330 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_6668330 : Nat := 118140960795 + 6668330 * 2 ^ 59
def prefixEnd_6668330 : Nat := 4983230072969 + 3 ^ 40 * 6668330 * 2
def baseEnd_6668330 : Nat := 3424058452796000361907915

theorem tailTrace_6668330 : CollatzResearch.WordTrace tailWord_6668330 prefixEnd_6668330 3424058452796000361907915 := by
  unfold tailWord_6668330
  simp only [CollatzResearch.WordTrace]
  refine ⟨60803493982946686234956611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162142650621191163293217629 60803493982946686234956611)
  ·
    refine ⟨91205240974420029352434917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60803493982946686234956611 91205240974420029352434917)
    ·
      refine ⟨17100982682703755503581547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91205240974420029352434917 17100982682703755503581547)
      ·
        refine ⟨25651474024055633255372321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17100982682703755503581547 25651474024055633255372321)
        ·
          refine ⟨19238605518041724941529241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25651474024055633255372321 19238605518041724941529241)
          ·
            refine ⟨14428954138531293706146931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19238605518041724941529241 14428954138531293706146931)
            ·
              refine ⟨21643431207796940559220397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14428954138531293706146931 21643431207796940559220397)
              ·
                refine ⟨8116286702923852709707649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21643431207796940559220397 8116286702923852709707649)
                ·
                  refine ⟨6087215027192889532280737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8116286702923852709707649 6087215027192889532280737)
                  ·
                    refine ⟨4565411270394667149210553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6087215027192889532280737 4565411270394667149210553)
                    ·
                      refine ⟨3424058452796000361907915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565411270394667149210553 3424058452796000361907915)
                      ·
                        rfl

theorem cell23_6668330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_6668330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668330 prefixEnd_6668330 := by exact prefixLift 6668330
  have htrace : WordTrace (prefixWord ++ tailWord_6668330) baseStart_6668330 baseEnd_6668330 := by
    simpa [prefixWord, tailWord_6668330, baseEnd_6668330] using wordTrace_append hprefix tailTrace_6668330
  have hstable : (prefixWord ++ tailWord_6668330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668330).length < 2 ^ (prefixWord ++ tailWord_6668330).sum := by decide
  have hdescent : baseEnd_6668330 < baseStart_6668330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668332 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_6668332 : Nat := 118140960795 + 6668332 * 2 ^ 59
def prefixEnd_6668332 : Nat := 4983230072969 + 3 ^ 40 * 6668332 * 2
def baseEnd_6668332 : Nat := 1141353159919103118027635

theorem tailTrace_6668332 : CollatzResearch.WordTrace tailWord_6668332 prefixEnd_6668332 1141353159919103118027635 := by
  unfold tailWord_6668332
  simp only [CollatzResearch.WordTrace]
  refine ⟨121607024438889749640699625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162142699251852999520932833 121607024438889749640699625)
  ·
    refine ⟨91205268329167312230524719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121607024438889749640699625 91205268329167312230524719)
    ·
      refine ⟨136807902493750968345787079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91205268329167312230524719 136807902493750968345787079)
      ·
        refine ⟨205211853740626452518680619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136807902493750968345787079 205211853740626452518680619)
        ·
          refine ⟨307817780610939678778020929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205211853740626452518680619 307817780610939678778020929)
          ·
            refine ⟨230863335458204759083515697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307817780610939678778020929 230863335458204759083515697)
            ·
              refine ⟨173147501593653569312636773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230863335458204759083515697 173147501593653569312636773)
              ·
                refine ⟨32465156548810044246119395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173147501593653569312636773 32465156548810044246119395)
                ·
                  refine ⟨48697734823215066369179093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32465156548810044246119395 48697734823215066369179093)
                  ·
                    refine ⟨1141353159919103118027635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48697734823215066369179093 1141353159919103118027635)
                    ·
                      rfl

theorem cell23_6668332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_6668332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668332 prefixEnd_6668332 := by exact prefixLift 6668332
  have htrace : WordTrace (prefixWord ++ tailWord_6668332) baseStart_6668332 baseEnd_6668332 := by
    simpa [prefixWord, tailWord_6668332, baseEnd_6668332] using wordTrace_append hprefix tailTrace_6668332
  have hstable : (prefixWord ++ tailWord_6668332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668332).length < 2 ^ (prefixWord ++ tailWord_6668332).sum := by decide
  have hdescent : baseEnd_6668332 < baseStart_6668332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668370 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_6668370 : Nat := 118140960795 + 6668370 * 2 ^ 59
def prefixEnd_6668370 : Nat := 4983230072969 + 3 ^ 40 * 6668370 * 2
def baseEnd_6668370 : Nat := 380453221335797800600859

theorem tailTrace_6668370 : CollatzResearch.WordTrace tailWord_6668370 prefixEnd_6668370 380453221335797800600859 := by
  unfold tailWord_6668370
  simp only [CollatzResearch.WordTrace]
  refine ⟨60803858712910457942820641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162143623234427887847521709 60803858712910457942820641)
  ·
    refine ⟨45602894034682843457115481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60803858712910457942820641 45602894034682843457115481)
    ·
      refine ⟨34202170526012132592836611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45602894034682843457115481 34202170526012132592836611)
      ·
        refine ⟨51303255789018198889254917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34202170526012132592836611 51303255789018198889254917)
        ·
          refine ⟨9619360460440912291735297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51303255789018198889254917 9619360460440912291735297)
          ·
            refine ⟨7214520345330684218801473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9619360460440912291735297 7214520345330684218801473)
            ·
              refine ⟨5410890258998013164101105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7214520345330684218801473 5410890258998013164101105)
              ·
                refine ⟨4058167694248509873075829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5410890258998013164101105 4058167694248509873075829)
                ·
                  refine ⟨380453221335797800600859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4058167694248509873075829 380453221335797800600859)
                  ·
                    rfl

theorem cell23_6668370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_6668370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668370 prefixEnd_6668370 := by exact prefixLift 6668370
  have htrace : WordTrace (prefixWord ++ tailWord_6668370) baseStart_6668370 baseEnd_6668370 := by
    simpa [prefixWord, tailWord_6668370, baseEnd_6668370] using wordTrace_append hprefix tailTrace_6668370
  have hstable : (prefixWord ++ tailWord_6668370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668370).length < 2 ^ (prefixWord ++ tailWord_6668370).sum := by decide
  have hdescent : baseEnd_6668370 < baseStart_6668370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668396 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_6668396 : Nat := 118140960795 + 6668396 * 2 ^ 59
def prefixEnd_6668396 : Nat := 4983230072969 + 3 ^ 40 * 6668396 * 2
def baseEnd_6668396 : Nat := 1141364114173065701227537

theorem tailTrace_6668396 : CollatzResearch.WordTrace tailWord_6668396 prefixEnd_6668396 1141364114173065701227537 := by
  unfold tailWord_6668396
  simp only [CollatzResearch.WordTrace]
  refine ⟨121608191574773819105864521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162144255433031758807819361 121608191574773819105864521)
  ·
    refine ⟨91206143681080364329398391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121608191574773819105864521 91206143681080364329398391)
    ·
      refine ⟨136809215521620546494097587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91206143681080364329398391 136809215521620546494097587)
      ·
        refine ⟨205213823282430819741146381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136809215521620546494097587 205213823282430819741146381)
        ·
          refine ⟨76955183730911557402929893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205213823282430819741146381 76955183730911557402929893)
          ·
            refine ⟨14429096949545917013049355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76955183730911557402929893 14429096949545917013049355)
            ·
              refine ⟨21643645424318875519574033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14429096949545917013049355 21643645424318875519574033)
              ·
                refine ⟨16232734068239156639680525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21643645424318875519574033 16232734068239156639680525)
                ·
                  refine ⟨6087275275589683739880197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16232734068239156639680525 6087275275589683739880197)
                  ·
                    refine ⟨1141364114173065701227537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6087275275589683739880197 1141364114173065701227537)
                    ·
                      rfl

theorem cell23_6668396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_6668396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668396 prefixEnd_6668396 := by exact prefixLift 6668396
  have htrace : WordTrace (prefixWord ++ tailWord_6668396) baseStart_6668396 baseEnd_6668396 := by
    simpa [prefixWord, tailWord_6668396, baseEnd_6668396] using wordTrace_append hprefix tailTrace_6668396
  have hstable : (prefixWord ++ tailWord_6668396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668396).length < 2 ^ (prefixWord ++ tailWord_6668396).sum := by decide
  have hdescent : baseEnd_6668396 < baseStart_6668396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668413 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_6668413 : Nat := 118140960795 + 6668413 * 2 ^ 59
def prefixEnd_6668413 : Nat := 4983230072969 + 3 ^ 40 * 6668413 * 2
def baseEnd_6668413 : Nat := 1141367023896774512390011

theorem tailTrace_6668413 : CollatzResearch.WordTrace tailWord_6668413 prefixEnd_6668413 1141367023896774512390011 := by
  unfold tailWord_6668413
  simp only [CollatzResearch.WordTrace]
  refine ⟨243217003190486050115097893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162144668793657366743398595 243217003190486050115097893)
  ·
    refine ⟨45603188098216134396580855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243217003190486050115097893 45603188098216134396580855)
    ·
      refine ⟨68404782147324201594871283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45603188098216134396580855 68404782147324201594871283)
      ·
        refine ⟨102607173220986302392306925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68404782147324201594871283 102607173220986302392306925)
        ·
          refine ⟨38477689957869863397115097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102607173220986302392306925 38477689957869863397115097)
          ·
            refine ⟨28858267468402397547836323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38477689957869863397115097 28858267468402397547836323)
            ·
              refine ⟨43287401202603596321754485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28858267468402397547836323 43287401202603596321754485)
              ·
                refine ⟨4058193862744087155164483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43287401202603596321754485 4058193862744087155164483)
                ·
                  refine ⟨6087290794116130732746725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058193862744087155164483 6087290794116130732746725)
                  ·
                    refine ⟨1141367023896774512390011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6087290794116130732746725 1141367023896774512390011)
                    ·
                      rfl

theorem cell23_6668413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_6668413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668413 prefixEnd_6668413 := by exact prefixLift 6668413
  have htrace : WordTrace (prefixWord ++ tailWord_6668413) baseStart_6668413 baseEnd_6668413 := by
    simpa [prefixWord, tailWord_6668413, baseEnd_6668413] using wordTrace_append hprefix tailTrace_6668413
  have hstable : (prefixWord ++ tailWord_6668413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668413).length < 2 ^ (prefixWord ++ tailWord_6668413).sum := by decide
  have hdescent : baseEnd_6668413 < baseStart_6668413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668426 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_6668426 : Nat := 118140960795 + 6668426 * 2 ^ 59
def prefixEnd_6668426 : Nat := 4983230072969 + 3 ^ 40 * 6668426 * 2
def baseEnd_6668426 : Nat := 380456416326536887367497

theorem tailTrace_6668426 : CollatzResearch.WordTrace tailWord_6668426 prefixEnd_6668426 380456416326536887367497 := by
  unfold tailWord_6668426
  simp only [CollatzResearch.WordTrace]
  refine ⟨60804369334859738333830283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162144984892959302223547421 60804369334859738333830283)
  ·
    refine ⟨91206554002289607500745425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60804369334859738333830283 91206554002289607500745425)
    ·
      refine ⟨68404915501717205625559069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91206554002289607500745425 68404915501717205625559069)
      ·
        refine ⟨25651843313143952109584651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68404915501717205625559069 25651843313143952109584651)
        ·
          refine ⟨38477764969715928164376977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25651843313143952109584651 38477764969715928164376977)
          ·
            refine ⟨28858323727286946123282733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38477764969715928164376977 28858323727286946123282733)
            ·
              refine ⟨10821871397732604796231025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28858323727286946123282733 10821871397732604796231025)
              ·
                refine ⟨8116403548299453597173269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10821871397732604796231025 8116403548299453597173269)
                ·
                  refine ⟨380456416326536887367497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8116403548299453597173269 380456416326536887367497)
                  ·
                    rfl

theorem cell23_6668426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_6668426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668426 prefixEnd_6668426 := by exact prefixLift 6668426
  have htrace : WordTrace (prefixWord ++ tailWord_6668426) baseStart_6668426 baseEnd_6668426 := by
    simpa [prefixWord, tailWord_6668426, baseEnd_6668426] using wordTrace_append hprefix tailTrace_6668426
  have hstable : (prefixWord ++ tailWord_6668426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668426).length < 2 ^ (prefixWord ++ tailWord_6668426).sum := by decide
  have hdescent : baseEnd_6668426 < baseStart_6668426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668459 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 4]
def baseStart_6668459 : Nat := 118140960795 + 6668459 * 2 ^ 59
def prefixEnd_6668459 : Nat := 4983230072969 + 3 ^ 40 * 6668459 * 2
def baseEnd_6668459 : Nat := 3424124691800430357194821

theorem tailTrace_6668459 : CollatzResearch.WordTrace tailWord_6668459 prefixEnd_6668459 3424124691800430357194821 := by
  unfold tailWord_6668459
  simp only [CollatzResearch.WordTrace]
  refine ⟨243218680948319399971272431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162145787298879599980848287 243218680948319399971272431)
  ·
    refine ⟨364828021422479099956908647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243218680948319399971272431 364828021422479099956908647)
    ·
      refine ⟨547242032133718649935362971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364828021422479099956908647 547242032133718649935362971)
      ·
        refine ⟨820863048200577974903044457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547242032133718649935362971 820863048200577974903044457)
        ·
          refine ⟨615647286150433481177283343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820863048200577974903044457 615647286150433481177283343)
          ·
            refine ⟨923470929225650221765925015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615647286150433481177283343 923470929225650221765925015)
            ·
              refine ⟨1385206393838475332648887523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923470929225650221765925015 1385206393838475332648887523)
              ·
                refine ⟨2077809590757712998973331285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385206393838475332648887523 2077809590757712998973331285)
                ·
                  refine ⟨12174665570845974603359363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2077809590757712998973331285 12174665570845974603359363)
                  ·
                    refine ⟨18261998356268961905039045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12174665570845974603359363 18261998356268961905039045)
                    ·
                      refine ⟨3424124691800430357194821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18261998356268961905039045 3424124691800430357194821)
                      ·
                        rfl

theorem cell23_6668459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 4].length) (baseStart_6668459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668459 prefixEnd_6668459 := by exact prefixLift 6668459
  have htrace : WordTrace (prefixWord ++ tailWord_6668459) baseStart_6668459 baseEnd_6668459 := by
    simpa [prefixWord, tailWord_6668459, baseEnd_6668459] using wordTrace_append hprefix tailTrace_6668459
  have hstable : (prefixWord ++ tailWord_6668459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668459).length < 2 ^ (prefixWord ++ tailWord_6668459).sum := by decide
  have hdescent : baseEnd_6668459 < baseStart_6668459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668489 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_6668489 : Nat := 118140960795 + 6668489 * 2 ^ 59
def prefixEnd_6668489 : Nat := 4983230072969 + 3 ^ 40 * 6668489 * 2
def baseEnd_6668489 : Nat := 3424140096220065239819683

theorem tailTrace_6668489 : CollatzResearch.WordTrace tailWord_6668489 prefixEnd_6668489 3424140096220065239819683 := by
  unfold tailWord_6668489
  simp only [CollatzResearch.WordTrace]
  refine ⟨243219775138210715094864521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162146516758807143396576347 243219775138210715094864521)
  ·
    refine ⟨182414831353658036321148391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243219775138210715094864521 182414831353658036321148391)
    ·
      refine ⟨273622247030487054481722587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182414831353658036321148391 273622247030487054481722587)
      ·
        refine ⟨410433370545730581722583881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273622247030487054481722587 410433370545730581722583881)
        ·
          refine ⟨307825027909297936291937911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410433370545730581722583881 307825027909297936291937911)
          ·
            refine ⟨461737541863946904437906867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307825027909297936291937911 461737541863946904437906867)
            ·
              refine ⟨692606312795920356656860301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461737541863946904437906867 692606312795920356656860301)
              ·
                refine ⟨259727367298470133746322613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692606312795920356656860301 259727367298470133746322613)
                ·
                  refine ⟨24349440684231575038717745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259727367298470133746322613 24349440684231575038717745)
                  ·
                    refine ⟨18262080513173681279038309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24349440684231575038717745 18262080513173681279038309)
                    ·
                      refine ⟨3424140096220065239819683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18262080513173681279038309 3424140096220065239819683)
                      ·
                        rfl

theorem cell23_6668489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_6668489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668489 prefixEnd_6668489 := by exact prefixLift 6668489
  have htrace : WordTrace (prefixWord ++ tailWord_6668489) baseStart_6668489 baseEnd_6668489 := by
    simpa [prefixWord, tailWord_6668489, baseEnd_6668489] using wordTrace_append hprefix tailTrace_6668489
  have hstable : (prefixWord ++ tailWord_6668489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668489).length < 2 ^ (prefixWord ++ tailWord_6668489).sum := by decide
  have hdescent : baseEnd_6668489 < baseStart_6668489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668553 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 3, 3, 2]
def baseStart_6668553 : Nat := 118140960795 + 6668553 * 2 ^ 59
def prefixEnd_6668553 : Nat := 4983230072969 + 3 ^ 40 * 6668553 * 2
def baseEnd_6668553 : Nat := 3424172958981952989419389

theorem tailTrace_6668553 : CollatzResearch.WordTrace tailWord_6668553 prefixEnd_6668553 3424172958981952989419389 := by
  unfold tailWord_6668553
  simp only [CollatzResearch.WordTrace]
  refine ⟨243222109409978854025194313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162148072939985902683462875 243222109409978854025194313)
  ·
    refine ⟨182416582057484140518895735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243222109409978854025194313 182416582057484140518895735)
    ·
      refine ⟨273624873086226210778343603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182416582057484140518895735 273624873086226210778343603)
      ·
        refine ⟨410437309629339316167515405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273624873086226210778343603 410437309629339316167515405)
        ·
          refine ⟨153913991111002243562818277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410437309629339316167515405 153913991111002243562818277)
          ·
            refine ⟨28858873333312920668028427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153913991111002243562818277 28858873333312920668028427)
            ·
              refine ⟨43288309999969381002042641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28858873333312920668028427 43288309999969381002042641)
              ·
                refine ⟨32466232499977035751531981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43288309999969381002042641 32466232499977035751531981)
                ·
                  refine ⟨12174837187491388406824493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32466232499977035751531981 12174837187491388406824493)
                  ·
                    refine ⟨4565563945309270652559185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12174837187491388406824493 4565563945309270652559185)
                    ·
                      refine ⟨3424172958981952989419389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565563945309270652559185 3424172958981952989419389)
                      ·
                        rfl

theorem cell23_6668553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 3, 2].length) (baseStart_6668553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668553 prefixEnd_6668553 := by exact prefixLift 6668553
  have htrace : WordTrace (prefixWord ++ tailWord_6668553) baseStart_6668553 baseEnd_6668553 := by
    simpa [prefixWord, tailWord_6668553, baseEnd_6668553] using wordTrace_append hprefix tailTrace_6668553
  have hstable : (prefixWord ++ tailWord_6668553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668553).length < 2 ^ (prefixWord ++ tailWord_6668553).sum := by decide
  have hdescent : baseEnd_6668553 < baseStart_6668553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668594 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_6668594 : Nat := 118140960795 + 6668594 * 2 ^ 59
def prefixEnd_6668594 : Nat := 4983230072969 + 3 ^ 40 * 6668594 * 2
def baseEnd_6668594 : Nat := 3424194011688787329006701

theorem tailTrace_6668594 : CollatzResearch.WordTrace tailWord_6668594 prefixEnd_6668594 3424194011688787329006701 := by
  unfold tailWord_6668594
  simp only [CollatzResearch.WordTrace]
  refine ⟨60805901200707579506859209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162149069868553545351624557 60805901200707579506859209)
  ·
    refine ⟨45604425900530684630144407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60805901200707579506859209 45604425900530684630144407)
    ·
      refine ⟨68406638850796026945216611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45604425900530684630144407 68406638850796026945216611)
      ·
        refine ⟨102609958276194040417824917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68406638850796026945216611 102609958276194040417824917)
        ·
          refine ⟨4809841794196595644585543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102609958276194040417824917 4809841794196595644585543)
          ·
            refine ⟨7214762691294893466878315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809841794196595644585543 7214762691294893466878315)
            ·
              refine ⟨10822144036942340200317473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214762691294893466878315 10822144036942340200317473)
              ·
                refine ⟨8116608027706755150238105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10822144036942340200317473 8116608027706755150238105)
                ·
                  refine ⟨6087456020780066362678579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8116608027706755150238105 6087456020780066362678579)
                  ·
                    refine ⟨9131184031170099544017869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6087456020780066362678579 9131184031170099544017869)
                    ·
                      refine ⟨3424194011688787329006701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9131184031170099544017869 3424194011688787329006701)
                      ·
                        rfl

theorem cell23_6668594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_6668594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668594 prefixEnd_6668594 := by exact prefixLift 6668594
  have htrace : WordTrace (prefixWord ++ tailWord_6668594) baseStart_6668594 baseEnd_6668594 := by
    simpa [prefixWord, tailWord_6668594, baseEnd_6668594] using wordTrace_append hprefix tailTrace_6668594
  have hstable : (prefixWord ++ tailWord_6668594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668594).length < 2 ^ (prefixWord ++ tailWord_6668594).sum := by decide
  have hdescent : baseEnd_6668594 < baseStart_6668594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668653 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_6668653 : Nat := 118140960795 + 6668653 * 2 ^ 59
def prefixEnd_6668653 : Nat := 4983230072969 + 3 ^ 40 * 6668653 * 2
def baseEnd_6668653 : Nat := 1141408102349134199389643

theorem tailTrace_6668653 : CollatzResearch.WordTrace tailWord_6668653 prefixEnd_6668653 1141408102349134199389643 := by
  unfold tailWord_6668653
  simp only [CollatzResearch.WordTrace]
  refine ⟨243225756709616571103834613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162150504473077714069223075 243225756709616571103834613)
  ·
    refine ⟨22802414691526553540984495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243225756709616571103834613 22802414691526553540984495)
    ·
      refine ⟨34203622037289830311476743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22802414691526553540984495 34203622037289830311476743)
      ·
        refine ⟨51305433055934745467215115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34203622037289830311476743 51305433055934745467215115)
        ·
          refine ⟨76958149583902118200822673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51305433055934745467215115 76958149583902118200822673)
          ·
            refine ⟨57718612187926588650617005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76958149583902118200822673 57718612187926588650617005)
            ·
              refine ⟨21644479570472470743981377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57718612187926588650617005 21644479570472470743981377)
              ·
                refine ⟨16233359677854353057986033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21644479570472470743981377 16233359677854353057986033)
                ·
                  refine ⟨12175019758390764793489525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16233359677854353057986033 12175019758390764793489525)
                  ·
                    refine ⟨1141408102349134199389643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12175019758390764793489525 1141408102349134199389643)
                    ·
                      rfl

theorem cell23_6668653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_6668653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668653 prefixEnd_6668653 := by exact prefixLift 6668653
  have htrace : WordTrace (prefixWord ++ tailWord_6668653) baseStart_6668653 baseEnd_6668653 := by
    simpa [prefixWord, tailWord_6668653, baseEnd_6668653] using wordTrace_append hprefix tailTrace_6668653
  have hstable : (prefixWord ++ tailWord_6668653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668653).length < 2 ^ (prefixWord ++ tailWord_6668653).sum := by decide
  have hdescent : baseEnd_6668653 < baseStart_6668653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668716 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_6668716 : Nat := 118140960795 + 6668716 * 2 ^ 59
def prefixEnd_6668716 : Nat := 4983230072969 + 3 ^ 40 * 6668716 * 2
def baseEnd_6668716 : Nat := 3424256656328635851681139

theorem tailTrace_6668716 : CollatzResearch.WordTrace tailWord_6668716 prefixEnd_6668716 3424256656328635851681139 := by
  unfold tailWord_6668716
  simp only [CollatzResearch.WordTrace]
  refine ⟨121614027254194166431689001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162152036338925555242252001 121614027254194166431689001)
  ·
    refine ⟨91210520440645624823766751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121614027254194166431689001 91210520440645624823766751)
    ·
      refine ⟨136815780660968437235650127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91210520440645624823766751 136815780660968437235650127)
      ·
        refine ⟨205223670991452655853475191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136815780660968437235650127 205223670991452655853475191)
        ·
          refine ⟨307835506487178983780212787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205223670991452655853475191 307835506487178983780212787)
          ·
            refine ⟨461753259730768475670319181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307835506487178983780212787 461753259730768475670319181)
            ·
              refine ⟨173157472399038178376369693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461753259730768475670319181 173157472399038178376369693)
              ·
                refine ⟨64934052149639316891138635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173157472399038178376369693 64934052149639316891138635)
                ·
                  refine ⟨97401078224458975336707953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64934052149639316891138635 97401078224458975336707953)
                  ·
                    refine ⟨73050808668344231502530965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97401078224458975336707953 73050808668344231502530965)
                    ·
                      refine ⟨3424256656328635851681139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73050808668344231502530965 3424256656328635851681139)
                      ·
                        rfl

theorem cell23_6668716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_6668716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668716 prefixEnd_6668716 := by exact prefixLift 6668716
  have htrace : WordTrace (prefixWord ++ tailWord_6668716) baseStart_6668716 baseEnd_6668716 := by
    simpa [prefixWord, tailWord_6668716, baseEnd_6668716] using wordTrace_append hprefix tailTrace_6668716
  have hstable : (prefixWord ++ tailWord_6668716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668716).length < 2 ^ (prefixWord ++ tailWord_6668716).sum := by decide
  have hdescent : baseEnd_6668716 < baseStart_6668716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668736 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_6668736 : Nat := 118140960795 + 6668736 * 2 ^ 59
def prefixEnd_6668736 : Nat := 4983230072969 + 3 ^ 40 * 6668736 * 2
def baseEnd_6668736 : Nat := 3424266925941725773431047

theorem tailTrace_6668736 : CollatzResearch.WordTrace tailWord_6668736 prefixEnd_6668736 3424266925941725773431047 := by
  unfold tailWord_6668736
  simp only [CollatzResearch.WordTrace]
  refine ⟨121614391984157938139553031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162152522645543917519404041 121614391984157938139553031)
  ·
    refine ⟨182421587976236907209329547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121614391984157938139553031 182421587976236907209329547)
    ·
      refine ⟨273632381964355360813994321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182421587976236907209329547 273632381964355360813994321)
      ·
        refine ⟨205224286473266520610495741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273632381964355360813994321 205224286473266520610495741)
        ·
          refine ⟨76959107427474945228935903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205224286473266520610495741 76959107427474945228935903)
          ·
            refine ⟨115438661141212417843403855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76959107427474945228935903 115438661141212417843403855)
            ·
              refine ⟨173157991711818626765105783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115438661141212417843403855 173157991711818626765105783)
              ·
                refine ⟨259736987567727940147658675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173157991711818626765105783 259736987567727940147658675)
                ·
                  refine ⟨389605481351591910221488013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259736987567727940147658675 389605481351591910221488013)
                  ·
                    refine ⟨146102055506846966333058005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389605481351591910221488013 146102055506846966333058005)
                    ·
                      refine ⟨3424266925941725773431047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146102055506846966333058005 3424266925941725773431047)
                      ·
                        rfl

theorem cell23_6668736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_6668736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668736 prefixEnd_6668736 := by exact prefixLift 6668736
  have htrace : WordTrace (prefixWord ++ tailWord_6668736) baseStart_6668736 baseEnd_6668736 := by
    simpa [prefixWord, tailWord_6668736, baseEnd_6668736] using wordTrace_append hprefix tailTrace_6668736
  have hstable : (prefixWord ++ tailWord_6668736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668736).length < 2 ^ (prefixWord ++ tailWord_6668736).sum := by decide
  have hdescent : baseEnd_6668736 < baseStart_6668736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668743 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 3, 5]
def baseStart_6668743 : Nat := 118140960795 + 6668743 * 2 ^ 59
def prefixEnd_6668743 : Nat := 4983230072969 + 3 ^ 40 * 6668743 * 2
def baseEnd_6668743 : Nat := 1141423506768769082014505

theorem tailTrace_6668743 : CollatzResearch.WordTrace tailWord_6668743 prefixEnd_6668743 1141423506768769082014505 := by
  unfold tailWord_6668743
  simp only [CollatzResearch.WordTrace]
  refine ⟨243229039279290516474610883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162152692852860344316407255 243229039279290516474610883)
  ·
    refine ⟨364843558918935774711916325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243229039279290516474610883 364843558918935774711916325)
    ·
      refine ⟨68408167297300457758484311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364843558918935774711916325 68408167297300457758484311)
      ·
        refine ⟨102612250945950686637726467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68408167297300457758484311 102612250945950686637726467)
        ·
          refine ⟨153918376418926029956589701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102612250945950686637726467 153918376418926029956589701)
          ·
            refine ⟨28859695578548630616860569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153918376418926029956589701 28859695578548630616860569)
            ·
              refine ⟨21644771683911472962645427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28859695578548630616860569 21644771683911472962645427)
              ·
                refine ⟨32467157525867209443968141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21644771683911472962645427 32467157525867209443968141)
                ·
                  refine ⟨12175184072200203541488053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32467157525867209443968141 12175184072200203541488053)
                  ·
                    refine ⟨1141423506768769082014505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12175184072200203541488053 1141423506768769082014505)
                    ·
                      rfl

theorem cell23_6668743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_6668743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668743 prefixEnd_6668743 := by exact prefixLift 6668743
  have htrace : WordTrace (prefixWord ++ tailWord_6668743) baseStart_6668743 baseEnd_6668743 := by
    simpa [prefixWord, tailWord_6668743, baseEnd_6668743] using wordTrace_append hprefix tailTrace_6668743
  have hstable : (prefixWord ++ tailWord_6668743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668743).length < 2 ^ (prefixWord ++ tailWord_6668743).sum := by decide
  have hdescent : baseEnd_6668743 < baseStart_6668743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668797 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_6668797 : Nat := 118140960795 + 6668797 * 2 ^ 59
def prefixEnd_6668797 : Nat := 4983230072969 + 3 ^ 40 * 6668797 * 2
def baseEnd_6668797 : Nat := 3424298248261650034768267

theorem tailTrace_6668797 : CollatzResearch.WordTrace tailWord_6668797 prefixEnd_6668797 3424298248261650034768267 := by
  unfold tailWord_6668797
  simp only [CollatzResearch.WordTrace]
  refine ⟨243231008821094883697076645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162154005880729922464717763 243231008821094883697076645)
  ·
    refine ⟨45605814153955290693201871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243231008821094883697076645 45605814153955290693201871)
    ·
      refine ⟨68408721230932936039802807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45605814153955290693201871 68408721230932936039802807)
      ·
        refine ⟨102613081846399404059704211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68408721230932936039802807 102613081846399404059704211)
        ·
          refine ⟨153919622769599106089556317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102613081846399404059704211 153919622769599106089556317)
          ·
            refine ⟨57719858538599664783583619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153919622769599106089556317 57719858538599664783583619)
            ·
              refine ⟨86579787807899497175375429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57719858538599664783583619 86579787807899497175375429)
              ·
                refine ⟨16233710213981155720382893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86579787807899497175375429 16233710213981155720382893)
                ·
                  refine ⟨6087641330242933395143585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16233710213981155720382893 6087641330242933395143585)
                  ·
                    refine ⟨4565730997682200046357689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6087641330242933395143585 4565730997682200046357689)
                    ·
                      refine ⟨3424298248261650034768267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565730997682200046357689 3424298248261650034768267)
                      ·
                        rfl

theorem cell23_6668797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_6668797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668797 prefixEnd_6668797 := by exact prefixLift 6668797
  have htrace : WordTrace (prefixWord ++ tailWord_6668797) baseStart_6668797 baseEnd_6668797 := by
    simpa [prefixWord, tailWord_6668797, baseEnd_6668797] using wordTrace_append hprefix tailTrace_6668797
  have hstable : (prefixWord ++ tailWord_6668797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668797).length < 2 ^ (prefixWord ++ tailWord_6668797).sum := by decide
  have hdescent : baseEnd_6668797 < baseStart_6668797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668820 : List Nat := [2, 4, 3, 1, 1, 1, 11]
def baseStart_6668820 : Nat := 118140960795 + 6668820 * 2 ^ 59
def prefixEnd_6668820 : Nat := 4983230072969 + 3 ^ 40 * 6668820 * 2
def baseEnd_6668820 : Nat := 42275432818724733886181

theorem tailTrace_6668820 : CollatzResearch.WordTrace tailWord_6668820 prefixEnd_6668820 42275432818724733886181 := by
  unfold tailWord_6668820
  simp only [CollatzResearch.WordTrace]
  refine ⟨121615923850005779312581957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162154565133341039083442609 121615923850005779312581957)
  ·
    refine ⟨22802985721876083621109117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121615923850005779312581957 22802985721876083621109117)
    ·
      refine ⟨8551119645703531357915919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22802985721876083621109117 8551119645703531357915919)
      ·
        refine ⟨12826679468555297036873879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551119645703531357915919 12826679468555297036873879)
        ·
          refine ⟨19240019202832945555310819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12826679468555297036873879 19240019202832945555310819)
          ·
            refine ⟨28860028804249418332966229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19240019202832945555310819 28860028804249418332966229)
            ·
              refine ⟨42275432818724733886181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28860028804249418332966229 42275432818724733886181)
              ·
                rfl

theorem cell23_6668820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 11].length) (baseStart_6668820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668820 prefixEnd_6668820 := by exact prefixLift 6668820
  have htrace : WordTrace (prefixWord ++ tailWord_6668820) baseStart_6668820 baseEnd_6668820 := by
    simpa [prefixWord, tailWord_6668820, baseEnd_6668820] using wordTrace_append hprefix tailTrace_6668820
  have hstable : (prefixWord ++ tailWord_6668820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668820).length < 2 ^ (prefixWord ++ tailWord_6668820).sum := by decide
  have hdescent : baseEnd_6668820 < baseStart_6668820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668833 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_6668833 : Nat := 118140960795 + 6668833 * 2 ^ 59
def prefixEnd_6668833 : Nat := 4983230072969 + 3 ^ 40 * 6668833 * 2
def baseEnd_6668833 : Nat := 1141438911188403964639367

theorem tailTrace_6668833 : CollatzResearch.WordTrace tailWord_6668833 prefixEnd_6668833 1141438911188403964639367 := by
  unfold tailWord_6668833
  simp only [CollatzResearch.WordTrace]
  refine ⟨243232321848964461845387153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162154881232642974563591435 243232321848964461845387153)
  ·
    refine ⟨182424241386723346384040365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243232321848964461845387153 182424241386723346384040365)
    ·
      refine ⟨68409090520021254894015137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182424241386723346384040365 68409090520021254894015137)
      ·
        refine ⟨51306817890015941170511353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68409090520021254894015137 51306817890015941170511353)
        ·
          refine ⟨38480113417511955877883515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51306817890015941170511353 38480113417511955877883515)
          ·
            refine ⟨57720170126267933816825273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38480113417511955877883515 57720170126267933816825273)
            ·
              refine ⟨43290127594700950362618955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57720170126267933816825273 43290127594700950362618955)
              ·
                refine ⟨64935191392051425543928433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43290127594700950362618955 64935191392051425543928433)
                ·
                  refine ⟨48701393544038569157946325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64935191392051425543928433 48701393544038569157946325)
                  ·
                    refine ⟨1141438911188403964639367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48701393544038569157946325 1141438911188403964639367)
                    ·
                      rfl

theorem cell23_6668833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_6668833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668833 prefixEnd_6668833 := by exact prefixLift 6668833
  have htrace : WordTrace (prefixWord ++ tailWord_6668833) baseStart_6668833 baseEnd_6668833 := by
    simpa [prefixWord, tailWord_6668833, baseEnd_6668833] using wordTrace_append hprefix tailTrace_6668833
  have hstable : (prefixWord ++ tailWord_6668833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668833).length < 2 ^ (prefixWord ++ tailWord_6668833).sum := by decide
  have hdescent : baseEnd_6668833 < baseStart_6668833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668857 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6668857 : Nat := 118140960795 + 6668857 * 2 ^ 59
def prefixEnd_6668857 : Nat := 4983230072969 + 3 ^ 40 * 6668857 * 2
def baseEnd_6668857 : Nat := 3424329057100919800017991

theorem tailTrace_6668857 : CollatzResearch.WordTrace tailWord_6668857 prefixEnd_6668857 3424329057100919800017991 := by
  unfold tailWord_6668857
  simp only [CollatzResearch.WordTrace]
  refine ⟨243233197200877513944260825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162155464800585009296173883 243233197200877513944260825)
  ·
    refine ⟨182424897900658135458195619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243233197200877513944260825 182424897900658135458195619)
    ·
      refine ⟨273637346850987203187293429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182424897900658135458195619 273637346850987203187293429)
      ·
        refine ⟨25653501267280050298808759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273637346850987203187293429 25653501267280050298808759)
        ·
          refine ⟨38480251900920075448213139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25653501267280050298808759 38480251900920075448213139)
          ·
            refine ⟨57720377851380113172319709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38480251900920075448213139 57720377851380113172319709)
            ·
              refine ⟨21645141694267542439619891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57720377851380113172319709 21645141694267542439619891)
              ·
                refine ⟨32467712541401313659429837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21645141694267542439619891 32467712541401313659429837)
                ·
                  refine ⟨12175392203025492622286189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32467712541401313659429837 12175392203025492622286189)
                  ·
                    refine ⟨4565772076134559733357321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12175392203025492622286189 4565772076134559733357321)
                    ·
                      refine ⟨3424329057100919800017991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565772076134559733357321 3424329057100919800017991)
                      ·
                        rfl

theorem cell23_6668857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6668857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668857 prefixEnd_6668857 := by exact prefixLift 6668857
  have htrace : WordTrace (prefixWord ++ tailWord_6668857) baseStart_6668857 baseEnd_6668857 := by
    simpa [prefixWord, tailWord_6668857, baseEnd_6668857] using wordTrace_append hprefix tailTrace_6668857
  have hstable : (prefixWord ++ tailWord_6668857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668857).length < 2 ^ (prefixWord ++ tailWord_6668857).sum := by decide
  have hdescent : baseEnd_6668857 < baseStart_6668857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668868 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6668868 : Nat := 118140960795 + 6668868 * 2 ^ 59
def prefixEnd_6668868 : Nat := 4983230072969 + 3 ^ 40 * 6668868 * 2
def baseEnd_6668868 : Nat := 3424334705388119256980441

theorem tailTrace_6668868 : CollatzResearch.WordTrace tailWord_6668868 prefixEnd_6668868 3424334705388119256980441 := by
  unfold tailWord_6668868
  simp only [CollatzResearch.WordTrace]
  refine ⟨121616799201918831411455629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162155732269225108548607505 121616799201918831411455629)
  ·
    refine ⟨45606299700719561779295861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121616799201918831411455629 45606299700719561779295861)
    ·
      refine ⟨4275590596942458916808987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45606299700719561779295861 4275590596942458916808987)
      ·
        refine ⟨6413385895413688375213481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275590596942458916808987 6413385895413688375213481)
        ·
          refine ⟨4810039421560266281410111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413385895413688375213481 4810039421560266281410111)
          ·
            refine ⟨7215059132340399422115167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810039421560266281410111 7215059132340399422115167)
            ·
              refine ⟨10822588698510599133172751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215059132340399422115167 10822588698510599133172751)
              ·
                refine ⟨16233883047765898699759127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10822588698510599133172751 16233883047765898699759127)
                ·
                  refine ⟨24350824571648848049638691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16233883047765898699759127 24350824571648848049638691)
                  ·
                    refine ⟨36526236857473272074458037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24350824571648848049638691 36526236857473272074458037)
                    ·
                      refine ⟨3424334705388119256980441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36526236857473272074458037 3424334705388119256980441)
                      ·
                        rfl

theorem cell23_6668868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6668868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668868 prefixEnd_6668868 := by exact prefixLift 6668868
  have htrace : WordTrace (prefixWord ++ tailWord_6668868) baseStart_6668868 baseEnd_6668868 := by
    simpa [prefixWord, tailWord_6668868, baseEnd_6668868] using wordTrace_append hprefix tailTrace_6668868
  have hstable : (prefixWord ++ tailWord_6668868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668868).length < 2 ^ (prefixWord ++ tailWord_6668868).sum := by decide
  have hdescent : baseEnd_6668868 < baseStart_6668868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668900 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_6668900 : Nat := 118140960795 + 6668900 * 2 ^ 59
def prefixEnd_6668900 : Nat := 4983230072969 + 3 ^ 40 * 6668900 * 2
def baseEnd_6668900 : Nat := 3424351136769063131780293

theorem tailTrace_6668900 : CollatzResearch.WordTrace tailWord_6668900 prefixEnd_6668900 3424351136769063131780293 := by
  unfold tailWord_6668900
  simp only [CollatzResearch.WordTrace]
  refine ⟨121617382769860866144038077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162156510359814488192050769 121617382769860866144038077)
  ·
    refine ⟨45606518538697824804014279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121617382769860866144038077 45606518538697824804014279)
    ·
      refine ⟨68409777808046737206021419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45606518538697824804014279 68409777808046737206021419)
      ·
        refine ⟨102614666712070105809032129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68409777808046737206021419 102614666712070105809032129)
        ·
          refine ⟨76961000034052579356774097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102614666712070105809032129 76961000034052579356774097)
          ·
            refine ⟨57720750025539434517580573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76961000034052579356774097 57720750025539434517580573)
            ·
              refine ⟨21645281259577287944092715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57720750025539434517580573 21645281259577287944092715)
              ·
                refine ⟨32467921889365931916139073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21645281259577287944092715 32467921889365931916139073)
                ·
                  refine ⟨24350941417024448937104305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32467921889365931916139073 24350941417024448937104305)
                  ·
                    refine ⟨18263206062768336702828229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24350941417024448937104305 18263206062768336702828229)
                    ·
                      refine ⟨3424351136769063131780293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18263206062768336702828229 3424351136769063131780293)
                      ·
                        rfl

theorem cell23_6668900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_6668900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668900 prefixEnd_6668900 := by exact prefixLift 6668900
  have htrace : WordTrace (prefixWord ++ tailWord_6668900) baseStart_6668900 baseEnd_6668900 := by
    simpa [prefixWord, tailWord_6668900, baseEnd_6668900] using wordTrace_append hprefix tailTrace_6668900
  have hstable : (prefixWord ++ tailWord_6668900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668900).length < 2 ^ (prefixWord ++ tailWord_6668900).sum := by decide
  have hdescent : baseEnd_6668900 < baseStart_6668900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668910 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_6668910 : Nat := 118140960795 + 6668910 * 2 ^ 59
def prefixEnd_6668910 : Nat := 4983230072969 + 3 ^ 40 * 6668910 * 2
def baseEnd_6668910 : Nat := 380484030175067565850583

theorem tailTrace_6668910 : CollatzResearch.WordTrace tailWord_6668910 prefixEnd_6668910 380484030175067565850583 := by
  unfold tailWord_6668910
  simp only [CollatzResearch.WordTrace]
  refine ⟨30404391283710687999492523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162156753513123669330626789 30404391283710687999492523)
  ·
    refine ⟨45606586925566031999238785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30404391283710687999492523 45606586925566031999238785)
    ·
      refine ⟨34204940194174523999429089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45606586925566031999238785 34204940194174523999429089)
      ·
        refine ⟨25653705145630892999571817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34204940194174523999429089 25653705145630892999571817)
        ·
          refine ⟨19240278859223169749678863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25653705145630892999571817 19240278859223169749678863)
          ·
            refine ⟨28860418288834754624518295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19240278859223169749678863 28860418288834754624518295)
            ·
              refine ⟨43290627433252131936777443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28860418288834754624518295 43290627433252131936777443)
              ·
                refine ⟨64935941149878197905166165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43290627433252131936777443 64935941149878197905166165)
                ·
                  refine ⟨380484030175067565850583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64935941149878197905166165 380484030175067565850583)
                  ·
                    rfl

theorem cell23_6668910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_6668910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668910 prefixEnd_6668910 := by exact prefixLift 6668910
  have htrace : WordTrace (prefixWord ++ tailWord_6668910) baseStart_6668910 baseEnd_6668910 := by
    simpa [prefixWord, tailWord_6668910, baseEnd_6668910] using wordTrace_append hprefix tailTrace_6668910
  have hstable : (prefixWord ++ tailWord_6668910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668910).length < 2 ^ (prefixWord ++ tailWord_6668910).sum := by decide
  have hdescent : baseEnd_6668910 < baseStart_6668910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6668938 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_6668938 : Nat := 118140960795 + 6668938 * 2 ^ 59
def prefixEnd_6668938 : Nat := 4983230072969 + 3 ^ 40 * 6668938 * 2
def baseEnd_6668938 : Nat := 3424370649033933983105119

theorem tailTrace_6668938 : CollatzResearch.WordTrace tailWord_6668938 prefixEnd_6668938 3424370649033933983105119 := by
  unfold tailWord_6668938
  simp only [CollatzResearch.WordTrace]
  refine ⟨60809037878396016194489867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162157434342389376518639645 60809037878396016194489867)
  ·
    refine ⟨91213556817594024291734801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60809037878396016194489867 91213556817594024291734801)
    ·
      refine ⟨68410167613195518218801101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91213556817594024291734801 68410167613195518218801101)
      ·
        refine ⟨25653812854948319332050413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68410167613195518218801101 25653812854948319332050413)
        ·
          refine ⟨9620179820605619749518905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25653812854948319332050413 9620179820605619749518905)
          ·
            refine ⟨7215134865454214812139179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9620179820605619749518905 7215134865454214812139179)
            ·
              refine ⟨10822702298181322218208769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215134865454214812139179 10822702298181322218208769)
              ·
                refine ⟨8117026723635991663656577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10822702298181322218208769 8117026723635991663656577)
                ·
                  refine ⟨6087770042726993747742433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8117026723635991663656577 6087770042726993747742433)
                  ·
                    refine ⟨4565827532045245310806825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6087770042726993747742433 4565827532045245310806825)
                    ·
                      refine ⟨3424370649033933983105119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565827532045245310806825 3424370649033933983105119)
                      ·
                        rfl

theorem cell23_6668938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_6668938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6668938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6668938 prefixEnd_6668938 := by exact prefixLift 6668938
  have htrace : WordTrace (prefixWord ++ tailWord_6668938) baseStart_6668938 baseEnd_6668938 := by
    simpa [prefixWord, tailWord_6668938, baseEnd_6668938] using wordTrace_append hprefix tailTrace_6668938
  have hstable : (prefixWord ++ tailWord_6668938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6668938).length < 2 ^ (prefixWord ++ tailWord_6668938).sum := by decide
  have hdescent : baseEnd_6668938 < baseStart_6668938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6668938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669000 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 8]
def baseStart_6669000 : Nat := 118140960795 + 6669000 * 2 ^ 59
def prefixEnd_6669000 : Nat := 4983230072969 + 3 ^ 40 * 6669000 * 2
def baseEnd_6669000 : Nat := 380489164981612526725537

theorem tailTrace_6669000 : CollatzResearch.WordTrace tailWord_6669000 prefixEnd_6669000 380489164981612526725537 := by
  unfold tailWord_6669000
  simp only [CollatzResearch.WordTrace]
  refine ⟨121619206419679724683358227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162158941892906299577810969 121619206419679724683358227)
  ·
    refine ⟨182428809629519587025037341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121619206419679724683358227 182428809629519587025037341)
    ·
      refine ⟨68410803611069845134389003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182428809629519587025037341 68410803611069845134389003)
      ·
        refine ⟨102616205416604767701583505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68410803611069845134389003 102616205416604767701583505)
        ·
          refine ⟨76962154062453575776187629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102616205416604767701583505 76962154062453575776187629)
          ·
            refine ⟨28860807773420090916070361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76962154062453575776187629 28860807773420090916070361)
            ·
              refine ⟨21645605830065068187052771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28860807773420090916070361 21645605830065068187052771)
              ·
                refine ⟨32468408745097602280579157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21645605830065068187052771 32468408745097602280579157)
                ·
                  refine ⟨380489164981612526725537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32468408745097602280579157 380489164981612526725537)
                  ·
                    rfl

theorem cell23_6669000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_6669000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669000 prefixEnd_6669000 := by exact prefixLift 6669000
  have htrace : WordTrace (prefixWord ++ tailWord_6669000) baseStart_6669000 baseEnd_6669000 := by
    simpa [prefixWord, tailWord_6669000, baseEnd_6669000] using wordTrace_append hprefix tailTrace_6669000
  have hstable : (prefixWord ++ tailWord_6669000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669000).length < 2 ^ (prefixWord ++ tailWord_6669000).sum := by decide
  have hdescent : baseEnd_6669000 < baseStart_6669000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669004 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_6669004 : Nat := 118140960795 + 6669004 * 2 ^ 59
def prefixEnd_6669004 : Nat := 4983230072969 + 3 ^ 40 * 6669004 * 2
def baseEnd_6669004 : Nat := 1141468179585710241626605

theorem tailTrace_6669004 : CollatzResearch.WordTrace tailWord_6669004 prefixEnd_6669004 1141468179585710241626605 := by
  unfold tailWord_6669004
  simp only [CollatzResearch.WordTrace]
  refine ⟨121619279365672479024931033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162159039154229972033241377 121619279365672479024931033)
  ·
    refine ⟨91214459524254359268698275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121619279365672479024931033 91214459524254359268698275)
    ·
      refine ⟨136821689286381538903047413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91214459524254359268698275 136821689286381538903047413)
      ·
        refine ⟨12827033370598269272160695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136821689286381538903047413 12827033370598269272160695)
        ·
          refine ⟨19240550055897403908241043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827033370598269272160695 19240550055897403908241043)
          ·
            refine ⟨28860825083846105862361565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19240550055897403908241043 28860825083846105862361565)
            ·
              refine ⟨10822809406442289698385587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28860825083846105862361565 10822809406442289698385587)
              ·
                refine ⟨16234214109663434547578381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10822809406442289698385587 16234214109663434547578381)
                ·
                  refine ⟨6087830291123787955341893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16234214109663434547578381 6087830291123787955341893)
                  ·
                    refine ⟨1141468179585710241626605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6087830291123787955341893 1141468179585710241626605)
                    ·
                      rfl

theorem cell23_6669004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_6669004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669004 prefixEnd_6669004 := by exact prefixLift 6669004
  have htrace : WordTrace (prefixWord ++ tailWord_6669004) baseStart_6669004 baseEnd_6669004 := by
    simpa [prefixWord, tailWord_6669004, baseEnd_6669004] using wordTrace_append hprefix tailTrace_6669004
  have hstable : (prefixWord ++ tailWord_6669004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669004).length < 2 ^ (prefixWord ++ tailWord_6669004).sum := by decide
  have hdescent : baseEnd_6669004 < baseStart_6669004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669067 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 6, 2]
def baseStart_6669067 : Nat := 118140960795 + 6669067 * 2 ^ 59
def prefixEnd_6669067 : Nat := 4983230072969 + 3 ^ 40 * 6669067 * 2
def baseEnd_6669067 : Nat := 3424436888038363978392025

theorem tailTrace_6669067 : CollatzResearch.WordTrace tailWord_6669067 prefixEnd_6669067 3424436888038363978392025 := by
  unfold tailWord_6669067
  simp only [CollatzResearch.WordTrace]
  refine ⟨243240856530116719809405455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162160571020077813206270303 243240856530116719809405455)
  ·
    refine ⟨364861284795175079714108183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243240856530116719809405455 364861284795175079714108183)
    ·
      refine ⟨547291927192762619571162275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364861284795175079714108183 547291927192762619571162275)
      ·
        refine ⟨820937890789143929356743413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547291927192762619571162275 820937890789143929356743413)
        ·
          refine ⟨76962927261482243377194695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 820937890789143929356743413 76962927261482243377194695)
          ·
            refine ⟨115444390892223365065792043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76962927261482243377194695 115444390892223365065792043)
            ·
              refine ⟨173166586338335047598688065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115444390892223365065792043 173166586338335047598688065)
              ·
                refine ⟨129874939753751285699016049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173166586338335047598688065 129874939753751285699016049)
                ·
                  refine ⟨97406204815313464274262037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129874939753751285699016049 97406204815313464274262037)
                  ·
                    refine ⟨4565915850717818637856033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97406204815313464274262037 4565915850717818637856033)
                    ·
                      refine ⟨3424436888038363978392025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565915850717818637856033 3424436888038363978392025)
                      ·
                        rfl

theorem cell23_6669067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6, 2].length) (baseStart_6669067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669067 prefixEnd_6669067 := by exact prefixLift 6669067
  have htrace : WordTrace (prefixWord ++ tailWord_6669067) baseStart_6669067 baseEnd_6669067 := by
    simpa [prefixWord, tailWord_6669067, baseEnd_6669067] using wordTrace_append hprefix tailTrace_6669067
  have hstable : (prefixWord ++ tailWord_6669067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669067).length < 2 ^ (prefixWord ++ tailWord_6669067).sum := by decide
  have hdescent : baseEnd_6669067 < baseStart_6669067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669077 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_6669077 : Nat := 118140960795 + 6669077 * 2 ^ 59
def prefixEnd_6669077 : Nat := 4983230072969 + 3 ^ 40 * 6669077 * 2
def baseEnd_6669077 : Nat := 1141480674281636313088993

theorem tailTrace_6669077 : CollatzResearch.WordTrace tailWord_6669077 prefixEnd_6669077 1141480674281636313088993 := by
  unfold tailWord_6669077
  simp only [CollatzResearch.WordTrace]
  refine ⟨243241221260080491517269485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162160814173386994344846323 243241221260080491517269485)
  ·
    refine ⟨91215457972530184318976057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243241221260080491517269485 91215457972530184318976057)
    ·
      refine ⟨68411593479397638239232043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91215457972530184318976057 68411593479397638239232043)
      ·
        refine ⟨102617390219096457358848065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68411593479397638239232043 102617390219096457358848065)
        ·
          refine ⟨76963042664322343019136049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102617390219096457358848065 76963042664322343019136049)
          ·
            refine ⟨57722281998241757264352037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76963042664322343019136049 57722281998241757264352037)
            ·
              refine ⟨10822927874670329487066007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57722281998241757264352037 10822927874670329487066007)
              ·
                refine ⟨16234391812005494230599011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10822927874670329487066007 16234391812005494230599011)
                ·
                  refine ⟨24351587718008241345898517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16234391812005494230599011 24351587718008241345898517)
                  ·
                    refine ⟨1141480674281636313088993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24351587718008241345898517 1141480674281636313088993)
                    ·
                      rfl

theorem cell23_6669077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_6669077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669077 prefixEnd_6669077 := by exact prefixLift 6669077
  have htrace : WordTrace (prefixWord ++ tailWord_6669077) baseStart_6669077 baseEnd_6669077 := by
    simpa [prefixWord, tailWord_6669077, baseEnd_6669077] using wordTrace_append hprefix tailTrace_6669077
  have hstable : (prefixWord ++ tailWord_6669077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669077).length < 2 ^ (prefixWord ++ tailWord_6669077).sum := by decide
  have hdescent : baseEnd_6669077 < baseStart_6669077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669120 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_6669120 : Nat := 118140960795 + 6669120 * 2 ^ 59
def prefixEnd_6669120 : Nat := 4983230072969 + 3 ^ 40 * 6669120 * 2
def baseEnd_6669120 : Nat := 1141488034171017423676427

theorem tailTrace_6669120 : CollatzResearch.WordTrace tailWord_6669120 prefixEnd_6669120 1141488034171017423676427 := by
  unfold tailWord_6669120
  simp only [CollatzResearch.WordTrace]
  refine ⟨121621394799462354930542407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162161859732616473240723209 121621394799462354930542407)
  ·
    refine ⟨182432092199193532395813611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121621394799462354930542407 182432092199193532395813611)
    ·
      refine ⟨273648138298790298593720417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182432092199193532395813611 273648138298790298593720417)
      ·
        refine ⟨205236103724092723945290313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273648138298790298593720417 205236103724092723945290313)
        ·
          refine ⟨153927077793069542958967735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205236103724092723945290313 153927077793069542958967735)
          ·
            refine ⟨230890616689604314438451603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153927077793069542958967735 230890616689604314438451603)
            ·
              refine ⟨346335925034406471657677405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230890616689604314438451603 346335925034406471657677405)
              ·
                refine ⟨129875971887902426871629027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346335925034406471657677405 129875971887902426871629027)
                ·
                  refine ⟨194813957831853640307443541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129875971887902426871629027 194813957831853640307443541)
                  ·
                    refine ⟨1141488034171017423676427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194813957831853640307443541 1141488034171017423676427)
                    ·
                      rfl

theorem cell23_6669120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_6669120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669120 prefixEnd_6669120 := by exact prefixLift 6669120
  have htrace : WordTrace (prefixWord ++ tailWord_6669120) baseStart_6669120 baseEnd_6669120 := by
    simpa [prefixWord, tailWord_6669120, baseEnd_6669120] using wordTrace_append hprefix tailTrace_6669120
  have hstable : (prefixWord ++ tailWord_6669120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669120).length < 2 ^ (prefixWord ++ tailWord_6669120).sum := by decide
  have hdescent : baseEnd_6669120 < baseStart_6669120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669121 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6669121 : Nat := 118140960795 + 6669121 * 2 ^ 59
def prefixEnd_6669121 : Nat := 4983230072969 + 3 ^ 40 * 6669121 * 2
def baseEnd_6669121 : Nat := 3424464615993706767116777

theorem tailTrace_6669121 : CollatzResearch.WordTrace tailWord_6669121 prefixEnd_6669121 3424464615993706767116777 := by
  unfold tailWord_6669121
  simp only [CollatzResearch.WordTrace]
  refine ⟨243242826071921087031871217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162161884047947391354580811 243242826071921087031871217)
  ·
    refine ⟨182432119553940815273903413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243242826071921087031871217 182432119553940815273903413)
    ·
      refine ⟨17103011208181951431928445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182432119553940815273903413 17103011208181951431928445)
      ·
        refine ⟨6413629203068231786973167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17103011208181951431928445 6413629203068231786973167)
        ·
          refine ⟨9620443804602347680459751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6413629203068231786973167 9620443804602347680459751)
          ·
            refine ⟨14430665706903521520689627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620443804602347680459751 14430665706903521520689627)
            ·
              refine ⟨21645998560355282281034441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14430665706903521520689627 21645998560355282281034441)
              ·
                refine ⟨16234498920266461710775831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21645998560355282281034441 16234498920266461710775831)
                ·
                  refine ⟨24351748380399692566163747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16234498920266461710775831 24351748380399692566163747)
                  ·
                    refine ⟨36527622570599538849245621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24351748380399692566163747 36527622570599538849245621)
                    ·
                      refine ⟨3424464615993706767116777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36527622570599538849245621 3424464615993706767116777)
                      ·
                        rfl

theorem cell23_6669121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6669121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669121 prefixEnd_6669121 := by exact prefixLift 6669121
  have htrace : WordTrace (prefixWord ++ tailWord_6669121) baseStart_6669121 baseEnd_6669121 := by
    simpa [prefixWord, tailWord_6669121, baseEnd_6669121] using wordTrace_append hprefix tailTrace_6669121
  have hstable : (prefixWord ++ tailWord_6669121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669121).length < 2 ^ (prefixWord ++ tailWord_6669121).sum := by decide
  have hdescent : baseEnd_6669121 < baseStart_6669121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669144 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 3, 3, 2]
def baseStart_6669144 : Nat := 118140960795 + 6669144 * 2 ^ 59
def prefixEnd_6669144 : Nat := 4983230072969 + 3 ^ 40 * 6669144 * 2
def baseEnd_6669144 : Nat := 3424476426048760177129171

theorem tailTrace_6669144 : CollatzResearch.WordTrace tailWord_6669144 prefixEnd_6669144 3424476426048760177129171 := by
  unfold tailWord_6669144
  simp only [CollatzResearch.WordTrace]
  refine ⟨121621832475418880979979243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162162443300558507973305657 121621832475418880979979243)
  ·
    refine ⟨182432748713128321469968865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121621832475418880979979243 182432748713128321469968865)
    ·
      refine ⟨136824561534846241102476649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182432748713128321469968865 136824561534846241102476649)
      ·
        refine ⟨102618421151134680826857487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136824561534846241102476649 102618421151134680826857487)
        ·
          refine ⟨153927631726702021240286231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102618421151134680826857487 153927631726702021240286231)
          ·
            refine ⟨230891447590053031860429347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153927631726702021240286231 230891447590053031860429347)
            ·
              refine ⟨346337171385079547790644021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230891447590053031860429347 346337171385079547790644021)
              ·
                refine ⟨32469109817351207605372877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346337171385079547790644021 32469109817351207605372877)
                ·
                  refine ⟨12175916181506702852014829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32469109817351207605372877 12175916181506702852014829)
                  ·
                    refine ⟨4565968568065013569505561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12175916181506702852014829 4565968568065013569505561)
                    ·
                      refine ⟨3424476426048760177129171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4565968568065013569505561 3424476426048760177129171)
                      ·
                        rfl

theorem cell23_6669144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_6669144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669144 prefixEnd_6669144 := by exact prefixLift 6669144
  have htrace : WordTrace (prefixWord ++ tailWord_6669144) baseStart_6669144 baseEnd_6669144 := by
    simpa [prefixWord, tailWord_6669144, baseEnd_6669144] using wordTrace_append hprefix tailTrace_6669144
  have hstable : (prefixWord ++ tailWord_6669144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669144).length < 2 ^ (prefixWord ++ tailWord_6669144).sum := by decide
  have hdescent : baseEnd_6669144 < baseStart_6669144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669187 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4]
def baseStart_6669187 : Nat := 118140960795 + 6669187 * 2 ^ 59
def prefixEnd_6669187 : Nat := 4983230072969 + 3 ^ 40 * 6669187 * 2
def baseEnd_6669187 : Nat := 3424498505716903508891473

theorem tailTrace_6669187 : CollatzResearch.WordTrace tailWord_6669187 prefixEnd_6669187 3424498505716903508891473 := by
  unfold tailWord_6669187
  simp only [CollatzResearch.WordTrace]
  refine ⟨243245233289681980303773815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162163488859787986869182543 243245233289681980303773815)
  ·
    refine ⟨364867849934522970455660723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243245233289681980303773815 364867849934522970455660723)
    ·
      refine ⟨547301774901784455683491085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364867849934522970455660723 547301774901784455683491085)
      ·
        refine ⟨205238165588169170881309157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547301774901784455683491085 205238165588169170881309157)
        ·
          refine ⟨38482156047781719540245467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205238165588169170881309157 38482156047781719540245467)
          ·
            refine ⟨57723234071672579310368201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38482156047781719540245467 57723234071672579310368201)
            ·
              refine ⟨43292425553754434482776151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57723234071672579310368201 43292425553754434482776151)
              ·
                refine ⟨64938638330631651724164227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43292425553754434482776151 64938638330631651724164227)
                ·
                  refine ⟨97407957495947477586246341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64938638330631651724164227 97407957495947477586246341)
                  ·
                    refine ⟨18263992030490152047421189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97407957495947477586246341 18263992030490152047421189)
                    ·
                      refine ⟨3424498505716903508891473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18263992030490152047421189 3424498505716903508891473)
                      ·
                        rfl

theorem cell23_6669187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_6669187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669187 prefixEnd_6669187 := by exact prefixLift 6669187
  have htrace : WordTrace (prefixWord ++ tailWord_6669187) baseStart_6669187 baseEnd_6669187 := by
    simpa [prefixWord, tailWord_6669187, baseEnd_6669187] using wordTrace_append hprefix tailTrace_6669187
  have hstable : (prefixWord ++ tailWord_6669187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669187).length < 2 ^ (prefixWord ++ tailWord_6669187).sum := by decide
  have hdescent : baseEnd_6669187 < baseStart_6669187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669194 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6669194 : Nat := 118140960795 + 6669194 * 2 ^ 59
def prefixEnd_6669194 : Nat := 4983230072969 + 3 ^ 40 * 6669194 * 2
def baseEnd_6669194 : Nat := 3424502100081484981503941

theorem tailTrace_6669194 : CollatzResearch.WordTrace tailWord_6669194 prefixEnd_6669194 3424502100081484981503941 := by
  unfold tailWord_6669194
  simp only [CollatzResearch.WordTrace]
  refine ⟨60811372150164155124819659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162163659067104413666185757 60811372150164155124819659)
  ·
    refine ⟨91217058225246232687229489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60811372150164155124819659 91217058225246232687229489)
    ·
      refine ⟨68412793668934674515422117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91217058225246232687229489 68412793668934674515422117)
      ·
        refine ⟨12827398812925251471641647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68412793668934674515422117 12827398812925251471641647)
        ·
          refine ⟨19241098219387877207462471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827398812925251471641647 19241098219387877207462471)
          ·
            refine ⟨28861647329081815811193707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19241098219387877207462471 28861647329081815811193707)
            ·
              refine ⟨43292470993622723716790561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28861647329081815811193707 43292470993622723716790561)
              ·
                refine ⟨32469353245217042787592921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43292470993622723716790561 32469353245217042787592921)
                ·
                  refine ⟨24352014933912782090694691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32469353245217042787592921 24352014933912782090694691)
                  ·
                    refine ⟨36528022400869173136042037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24352014933912782090694691 36528022400869173136042037)
                    ·
                      refine ⟨3424502100081484981503941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36528022400869173136042037 3424502100081484981503941)
                      ·
                        rfl

theorem cell23_6669194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6669194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669194 prefixEnd_6669194 := by exact prefixLift 6669194
  have htrace : WordTrace (prefixWord ++ tailWord_6669194) baseStart_6669194 baseEnd_6669194 := by
    simpa [prefixWord, tailWord_6669194, baseEnd_6669194] using wordTrace_append hprefix tailTrace_6669194
  have hstable : (prefixWord ++ tailWord_6669194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669194).length < 2 ^ (prefixWord ++ tailWord_6669194).sum := by decide
  have hdescent : baseEnd_6669194 < baseStart_6669194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669264 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 6, 2]
def baseStart_6669264 : Nat := 118140960795 + 6669264 * 2 ^ 59
def prefixEnd_6669264 : Nat := 4983230072969 + 3 ^ 40 * 6669264 * 2
def baseEnd_6669264 : Nat := 3424538043727299707628619

theorem tailTrace_6669264 : CollatzResearch.WordTrace tailWord_6669264 prefixEnd_6669264 3424538043727299707628619 := by
  unfold tailWord_6669264
  simp only [CollatzResearch.WordTrace]
  refine ⟨121624020855201511227163423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162165361140268681636217897 121624020855201511227163423)
  ·
    refine ⟨182436031282802266840745135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121624020855201511227163423 182436031282802266840745135)
    ·
      refine ⟨273654046924203400261117703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182436031282802266840745135 273654046924203400261117703)
      ·
        refine ⟨410481070386305100391676555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273654046924203400261117703 410481070386305100391676555)
        ·
          refine ⟨615721605579457650587514833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410481070386305100391676555 615721605579457650587514833)
          ·
            refine ⟨461791204184593237940636125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615721605579457650587514833 461791204184593237940636125)
            ·
              refine ⟨173171701569222464227738547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461791204184593237940636125 173171701569222464227738547)
              ·
                refine ⟨259757552353833696341607821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173171701569222464227738547 259757552353833696341607821)
                ·
                  refine ⟨97409082132687636128102933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259757552353833696341607821 97409082132687636128102933)
                  ·
                    refine ⟨4566050724969732943504825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97409082132687636128102933 4566050724969732943504825)
                    ·
                      refine ⟨3424538043727299707628619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566050724969732943504825 3424538043727299707628619)
                      ·
                        rfl

theorem cell23_6669264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 6, 2].length) (baseStart_6669264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669264 prefixEnd_6669264 := by exact prefixLift 6669264
  have htrace : WordTrace (prefixWord ++ tailWord_6669264) baseStart_6669264 baseEnd_6669264 := by
    simpa [prefixWord, tailWord_6669264, baseEnd_6669264] using wordTrace_append hprefix tailTrace_6669264
  have hstable : (prefixWord ++ tailWord_6669264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669264).length < 2 ^ (prefixWord ++ tailWord_6669264).sum := by decide
  have hdescent : baseEnd_6669264 < baseStart_6669264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669307 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_6669307 : Nat := 118140960795 + 6669307 * 2 ^ 59
def prefixEnd_6669307 : Nat := 4983230072969 + 3 ^ 40 * 6669307 * 2
def baseEnd_6669307 : Nat := 3424560123395443039390921

theorem tailTrace_6669307 : CollatzResearch.WordTrace tailWord_6669307 prefixEnd_6669307 3424560123395443039390921 := by
  unfold tailWord_6669307
  simp only [CollatzResearch.WordTrace]
  refine ⟨243249610049247240798142175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162166406699498160532094783 243249610049247240798142175)
  ·
    refine ⟨364874415073870861197213263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243249610049247240798142175 364874415073870861197213263)
    ·
      refine ⟨547311622610806291795819895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364874415073870861197213263 547311622610806291795819895)
      ·
        refine ⟨820967433916209437693729843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547311622610806291795819895 820967433916209437693729843)
        ·
          refine ⟨1231451150874314156540594765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820967433916209437693729843 1231451150874314156540594765)
          ·
            refine ⟨461794181577867808702723037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1231451150874314156540594765 461794181577867808702723037)
            ·
              refine ⟨173172818091700428263521139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461794181577867808702723037 173172818091700428263521139)
              ·
                refine ⟨259759227137550642395281709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173172818091700428263521139 259759227137550642395281709)
                ·
                  refine ⟨97409710176581490898230641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259759227137550642395281709 97409710176581490898230641)
                  ·
                    refine ⟨73057282632436118173672981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97409710176581490898230641 73057282632436118173672981)
                    ·
                      refine ⟨3424560123395443039390921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73057282632436118173672981 3424560123395443039390921)
                      ·
                        rfl

theorem cell23_6669307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_6669307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669307 prefixEnd_6669307 := by exact prefixLift 6669307
  have htrace : WordTrace (prefixWord ++ tailWord_6669307) baseStart_6669307 baseEnd_6669307 := by
    simpa [prefixWord, tailWord_6669307, baseEnd_6669307] using wordTrace_append hprefix tailTrace_6669307
  have hstable : (prefixWord ++ tailWord_6669307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669307).length < 2 ^ (prefixWord ++ tailWord_6669307).sum := by decide
  have hdescent : baseEnd_6669307 < baseStart_6669307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669327 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_6669327 : Nat := 118140960795 + 6669327 * 2 ^ 59
def prefixEnd_6669327 : Nat := 4983230072969 + 3 ^ 40 * 6669327 * 2
def baseEnd_6669327 : Nat := 3424570393008532961140829

theorem tailTrace_6669327 : CollatzResearch.WordTrace tailWord_6669327 prefixEnd_6669327 3424570393008532961140829 := by
  unfold tailWord_6669327
  simp only [CollatzResearch.WordTrace]
  refine ⟨243250339509174784213870235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162166893006116522809246823 243250339509174784213870235)
  ·
    refine ⟨364875509263762176320805353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243250339509174784213870235 364875509263762176320805353)
    ·
      refine ⟨273656631947821632240604015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364875509263762176320805353 273656631947821632240604015)
      ·
        refine ⟨410484947921732448360906023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273656631947821632240604015 410484947921732448360906023)
        ·
          refine ⟨615727421882598672541359035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410484947921732448360906023 615727421882598672541359035)
          ·
            refine ⟨923591132823898008812038553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615727421882598672541359035 923591132823898008812038553)
            ·
              refine ⟨692693349617923506609028915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923591132823898008812038553 692693349617923506609028915)
              ·
                refine ⟨1039040024426885259913543373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692693349617923506609028915 1039040024426885259913543373)
                ·
                  refine ⟨389640009160081972467578765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039040024426885259913543373 389640009160081972467578765)
                  ·
                    refine ⟨146115003435030739675342037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389640009160081972467578765 146115003435030739675342037)
                    ·
                      refine ⟨3424570393008532961140829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 146115003435030739675342037 3424570393008532961140829)
                      ·
                        rfl

theorem cell23_6669327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_6669327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669327 prefixEnd_6669327 := by exact prefixLift 6669327
  have htrace : WordTrace (prefixWord ++ tailWord_6669327) baseStart_6669327 baseEnd_6669327 := by
    simpa [prefixWord, tailWord_6669327, baseEnd_6669327] using wordTrace_append hprefix tailTrace_6669327
  have hstable : (prefixWord ++ tailWord_6669327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669327).length < 2 ^ (prefixWord ++ tailWord_6669327).sum := by decide
  have hdescent : baseEnd_6669327 < baseStart_6669327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
