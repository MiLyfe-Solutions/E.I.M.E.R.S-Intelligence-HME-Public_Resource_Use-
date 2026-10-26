import V185TrunkScan23Chunk1173

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6955872 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 1, 4, 2]
def baseStart_6955872 : Nat := 118140960795 + 6955872 * 2 ^ 59
def prefixEnd_6955872 : Nat := 4983230072969 + 3 ^ 40 * 6955872 * 2
def baseEnd_6955872 : Nat := 3571705707151114352510533

theorem tailTrace_6955872 : CollatzResearch.WordTrace tailWord_6955872 prefixEnd_6955872 3571705707151114352510533 := by
  unfold tailWord_6955872
  simp only [CollatzResearch.WordTrace]
  refine ⟨126850747128035593601858935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169134329504047458135811913 126850747128035593601858935)
  ·
    refine ⟨190276120692053390402788403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126850747128035593601858935 190276120692053390402788403)
    ·
      refine ⟨285414181038080085604182605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190276120692053390402788403 285414181038080085604182605)
      ·
        refine ⟨107030317889280032101568477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285414181038080085604182605 107030317889280032101568477)
        ·
          refine ⟨40136369208480012038088179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107030317889280032101568477 40136369208480012038088179)
          ·
            refine ⟨60204553812720018057132269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40136369208480012038088179 60204553812720018057132269)
            ·
              refine ⟨22576707679770006771424601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60204553812720018057132269 22576707679770006771424601)
              ·
                refine ⟨16932530759827505078568451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22576707679770006771424601 16932530759827505078568451)
                ·
                  refine ⟨25398796139741257617852677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16932530759827505078568451 25398796139741257617852677)
                  ·
                    refine ⟨4762274276201485803347377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25398796139741257617852677 4762274276201485803347377)
                    ·
                      refine ⟨3571705707151114352510533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762274276201485803347377 3571705707151114352510533)
                      ·
                        rfl

theorem cell23_6955872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_6955872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955872 prefixEnd_6955872 := by exact prefixLift 6955872
  have htrace : WordTrace (prefixWord ++ tailWord_6955872) baseStart_6955872 baseEnd_6955872 := by
    simpa [prefixWord, tailWord_6955872, baseEnd_6955872] using wordTrace_append hprefix tailTrace_6955872
  have hstable : (prefixWord ++ tailWord_6955872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955872).length < 2 ^ (prefixWord ++ tailWord_6955872).sum := by decide
  have hdescent : baseEnd_6955872 < baseStart_6955872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955875 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6955875 : Nat := 118140960795 + 6955875 * 2 ^ 59
def prefixEnd_6955875 : Nat := 4983230072969 + 3 ^ 40 * 6955875 * 2
def baseEnd_6955875 : Nat := 3571707247593077840773019

theorem tailTrace_6955875 : CollatzResearch.WordTrace tailWord_6955875 prefixEnd_6955875 3571707247593077840773019 := by
  unfold tailWord_6955875
  simp only [CollatzResearch.WordTrace]
  refine ⟨253701603675060318716077079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169134402450040212477384719 253701603675060318716077079)
  ·
    refine ⟨380552405512590478074115619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253701603675060318716077079 380552405512590478074115619)
    ·
      refine ⟨570828608268885717111173429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380552405512590478074115619 570828608268885717111173429)
      ·
        refine ⟨53515182025208035979172509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 570828608268885717111173429 53515182025208035979172509)
        ·
          refine ⟨20068193259453013492189691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53515182025208035979172509 20068193259453013492189691)
          ·
            refine ⟨30102289889179520238284537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20068193259453013492189691 30102289889179520238284537)
            ·
              refine ⟨22576717416884640178713403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30102289889179520238284537 22576717416884640178713403)
              ·
                refine ⟨33865076125326960268070105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22576717416884640178713403 33865076125326960268070105)
                ·
                  refine ⟨25398807093995220201052579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33865076125326960268070105 25398807093995220201052579)
                  ·
                    refine ⟨38098210640992830301578869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25398807093995220201052579 38098210640992830301578869)
                    ·
                      refine ⟨3571707247593077840773019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38098210640992830301578869 3571707247593077840773019)
                      ·
                        rfl

theorem cell23_6955875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6955875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955875 prefixEnd_6955875 := by exact prefixLift 6955875
  have htrace : WordTrace (prefixWord ++ tailWord_6955875) baseStart_6955875 baseEnd_6955875 := by
    simpa [prefixWord, tailWord_6955875, baseEnd_6955875] using wordTrace_append hprefix tailTrace_6955875
  have hstable : (prefixWord ++ tailWord_6955875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955875).length < 2 ^ (prefixWord ++ tailWord_6955875).sum := by decide
  have hdescent : baseEnd_6955875 < baseStart_6955875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955876 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_6955876 : Nat := 118140960795 + 6955876 * 2 ^ 59
def prefixEnd_6955876 : Nat := 4983230072969 + 3 ^ 40 * 6955876 * 2
def baseEnd_6955876 : Nat := 3571707761073732336860515

theorem tailTrace_6955876 : CollatzResearch.WordTrace tailWord_6955876 prefixEnd_6955876 3571707761073732336860515 := by
  unfold tailWord_6955876
  simp only [CollatzResearch.WordTrace]
  refine ⟨126850820074028347943431741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169134426765371130591242321 126850820074028347943431741)
  ·
    refine ⟨47569057527760630478786903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126850820074028347943431741 47569057527760630478786903)
    ·
      refine ⟨71353586291640945718180355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47569057527760630478786903 71353586291640945718180355)
      ·
        refine ⟨107030379437461418577270533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71353586291640945718180355 107030379437461418577270533)
        ·
          refine ⟨20068196144524015983238225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107030379437461418577270533 20068196144524015983238225)
          ·
            refine ⟨15051147108393011987428669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20068196144524015983238225 15051147108393011987428669)
            ·
              refine ⟨5644180165647379495285751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15051147108393011987428669 5644180165647379495285751)
              ·
                refine ⟨8466270248471069242928627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644180165647379495285751 8466270248471069242928627)
                ·
                  refine ⟨12699405372706603864392941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466270248471069242928627 12699405372706603864392941)
                  ·
                    refine ⟨4762277014764976449147353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12699405372706603864392941 4762277014764976449147353)
                    ·
                      refine ⟨3571707761073732336860515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762277014764976449147353 3571707761073732336860515)
                      ·
                        rfl

theorem cell23_6955876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_6955876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955876 prefixEnd_6955876 := by exact prefixLift 6955876
  have htrace : WordTrace (prefixWord ++ tailWord_6955876) baseStart_6955876 baseEnd_6955876 := by
    simpa [prefixWord, tailWord_6955876, baseEnd_6955876] using wordTrace_append hprefix tailTrace_6955876
  have hstable : (prefixWord ++ tailWord_6955876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955876).length < 2 ^ (prefixWord ++ tailWord_6955876).sum := by decide
  have hdescent : baseEnd_6955876 < baseStart_6955876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955885 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6955885 : Nat := 118140960795 + 6955885 * 2 ^ 59
def prefixEnd_6955885 : Nat := 4983230072969 + 3 ^ 40 * 6955885 * 2
def baseEnd_6955885 : Nat := 3571712382399622801647973

theorem tailTrace_6955885 : CollatzResearch.WordTrace tailWord_6955885 prefixEnd_6955885 3571712382399622801647973 := by
  unfold tailWord_6955885
  simp only [CollatzResearch.WordTrace]
  refine ⟨253701968405024090423941109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169134645603349393615960739 253701968405024090423941109)
  ·
    refine ⟨23784559537971008477244479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253701968405024090423941109 23784559537971008477244479)
    ·
      refine ⟨35676839306956512715866719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23784559537971008477244479 35676839306956512715866719)
      ·
        refine ⟨53515258960434769073800079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35676839306956512715866719 53515258960434769073800079)
        ·
          refine ⟨80272888440652153610700119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53515258960434769073800079 80272888440652153610700119)
          ·
            refine ⟨120409332660978230416050179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80272888440652153610700119 120409332660978230416050179)
            ·
              refine ⟨180613998991467345624075269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120409332660978230416050179 180613998991467345624075269)
              ·
                refine ⟨33865124810900127304514113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180613998991467345624075269 33865124810900127304514113)
                ·
                  refine ⟨25398843608175095478385585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33865124810900127304514113 25398843608175095478385585)
                  ·
                    refine ⟨19049132706131321608789189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25398843608175095478385585 19049132706131321608789189)
                    ·
                      refine ⟨3571712382399622801647973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19049132706131321608789189 3571712382399622801647973)
                      ·
                        rfl

theorem cell23_6955885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6955885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955885 prefixEnd_6955885 := by exact prefixLift 6955885
  have htrace : WordTrace (prefixWord ++ tailWord_6955885) baseStart_6955885 baseEnd_6955885 := by
    simpa [prefixWord, tailWord_6955885, baseEnd_6955885] using wordTrace_append hprefix tailTrace_6955885
  have hstable : (prefixWord ++ tailWord_6955885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955885).length < 2 ^ (prefixWord ++ tailWord_6955885).sum := by decide
  have hdescent : baseEnd_6955885 < baseStart_6955885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955888 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_6955888 : Nat := 118140960795 + 6955888 * 2 ^ 59
def prefixEnd_6955888 : Nat := 4983230072969 + 3 ^ 40 * 6955888 * 2
def baseEnd_6955888 : Nat := 3571713922841586289910459

theorem tailTrace_6955888 : CollatzResearch.WordTrace tailWord_6955888 prefixEnd_6955888 3571713922841586289910459 := by
  unfold tailWord_6955888
  simp only [CollatzResearch.WordTrace]
  refine ⟨126851038912006610968150159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169134718549342147957533545 126851038912006610968150159)
  ·
    refine ⟨190276558368009916452225239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126851038912006610968150159 190276558368009916452225239)
    ·
      refine ⟨285414837552014874678337859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190276558368009916452225239 285414837552014874678337859)
      ·
        refine ⟨428122256328022312017506789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285414837552014874678337859 428122256328022312017506789)
        ·
          refine ⟨80272923061504183503282523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428122256328022312017506789 80272923061504183503282523)
          ·
            refine ⟨120409384592256275254923785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80272923061504183503282523 120409384592256275254923785)
            ·
              refine ⟨90307038444192206441192839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120409384592256275254923785 90307038444192206441192839)
              ·
                refine ⟨135460557666288309661789259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90307038444192206441192839 135460557666288309661789259)
                ·
                  refine ⟨203190836499432464492683889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135460557666288309661789259 203190836499432464492683889)
                  ·
                    refine ⟨152393127374574348369512917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203190836499432464492683889 152393127374574348369512917)
                    ·
                      refine ⟨3571713922841586289910459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152393127374574348369512917 3571713922841586289910459)
                      ·
                        rfl

theorem cell23_6955888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_6955888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955888 prefixEnd_6955888 := by exact prefixLift 6955888
  have htrace : WordTrace (prefixWord ++ tailWord_6955888) baseStart_6955888 baseEnd_6955888 := by
    simpa [prefixWord, tailWord_6955888, baseEnd_6955888] using wordTrace_append hprefix tailTrace_6955888
  have hstable : (prefixWord ++ tailWord_6955888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955888).length < 2 ^ (prefixWord ++ tailWord_6955888).sum := by decide
  have hdescent : baseEnd_6955888 < baseStart_6955888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955889 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 2, 2, 2]
def baseStart_6955889 : Nat := 118140960795 + 6955889 * 2 ^ 59
def prefixEnd_6955889 : Nat := 4983230072969 + 3 ^ 40 * 6955889 * 2
def baseEnd_6955889 : Nat := 3571714436322240785997955

theorem tailTrace_6955889 : CollatzResearch.WordTrace tailWord_6955889 prefixEnd_6955889 3571714436322240785997955 := by
  unfold tailWord_6955889
  simp only [CollatzResearch.WordTrace]
  refine ⟨253702114297009599107086721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169134742864673066071391147 253702114297009599107086721)
  ·
    refine ⟨190276585722757199330315041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253702114297009599107086721 190276585722757199330315041)
    ·
      refine ⟨142707439292067899497736281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190276585722757199330315041 142707439292067899497736281)
      ·
        refine ⟨107030579469050924623302211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142707439292067899497736281 107030579469050924623302211)
        ·
          refine ⟨160545869203576386934953317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107030579469050924623302211 160545869203576386934953317)
          ·
            refine ⟨30102350475670572550303747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160545869203576386934953317 30102350475670572550303747)
            ·
              refine ⟨45153525713505858825455621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30102350475670572550303747 45153525713505858825455621)
              ·
                refine ⟨8466286071282348529772929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45153525713505858825455621 8466286071282348529772929)
                ·
                  refine ⟨6349714553461761397329697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8466286071282348529772929 6349714553461761397329697)
                  ·
                    refine ⟨4762285915096321047997273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349714553461761397329697 4762285915096321047997273)
                    ·
                      refine ⟨3571714436322240785997955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762285915096321047997273 3571714436322240785997955)
                      ·
                        rfl

theorem cell23_6955889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_6955889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955889 prefixEnd_6955889 := by exact prefixLift 6955889
  have htrace : WordTrace (prefixWord ++ tailWord_6955889) baseStart_6955889 baseEnd_6955889 := by
    simpa [prefixWord, tailWord_6955889, baseEnd_6955889] using wordTrace_append hprefix tailTrace_6955889
  have hstable : (prefixWord ++ tailWord_6955889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955889).length < 2 ^ (prefixWord ++ tailWord_6955889).sum := by decide
  have hdescent : baseEnd_6955889 < baseStart_6955889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955898 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_6955898 : Nat := 118140960795 + 6955898 * 2 ^ 59
def prefixEnd_6955898 : Nat := 4983230072969 + 3 ^ 40 * 6955898 * 2
def baseEnd_6955898 : Nat := 3571719057648131250785413

theorem tailTrace_6955898 : CollatzResearch.WordTrace tailWord_6955898 prefixEnd_6955898 3571719057648131250785413 := by
  unfold tailWord_6955898
  simp only [CollatzResearch.WordTrace]
  refine ⟨63425610638494248411041087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169134961702651329096109565 63425610638494248411041087)
  ·
    refine ⟨95138415957741372616561631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63425610638494248411041087 95138415957741372616561631)
    ·
      refine ⟨142707623936612058924842447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95138415957741372616561631 142707623936612058924842447)
      ·
        refine ⟨214061435904918088387263671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142707623936612058924842447 214061435904918088387263671)
        ·
          refine ⟨321092153857377132580895507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214061435904918088387263671 321092153857377132580895507)
          ·
            refine ⟨481638230786065698871343261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321092153857377132580895507 481638230786065698871343261)
            ·
              refine ⟨180614336544774637076753723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481638230786065698871343261 180614336544774637076753723)
              ·
                refine ⟨270921504817161955615130585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180614336544774637076753723 270921504817161955615130585)
                ·
                  refine ⟨203191128612871466711347939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270921504817161955615130585 203191128612871466711347939)
                  ·
                    refine ⟨304786692919307200067021909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 203191128612871466711347939 304786692919307200067021909)
                    ·
                      refine ⟨3571719057648131250785413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 304786692919307200067021909 3571719057648131250785413)
                      ·
                        rfl

theorem cell23_6955898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_6955898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955898 prefixEnd_6955898 := by exact prefixLift 6955898
  have htrace : WordTrace (prefixWord ++ tailWord_6955898) baseStart_6955898 baseEnd_6955898 := by
    simpa [prefixWord, tailWord_6955898, baseEnd_6955898] using wordTrace_append hprefix tailTrace_6955898
  have hstable : (prefixWord ++ tailWord_6955898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955898).length < 2 ^ (prefixWord ++ tailWord_6955898).sum := by decide
  have hdescent : baseEnd_6955898 < baseStart_6955898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955925 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_6955925 : Nat := 118140960795 + 6955925 * 2 ^ 59
def prefixEnd_6955925 : Nat := 4983230072969 + 3 ^ 40 * 6955925 * 2
def baseEnd_6955925 : Nat := 1190577640541934215049263

theorem tailTrace_6955925 : CollatzResearch.WordTrace tailWord_6955925 prefixEnd_6955925 1190577640541934215049263 := by
  unfold tailWord_6955925
  simp only [CollatzResearch.WordTrace]
  refine ⟨253703427324879177255397229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169135618216586118170264819 253703427324879177255397229)
  ·
    refine ⟨95138785246829691470773961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253703427324879177255397229 95138785246829691470773961)
    ·
      refine ⟨71354088935122268603080471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95138785246829691470773961 71354088935122268603080471)
      ·
        refine ⟨107031133402683402904620707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71354088935122268603080471 107031133402683402904620707)
        ·
          refine ⟨160546700104025104356931061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107031133402683402904620707 160546700104025104356931061)
          ·
            refine ⟨15051253134752353533462287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160546700104025104356931061 15051253134752353533462287)
            ·
              refine ⟨22576879702128530300193431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15051253134752353533462287 22576879702128530300193431)
              ·
                refine ⟨33865319553192795450290147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22576879702128530300193431 33865319553192795450290147)
                ·
                  refine ⟨50797979329789193175435221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33865319553192795450290147 50797979329789193175435221)
                  ·
                    refine ⟨1190577640541934215049263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50797979329789193175435221 1190577640541934215049263)
                    ·
                      rfl

theorem cell23_6955925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_6955925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955925 prefixEnd_6955925 := by exact prefixLift 6955925
  have htrace : WordTrace (prefixWord ++ tailWord_6955925) baseStart_6955925 baseEnd_6955925 := by
    simpa [prefixWord, tailWord_6955925, baseEnd_6955925] using wordTrace_append hprefix tailTrace_6955925
  have hstable : (prefixWord ++ tailWord_6955925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955925).length < 2 ^ (prefixWord ++ tailWord_6955925).sum := by decide
  have hdescent : baseEnd_6955925 < baseStart_6955925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955945 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_6955945 : Nat := 118140960795 + 6955945 * 2 ^ 59
def prefixEnd_6955945 : Nat := 4983230072969 + 3 ^ 40 * 6955945 * 2
def baseEnd_6955945 : Nat := 3571743191238892566897697

theorem tailTrace_6955945 : CollatzResearch.WordTrace tailWord_6955945 prefixEnd_6955945 3571743191238892566897697 := by
  unfold tailWord_6955945
  simp only [CollatzResearch.WordTrace]
  refine ⟨253704156784806720671125289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169136104523204480447416859 253704156784806720671125289)
  ·
    refine ⟨190278117588605040503343967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253704156784806720671125289 190278117588605040503343967)
    ·
      refine ⟨285417176382907560755015951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190278117588605040503343967 285417176382907560755015951)
      ·
        refine ⟨428125764574361341132523927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285417176382907560755015951 428125764574361341132523927)
        ·
          refine ⟨642188646861542011698785891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428125764574361341132523927 642188646861542011698785891)
          ·
            refine ⟨963282970292313017548178837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642188646861542011698785891 963282970292313017548178837)
            ·
              refine ⟨45153889232452172697570883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 963282970292313017548178837 45153889232452172697570883)
              ·
                refine ⟨67730833848678259046356325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45153889232452172697570883 67730833848678259046356325)
                ·
                  refine ⟨12699531346627173571191811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67730833848678259046356325 12699531346627173571191811)
                  ·
                    refine ⟨19049297019940760356787717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12699531346627173571191811 19049297019940760356787717)
                    ·
                      refine ⟨3571743191238892566897697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19049297019940760356787717 3571743191238892566897697)
                      ·
                        rfl

theorem cell23_6955945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_6955945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955945 prefixEnd_6955945 := by exact prefixLift 6955945
  have htrace : WordTrace (prefixWord ++ tailWord_6955945) baseStart_6955945 baseEnd_6955945 := by
    simpa [prefixWord, tailWord_6955945, baseEnd_6955945] using wordTrace_append hprefix tailTrace_6955945
  have hstable : (prefixWord ++ tailWord_6955945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955945).length < 2 ^ (prefixWord ++ tailWord_6955945).sum := by decide
  have hdescent : baseEnd_6955945 < baseStart_6955945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955962 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2]
def baseStart_6955962 : Nat := 118140960795 + 6955962 * 2 ^ 59
def prefixEnd_6955962 : Nat := 4983230072969 + 3 ^ 40 * 6955962 * 2
def baseEnd_6955962 : Nat := 3571751920410019000385119

theorem tailTrace_6955962 : CollatzResearch.WordTrace tailWord_6955962 prefixEnd_6955962 3571751920410019000385119 := by
  unfold tailWord_6955962
  simp only [CollatzResearch.WordTrace]
  refine ⟨63426194206436283143623535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169136517883830088382996093 63426194206436283143623535)
  ·
    refine ⟨95139291309654424715435303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63426194206436283143623535 95139291309654424715435303)
    ·
      refine ⟨142708936964481637073152955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95139291309654424715435303 142708936964481637073152955)
      ·
        refine ⟨214063405446722455609729433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142708936964481637073152955 214063405446722455609729433)
        ·
          refine ⟨160547554085041841707297075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214063405446722455609729433 160547554085041841707297075)
          ·
            refine ⟨240821331127562762560945613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160547554085041841707297075 240821331127562762560945613)
            ·
              refine ⟨90307999172836035960354605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240821331127562762560945613 90307999172836035960354605)
              ·
                refine ⟨33865499689813513485132977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90307999172836035960354605 33865499689813513485132977)
                ·
                  refine ⟨25399124767360135113849733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33865499689813513485132977 25399124767360135113849733)
                  ·
                    refine ⟨4762335893880025333846825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25399124767360135113849733 4762335893880025333846825)
                    ·
                      refine ⟨3571751920410019000385119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762335893880025333846825 3571751920410019000385119)
                      ·
                        rfl

theorem cell23_6955962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_6955962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955962 prefixEnd_6955962 := by exact prefixLift 6955962
  have htrace : WordTrace (prefixWord ++ tailWord_6955962) baseStart_6955962 baseEnd_6955962 := by
    simpa [prefixWord, tailWord_6955962, baseEnd_6955962] using wordTrace_append hprefix tailTrace_6955962
  have hstable : (prefixWord ++ tailWord_6955962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955962).length < 2 ^ (prefixWord ++ tailWord_6955962).sum := by decide
  have hdescent : baseEnd_6955962 < baseStart_6955962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955982 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_6955982 : Nat := 118140960795 + 6955982 * 2 ^ 59
def prefixEnd_6955982 : Nat := 4983230072969 + 3 ^ 40 * 6955982 * 2
def baseEnd_6955982 : Nat := 3571762190023108922135027

theorem tailTrace_6955982 : CollatzResearch.WordTrace tailWord_6955982 prefixEnd_6955982 3571762190023108922135027 := by
  unfold tailWord_6955982
  simp only [CollatzResearch.WordTrace]
  refine ⟨31713188285709084498777775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169137004190448450660148133 31713188285709084498777775)
  ·
    refine ⟨47569782428563626748166663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31713188285709084498777775 47569782428563626748166663)
    ·
      refine ⟨71354673642845440122249995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47569782428563626748166663 71354673642845440122249995)
      ·
        refine ⟨107032010464268160183374993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71354673642845440122249995 107032010464268160183374993)
        ·
          refine ⟨80274007848201120137531245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107032010464268160183374993 80274007848201120137531245)
          ·
            refine ⟨30102752943075420051574217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80274007848201120137531245 30102752943075420051574217)
            ·
              refine ⟨22577064707306565038680663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30102752943075420051574217 22577064707306565038680663)
              ·
                refine ⟨33865597060959847558020995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22577064707306565038680663 33865597060959847558020995)
                ·
                  refine ⟨50798395591439771337031493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33865597060959847558020995 50798395591439771337031493)
                  ·
                    refine ⟨9524699173394957125693405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50798395591439771337031493 9524699173394957125693405)
                    ·
                      refine ⟨3571762190023108922135027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524699173394957125693405 3571762190023108922135027)
                      ·
                        rfl

theorem cell23_6955982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_6955982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955982 prefixEnd_6955982 := by exact prefixLift 6955982
  have htrace : WordTrace (prefixWord ++ tailWord_6955982) baseStart_6955982 baseEnd_6955982 := by
    simpa [prefixWord, tailWord_6955982, baseEnd_6955982] using wordTrace_append hprefix tailTrace_6955982
  have hstable : (prefixWord ++ tailWord_6955982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955982).length < 2 ^ (prefixWord ++ tailWord_6955982).sum := by decide
  have hdescent : baseEnd_6955982 < baseStart_6955982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6955999 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_6955999 : Nat := 118140960795 + 6955999 * 2 ^ 59
def prefixEnd_6955999 : Nat := 4983230072969 + 3 ^ 40 * 6955999 * 2
def baseEnd_6955999 : Nat := 3571770919194235355622449

theorem tailTrace_6955999 : CollatzResearch.WordTrace tailWord_6955999 prefixEnd_6955999 3571770919194235355622449 := by
  unfold tailWord_6955999
  simp only [CollatzResearch.WordTrace]
  refine ⟨253706126326611087893591051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169137417551074058595727367 253706126326611087893591051)
  ·
    refine ⟨380559189489916631840386577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253706126326611087893591051 380559189489916631840386577)
    ·
      refine ⟨285419392117437473880289933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380559189489916631840386577 285419392117437473880289933)
      ·
        refine ⟨107032272044039052705108725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285419392117437473880289933 107032272044039052705108725)
        ·
          refine ⟨10034275504128661191103943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107032272044039052705108725 10034275504128661191103943)
          ·
            refine ⟨15051413256192991786655915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10034275504128661191103943 15051413256192991786655915)
            ·
              refine ⟨22577119884289487679983873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15051413256192991786655915 22577119884289487679983873)
              ·
                refine ⟨16932839913217115759987905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22577119884289487679983873 16932839913217115759987905)
                ·
                  refine ⟨12699629934912836819990929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16932839913217115759987905 12699629934912836819990929)
                  ·
                    refine ⟨9524722451184627614993197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12699629934912836819990929 9524722451184627614993197)
                    ·
                      refine ⟨3571770919194235355622449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524722451184627614993197 3571770919194235355622449)
                      ·
                        rfl

theorem cell23_6955999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_6955999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6955999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6955999 prefixEnd_6955999 := by exact prefixLift 6955999
  have htrace : WordTrace (prefixWord ++ tailWord_6955999) baseStart_6955999 baseEnd_6955999 := by
    simpa [prefixWord, tailWord_6955999, baseEnd_6955999] using wordTrace_append hprefix tailTrace_6955999
  have hstable : (prefixWord ++ tailWord_6955999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6955999).length < 2 ^ (prefixWord ++ tailWord_6955999).sum := by decide
  have hdescent : baseEnd_6955999 < baseStart_6955999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6955999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956063 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 1, 1, 3]
def baseStart_6956063 : Nat := 118140960795 + 6956063 * 2 ^ 59
def prefixEnd_6956063 : Nat := 4983230072969 + 3 ^ 40 * 6956063 * 2
def baseEnd_6956063 : Nat := 3571803781956123105222155

theorem tailTrace_6956063 : CollatzResearch.WordTrace tailWord_6956063 prefixEnd_6956063 3571803781956123105222155 := by
  unfold tailWord_6956063
  simp only [CollatzResearch.WordTrace]
  refine ⟨253708460598379226823920843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169138973732252817882613895 253708460598379226823920843)
  ·
    refine ⟨380562690897568840235881265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253708460598379226823920843 380562690897568840235881265)
    ·
      refine ⟨285422018173176630176910949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380562690897568840235881265 285422018173176630176910949)
      ·
        refine ⟨53516628407470618158170803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285422018173176630176910949 53516628407470618158170803)
        ·
          refine ⟨80274942611205927237256205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53516628407470618158170803 80274942611205927237256205)
          ·
            refine ⟨30103103479202222713971077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80274942611205927237256205 30103103479202222713971077)
            ·
              refine ⟨5644331902350416758869577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30103103479202222713971077 5644331902350416758869577)
              ·
                refine ⟨4233248926762812569152183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644331902350416758869577 4233248926762812569152183)
                ·
                  refine ⟨6349873390144218853728275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233248926762812569152183 6349873390144218853728275)
                  ·
                    refine ⟨9524810085216328280592413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6349873390144218853728275 9524810085216328280592413)
                    ·
                      refine ⟨3571803781956123105222155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524810085216328280592413 3571803781956123105222155)
                      ·
                        rfl

theorem cell23_6956063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_6956063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956063 prefixEnd_6956063 := by exact prefixLift 6956063
  have htrace : WordTrace (prefixWord ++ tailWord_6956063) baseStart_6956063 baseEnd_6956063 := by
    simpa [prefixWord, tailWord_6956063, baseEnd_6956063] using wordTrace_append hprefix tailTrace_6956063
  have hstable : (prefixWord ++ tailWord_6956063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956063).length < 2 ^ (prefixWord ++ tailWord_6956063).sum := by decide
  have hdescent : baseEnd_6956063 < baseStart_6956063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956089 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6956089 : Nat := 118140960795 + 6956089 * 2 ^ 59
def prefixEnd_6956089 : Nat := 4983230072969 + 3 ^ 40 * 6956089 * 2
def baseEnd_6956089 : Nat := 3571817132453140003497035

theorem tailTrace_6956089 : CollatzResearch.WordTrace tailWord_6956089 prefixEnd_6956089 3571817132453140003497035 := by
  unfold tailWord_6956089
  simp only [CollatzResearch.WordTrace]
  refine ⟨253709408896285033264367321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169139605930856688842911547 253709408896285033264367321)
  ·
    refine ⟨190282056672213774948275491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253709408896285033264367321 190282056672213774948275491)
    ·
      refine ⟨285423085008320662422413237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190282056672213774948275491 285423085008320662422413237)
      ·
        refine ⟨26758414219530062102101241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285423085008320662422413237 26758414219530062102101241)
        ·
          refine ⟨20068810664647546576575931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26758414219530062102101241 20068810664647546576575931)
          ·
            refine ⟨30103215996971319864863897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20068810664647546576575931 30103215996971319864863897)
            ·
              refine ⟨22577411997728489898647923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30103215996971319864863897 22577411997728489898647923)
              ·
                refine ⟨33866117996592734847971885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22577411997728489898647923 33866117996592734847971885)
                ·
                  refine ⟨12699794248722275567989457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33866117996592734847971885 12699794248722275567989457)
                  ·
                    refine ⟨9524845686541706675992093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12699794248722275567989457 9524845686541706675992093)
                    ·
                      refine ⟨3571817132453140003497035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524845686541706675992093 3571817132453140003497035)
                      ·
                        rfl

theorem cell23_6956089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6956089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956089 prefixEnd_6956089 := by exact prefixLift 6956089
  have htrace : WordTrace (prefixWord ++ tailWord_6956089) baseStart_6956089 baseEnd_6956089 := by
    simpa [prefixWord, tailWord_6956089, baseEnd_6956089] using wordTrace_append hprefix tailTrace_6956089
  have hstable : (prefixWord ++ tailWord_6956089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956089).length < 2 ^ (prefixWord ++ tailWord_6956089).sum := by decide
  have hdescent : baseEnd_6956089 < baseStart_6956089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956103 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_6956103 : Nat := 118140960795 + 6956103 * 2 ^ 59
def prefixEnd_6956103 : Nat := 4983230072969 + 3 ^ 40 * 6956103 * 2
def baseEnd_6956103 : Nat := 3571824321182302948721971

theorem tailTrace_6956103 : CollatzResearch.WordTrace tailWord_6956103 prefixEnd_6956103 3571824321182302948721971 := by
  unfold tailWord_6956103
  simp only [CollatzResearch.WordTrace]
  refine ⟨253709919518234313655376963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169139946345489542436917975 253709919518234313655376963)
  ·
    refine ⟨380564879277351470483065445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253709919518234313655376963 380564879277351470483065445)
    ·
      refine ⟨71355914864503400715574771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380564879277351470483065445 71355914864503400715574771)
      ·
        refine ⟨107033872296755101073362157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71355914864503400715574771 107033872296755101073362157)
        ·
          refine ⟨40137702111283162902510809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107033872296755101073362157 40137702111283162902510809)
          ·
            refine ⟨30103276583462372176883107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40137702111283162902510809 30103276583462372176883107)
            ·
              refine ⟨45154914875193558265324661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30103276583462372176883107 45154914875193558265324661)
              ·
                refine ⟨4233273269549396087374187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45154914875193558265324661 4233273269549396087374187)
                ·
                  refine ⟨6349909904324094131061281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233273269549396087374187 6349909904324094131061281)
                  ·
                    refine ⟨4762432428243070598295961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349909904324094131061281 4762432428243070598295961)
                    ·
                      refine ⟨3571824321182302948721971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762432428243070598295961 3571824321182302948721971)
                      ·
                        rfl

theorem cell23_6956103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_6956103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956103 prefixEnd_6956103 := by exact prefixLift 6956103
  have htrace : WordTrace (prefixWord ++ tailWord_6956103) baseStart_6956103 baseEnd_6956103 := by
    simpa [prefixWord, tailWord_6956103, baseEnd_6956103] using wordTrace_append hprefix tailTrace_6956103
  have hstable : (prefixWord ++ tailWord_6956103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956103).length < 2 ^ (prefixWord ++ tailWord_6956103).sum := by decide
  have hdescent : baseEnd_6956103 < baseStart_6956103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956105 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 9]
def baseStart_6956105 : Nat := 118140960795 + 6956105 * 2 ^ 59
def prefixEnd_6956105 : Nat := 4983230072969 + 3 ^ 40 * 6956105 * 2
def baseEnd_6956105 : Nat := 1190608449381203980298987

theorem tailTrace_6956105 : CollatzResearch.WordTrace tailWord_6956105 prefixEnd_6956105 1190608449381203980298987 := by
  unfold tailWord_6956105
  simp only [CollatzResearch.WordTrace]
  refine ⟨253709992464227067996949769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169139994976151378664633179 253709992464227067996949769)
  ·
    refine ⟨190282494348170300997712327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253709992464227067996949769 190282494348170300997712327)
    ·
      refine ⟨285423741522255451496568491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190282494348170300997712327 285423741522255451496568491)
      ·
        refine ⟨428135612283383177244852737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285423741522255451496568491 428135612283383177244852737)
        ·
          refine ⟨321101709212537382933639553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428135612283383177244852737 321101709212537382933639553)
          ·
            refine ⟨240826281909403037200229665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321101709212537382933639553 240826281909403037200229665)
            ·
              refine ⟨180619711432052277900172249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240826281909403037200229665 180619711432052277900172249)
              ·
                refine ⟨135464783574039208425129187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180619711432052277900172249 135464783574039208425129187)
                ·
                  refine ⟨203197175361058812637693781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135464783574039208425129187 203197175361058812637693781)
                  ·
                    refine ⟨1190608449381203980298987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 203197175361058812637693781 1190608449381203980298987)
                    ·
                      rfl

theorem cell23_6956105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_6956105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956105 prefixEnd_6956105 := by exact prefixLift 6956105
  have htrace : WordTrace (prefixWord ++ tailWord_6956105) baseStart_6956105 baseEnd_6956105 := by
    simpa [prefixWord, tailWord_6956105, baseEnd_6956105] using wordTrace_append hprefix tailTrace_6956105
  have hstable : (prefixWord ++ tailWord_6956105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956105).length < 2 ^ (prefixWord ++ tailWord_6956105).sum := by decide
  have hdescent : baseEnd_6956105 < baseStart_6956105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956106 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_6956106 : Nat := 118140960795 + 6956106 * 2 ^ 59
def prefixEnd_6956106 : Nat := 4983230072969 + 3 ^ 40 * 6956106 * 2
def baseEnd_6956106 : Nat := 3571825861624266436984457

theorem tailTrace_6956106 : CollatzResearch.WordTrace tailWord_6956106 prefixEnd_6956106 3571825861624266436984457 := by
  unfold tailWord_6956106
  simp only [CollatzResearch.WordTrace]
  refine ⟨63427507234305861291934043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169140019291482296778490781 63427507234305861291934043)
  ·
    refine ⟨95141260851458791937901065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63427507234305861291934043 95141260851458791937901065)
    ·
      refine ⟨71355945638594093953425799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95141260851458791937901065 71355945638594093953425799)
      ·
        refine ⟨107033918457891140930138699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71355945638594093953425799 107033918457891140930138699)
        ·
          refine ⟨160550877686836711395208049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107033918457891140930138699 160550877686836711395208049)
          ·
            refine ⟨120413158265127533546406037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160550877686836711395208049 120413158265127533546406037)
            ·
              refine ⟨5644366793677853134987783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120413158265127533546406037 5644366793677853134987783)
              ·
                refine ⟨8466550190516779702481675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644366793677853134987783 8466550190516779702481675)
                ·
                  refine ⟨12699825285775169553722513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466550190516779702481675 12699825285775169553722513)
                  ·
                    refine ⟨9524868964331377165291885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12699825285775169553722513 9524868964331377165291885)
                    ·
                      refine ⟨3571825861624266436984457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9524868964331377165291885 3571825861624266436984457)
                      ·
                        rfl

theorem cell23_6956106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_6956106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956106 prefixEnd_6956106 := by exact prefixLift 6956106
  have htrace : WordTrace (prefixWord ++ tailWord_6956106) baseStart_6956106 baseEnd_6956106 := by
    simpa [prefixWord, tailWord_6956106, baseEnd_6956106] using wordTrace_append hprefix tailTrace_6956106
  have hstable : (prefixWord ++ tailWord_6956106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956106).length < 2 ^ (prefixWord ++ tailWord_6956106).sum := by decide
  have hdescent : baseEnd_6956106 < baseStart_6956106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956129 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_6956129 : Nat := 118140960795 + 6956129 * 2 ^ 59
def prefixEnd_6956129 : Nat := 4983230072969 + 3 ^ 40 * 6956129 * 2
def baseEnd_6956129 : Nat := 3571837671679319846996851

theorem tailTrace_6956129 : CollatzResearch.WordTrace tailWord_6956129 prefixEnd_6956129 3571837671679319846996851 := by
  unfold tailWord_6956129
  simp only [CollatzResearch.WordTrace]
  refine ⟨253710867816140120095823441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169140578544093413397215627 253710867816140120095823441)
  ·
    refine ⟨190283150862105090071867581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253710867816140120095823441 190283150862105090071867581)
    ·
      refine ⟨71356181573289408776950343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190283150862105090071867581 71356181573289408776950343)
      ·
        refine ⟨107034272359934113165425515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71356181573289408776950343 107034272359934113165425515)
        ·
          refine ⟨160551408539901169748138273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107034272359934113165425515 160551408539901169748138273)
          ·
            refine ⟨120413556404925877311103705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160551408539901169748138273 120413556404925877311103705)
            ·
              refine ⟨90310167303694407983327779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120413556404925877311103705 90310167303694407983327779)
              ·
                refine ⟨135465250955541611974991669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90310167303694407983327779 135465250955541611974991669)
                ·
                  refine ⟨12699867277082026122655469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135465250955541611974991669 12699867277082026122655469)
                  ·
                    refine ⟨4762450228905759795995801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12699867277082026122655469 4762450228905759795995801)
                    ·
                      refine ⟨3571837671679319846996851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762450228905759795995801 3571837671679319846996851)
                      ·
                        rfl

theorem cell23_6956129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_6956129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956129 prefixEnd_6956129 := by exact prefixLift 6956129
  have htrace : WordTrace (prefixWord ++ tailWord_6956129) baseStart_6956129 baseEnd_6956129 := by
    simpa [prefixWord, tailWord_6956129, baseEnd_6956129] using wordTrace_append hprefix tailTrace_6956129
  have hstable : (prefixWord ++ tailWord_6956129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956129).length < 2 ^ (prefixWord ++ tailWord_6956129).sum := by decide
  have hdescent : baseEnd_6956129 < baseStart_6956129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956172 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6956172 : Nat := 118140960795 + 6956172 * 2 ^ 59
def prefixEnd_6956172 : Nat := 4983230072969 + 3 ^ 40 * 6956172 * 2
def baseEnd_6956172 : Nat := 3571859751347463178759153

theorem tailTrace_6956172 : CollatzResearch.WordTrace tailWord_6956172 prefixEnd_6956172 3571859751347463178759153 := by
  unfold tailWord_6956172
  simp only [CollatzResearch.WordTrace]
  refine ⟨126856218077492169219819385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169141624103322892293092513 126856218077492169219819385)
  ·
    refine ⟨95142163558119126914864539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126856218077492169219819385 95142163558119126914864539)
    ·
      refine ⟨142713245337178690372296809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95142163558119126914864539 142713245337178690372296809)
      ·
        refine ⟨107034934002884017779222607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142713245337178690372296809 107034934002884017779222607)
        ·
          refine ⟨160552401004326026668833911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107034934002884017779222607 160552401004326026668833911)
          ·
            refine ⟨240828601506489040003250867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160552401004326026668833911 240828601506489040003250867)
            ·
              refine ⟨361242902259733560004876301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240828601506489040003250867 361242902259733560004876301)
              ·
                refine ⟨135466088347400085001828613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361242902259733560004876301 135466088347400085001828613)
                ·
                  refine ⟨25399891565137515937842865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135466088347400085001828613 25399891565137515937842865)
                  ·
                    refine ⟨19049918673853136953382149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25399891565137515937842865 19049918673853136953382149)
                    ·
                      refine ⟨3571859751347463178759153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19049918673853136953382149 3571859751347463178759153)
                      ·
                        rfl

theorem cell23_6956172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6956172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956172 prefixEnd_6956172 := by exact prefixLift 6956172
  have htrace : WordTrace (prefixWord ++ tailWord_6956172) baseStart_6956172 baseEnd_6956172 := by
    simpa [prefixWord, tailWord_6956172, baseEnd_6956172] using wordTrace_append hprefix tailTrace_6956172
  have hstable : (prefixWord ++ tailWord_6956172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956172).length < 2 ^ (prefixWord ++ tailWord_6956172).sum := by decide
  have hdescent : baseEnd_6956172 < baseStart_6956172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956193 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6956193 : Nat := 118140960795 + 6956193 * 2 ^ 59
def prefixEnd_6956193 : Nat := 4983230072969 + 3 ^ 40 * 6956193 * 2
def baseEnd_6956193 : Nat := 3571870534441207596596557

theorem tailTrace_6956193 : CollatzResearch.WordTrace tailWord_6956193 prefixEnd_6956193 3571870534441207596596557 := by
  unfold tailWord_6956193
  simp only [CollatzResearch.WordTrace]
  refine ⟨253713202087908259026153233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169142134725272172684102155 253713202087908259026153233)
  ·
    refine ⟨190284901565931194269614925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253713202087908259026153233 190284901565931194269614925)
    ·
      refine ⟨71356838087224197851105597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190284901565931194269614925 71356838087224197851105597)
      ·
        refine ⟨26758814282709074194164599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71356838087224197851105597 26758814282709074194164599)
        ·
          refine ⟨40138221424063611291246899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26758814282709074194164599 40138221424063611291246899)
          ·
            refine ⟨60207332136095416936870349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40138221424063611291246899 60207332136095416936870349)
            ·
              refine ⟨22577749551035781351326381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60207332136095416936870349 22577749551035781351326381)
              ·
                refine ⟨8466656081638418006747393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22577749551035781351326381 8466656081638418006747393)
                ·
                  refine ⟨6349992061228813505060545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8466656081638418006747393 6349992061228813505060545)
                  ·
                    refine ⟨4762494045921610128795409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6349992061228813505060545 4762494045921610128795409)
                    ·
                      refine ⟨3571870534441207596596557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762494045921610128795409 3571870534441207596596557)
                      ·
                        rfl

theorem cell23_6956193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6956193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956193 prefixEnd_6956193 := by exact prefixLift 6956193
  have htrace : WordTrace (prefixWord ++ tailWord_6956193) baseStart_6956193 baseEnd_6956193 := by
    simpa [prefixWord, tailWord_6956193, baseEnd_6956193] using wordTrace_append hprefix tailTrace_6956193
  have hstable : (prefixWord ++ tailWord_6956193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956193).length < 2 ^ (prefixWord ++ tailWord_6956193).sum := by decide
  have hdescent : baseEnd_6956193 < baseStart_6956193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956214 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6956214 : Nat := 118140960795 + 6956214 * 2 ^ 59
def prefixEnd_6956214 : Nat := 4983230072969 + 3 ^ 40 * 6956214 * 2
def baseEnd_6956214 : Nat := 3571881317534952014433961

theorem tailTrace_6956214 : CollatzResearch.WordTrace tailWord_6956214 prefixEnd_6956214 3571881317534952014433961 := by
  unfold tailWord_6956214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15857123001302011225791731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169142645347221453075111797 15857123001302011225791731)
  ·
    refine ⟨23785684501953016838687597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15857123001302011225791731 23785684501953016838687597)
    ·
      refine ⟨8919631688232381314507849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23785684501953016838687597 8919631688232381314507849)
      ·
        refine ⟨6689723766174285985880887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8919631688232381314507849 6689723766174285985880887)
        ·
          refine ⟨10034585649261428978821331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6689723766174285985880887 10034585649261428978821331)
          ·
            refine ⟨15051878473892143468231997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10034585649261428978821331 15051878473892143468231997)
            ·
              refine ⟨5644454427709553800586999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15051878473892143468231997 5644454427709553800586999)
              ·
                refine ⟨8466681641564330700880499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644454427709553800586999 8466681641564330700880499)
                ·
                  refine ⟨12700022462346496051320749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466681641564330700880499 12700022462346496051320749)
                  ·
                    refine ⟨4762508423379936019245281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12700022462346496051320749 4762508423379936019245281)
                    ·
                      refine ⟨3571881317534952014433961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762508423379936019245281 3571881317534952014433961)
                      ·
                        rfl

theorem cell23_6956214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6956214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956214 prefixEnd_6956214 := by exact prefixLift 6956214
  have htrace : WordTrace (prefixWord ++ tailWord_6956214) baseStart_6956214 baseEnd_6956214 := by
    simpa [prefixWord, tailWord_6956214, baseEnd_6956214] using wordTrace_append hprefix tailTrace_6956214
  have hstable : (prefixWord ++ tailWord_6956214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956214).length < 2 ^ (prefixWord ++ tailWord_6956214).sum := by decide
  have hdescent : baseEnd_6956214 < baseStart_6956214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956263 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 2, 5]
def baseStart_6956263 : Nat := 118140960795 + 6956263 * 2 ^ 59
def prefixEnd_6956263 : Nat := 4983230072969 + 3 ^ 40 * 6956263 * 2
def baseEnd_6956263 : Nat := 1190635492695674107573745

theorem tailTrace_6956263 : CollatzResearch.WordTrace tailWord_6956263 prefixEnd_6956263 1190635492695674107573745 := by
  unfold tailWord_6956263
  simp only [CollatzResearch.WordTrace]
  refine ⟨253715755197654660981201443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169143836798436440654134295 253715755197654660981201443)
  ·
    refine ⟨380573632796481991471802165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253715755197654660981201443 380573632796481991471802165)
    ·
      refine ⟨35678778074670186700481453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 380573632796481991471802165 35678778074670186700481453)
      ·
        refine ⟨13379541778001320012680545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35678778074670186700481453 13379541778001320012680545)
        ·
          refine ⟨10034656333500990009510409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13379541778001320012680545 10034656333500990009510409)
          ·
            refine ⟨7525992250125742507132807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10034656333500990009510409 7525992250125742507132807)
            ·
              refine ⟨11288988375188613760699211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7525992250125742507132807 11288988375188613760699211)
              ·
                refine ⟨16933482562782920641048817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11288988375188613760699211 16933482562782920641048817)
                ·
                  refine ⟨12700111922087190480786613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16933482562782920641048817 12700111922087190480786613)
                  ·
                    refine ⟨1190635492695674107573745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12700111922087190480786613 1190635492695674107573745)
                    ·
                      rfl

theorem cell23_6956263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_6956263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956263 prefixEnd_6956263 := by exact prefixLift 6956263
  have htrace : WordTrace (prefixWord ++ tailWord_6956263) baseStart_6956263 baseEnd_6956263 := by
    simpa [prefixWord, tailWord_6956263, baseEnd_6956263] using wordTrace_append hprefix tailTrace_6956263
  have hstable : (prefixWord ++ tailWord_6956263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956263).length < 2 ^ (prefixWord ++ tailWord_6956263).sum := by decide
  have hdescent : baseEnd_6956263 < baseStart_6956263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956266 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_6956266 : Nat := 118140960795 + 6956266 * 2 ^ 59
def prefixEnd_6956266 : Nat := 4983230072969 + 3 ^ 40 * 6956266 * 2
def baseEnd_6956266 : Nat := 3571908018528985810983721

theorem tailTrace_6956266 : CollatzResearch.WordTrace tailWord_6956266 prefixEnd_6956266 3571908018528985810983721 := by
  unfold tailWord_6956266
  simp only [CollatzResearch.WordTrace]
  refine ⟨63428966154160948123390163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169143909744429194995707101 63428966154160948123390163)
  ·
    refine ⟨95143449231241422185085245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63428966154160948123390163 95143449231241422185085245)
    ·
      refine ⟨35678793461715533319406967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95143449231241422185085245 35678793461715533319406967)
      ·
        refine ⟨53518190192573299979110451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35678793461715533319406967 53518190192573299979110451)
        ·
          refine ⟨80277285288859949968665677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53518190192573299979110451 80277285288859949968665677)
          ·
            refine ⟨30103981983322481238249629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80277285288859949968665677 30103981983322481238249629)
            ·
              refine ⟨11288993243745930464343611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30103981983322481238249629 11288993243745930464343611)
              ·
                refine ⟨16933489865618895696515417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11288993243745930464343611 16933489865618895696515417)
                ·
                  refine ⟨12700117399214171772386563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16933489865618895696515417 12700117399214171772386563)
                  ·
                    refine ⟨19050176098821257658579845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12700117399214171772386563 19050176098821257658579845)
                    ·
                      refine ⟨3571908018528985810983721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19050176098821257658579845 3571908018528985810983721)
                      ·
                        rfl

theorem cell23_6956266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_6956266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956266 prefixEnd_6956266 := by exact prefixLift 6956266
  have htrace : WordTrace (prefixWord ++ tailWord_6956266) baseStart_6956266 baseEnd_6956266 := by
    simpa [prefixWord, tailWord_6956266, baseEnd_6956266] using wordTrace_append hprefix tailTrace_6956266
  have hstable : (prefixWord ++ tailWord_6956266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956266).length < 2 ^ (prefixWord ++ tailWord_6956266).sum := by decide
  have hdescent : baseEnd_6956266 < baseStart_6956266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956289 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 8]
def baseStart_6956289 : Nat := 118140960795 + 6956289 * 2 ^ 59
def prefixEnd_6956289 : Nat := 4983230072969 + 3 ^ 40 * 6956289 * 2
def baseEnd_6956289 : Nat := 396879980953782135666235

theorem tailTrace_6956289 : CollatzResearch.WordTrace tailWord_6956289 prefixEnd_6956289 396879980953782135666235 := by
  unfold tailWord_6956289
  simp only [CollatzResearch.WordTrace]
  refine ⟨253716703495560467421647921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169144468997040311614431947 253716703495560467421647921)
  ·
    refine ⟨190287527621670350566235941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253716703495560467421647921 190287527621670350566235941)
    ·
      refine ⟨35678911429063190731169239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190287527621670350566235941 35678911429063190731169239)
      ·
        refine ⟨53518367143594786096753859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35678911429063190731169239 53518367143594786096753859)
        ·
          refine ⟨80277550715392179145130789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53518367143594786096753859 80277550715392179145130789)
          ·
            refine ⟨15052040759136033589712023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80277550715392179145130789 15052040759136033589712023)
            ·
              refine ⟨22578061138704050384568035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15052040759136033589712023 22578061138704050384568035)
              ·
                refine ⟨33867091708056075576852053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22578061138704050384568035 33867091708056075576852053)
                ·
                  refine ⟨396879980953782135666235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33867091708056075576852053 396879980953782135666235)
                  ·
                    rfl

theorem cell23_6956289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 8].length) (baseStart_6956289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956289 prefixEnd_6956289 := by exact prefixLift 6956289
  have htrace : WordTrace (prefixWord ++ tailWord_6956289) baseStart_6956289 baseEnd_6956289 := by
    simpa [prefixWord, tailWord_6956289, baseEnd_6956289] using wordTrace_append hprefix tailTrace_6956289
  have hstable : (prefixWord ++ tailWord_6956289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956289).length < 2 ^ (prefixWord ++ tailWord_6956289).sum := by decide
  have hdescent : baseEnd_6956289 < baseStart_6956289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956369 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_6956369 : Nat := 118140960795 + 6956369 * 2 ^ 59
def prefixEnd_6956369 : Nat := 4983230072969 + 3 ^ 40 * 6956369 * 2
def baseEnd_6956369 : Nat := 3571960907036398907995747

theorem tailTrace_6956369 : CollatzResearch.WordTrace tailWord_6956369 prefixEnd_6956369 3571960907036398907995747 := by
  unfold tailWord_6956369
  simp only [CollatzResearch.WordTrace]
  refine ⟨253719621335270641084560161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169146414223513760723040107 253719621335270641084560161)
  ·
    refine ⟨190289716001452980813420121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253719621335270641084560161 190289716001452980813420121)
    ·
      refine ⟨142717287001089735610065091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190289716001452980813420121 142717287001089735610065091)
      ·
        refine ⟨214075930501634603415097637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142717287001089735610065091 214075930501634603415097637)
        ·
          refine ⟨40139236969056488140330807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214075930501634603415097637 40139236969056488140330807)
          ·
            refine ⟨60208855453584732210496211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40139236969056488140330807 60208855453584732210496211)
            ·
              refine ⟨90313283180377098315744317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60208855453584732210496211 90313283180377098315744317)
              ·
                refine ⟨33867481192641411868404119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90313283180377098315744317 33867481192641411868404119)
                ·
                  refine ⟨50801221788962117802606179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33867481192641411868404119 50801221788962117802606179)
                  ·
                    refine ⟨76201832683443176703909269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50801221788962117802606179 76201832683443176703909269)
                    ·
                      refine ⟨3571960907036398907995747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76201832683443176703909269 3571960907036398907995747)
                      ·
                        rfl

theorem cell23_6956369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_6956369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956369 prefixEnd_6956369 := by exact prefixLift 6956369
  have htrace : WordTrace (prefixWord ++ tailWord_6956369) baseStart_6956369 baseEnd_6956369 := by
    simpa [prefixWord, tailWord_6956369, baseEnd_6956369] using wordTrace_append hprefix tailTrace_6956369
  have hstable : (prefixWord ++ tailWord_6956369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956369).length < 2 ^ (prefixWord ++ tailWord_6956369).sum := by decide
  have hdescent : baseEnd_6956369 < baseStart_6956369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956373 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6956373 : Nat := 118140960795 + 6956373 * 2 ^ 59
def prefixEnd_6956373 : Nat := 4983230072969 + 3 ^ 40 * 6956373 * 2
def baseEnd_6956373 : Nat := 3571962960959016892345729

theorem tailTrace_6956373 : CollatzResearch.WordTrace tailWord_6956373 prefixEnd_6956373 3571962960959016892345729 := by
  unfold tailWord_6956373
  simp only [CollatzResearch.WordTrace]
  refine ⟨253719767227256149767705773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169146511484837433178470515 253719767227256149767705773)
  ·
    refine ⟨95144912710221056162889665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253719767227256149767705773 95144912710221056162889665)
    ·
      refine ⟨71358684532665792122167249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95144912710221056162889665 71358684532665792122167249)
      ·
        refine ⟨53519013399499344091625437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71358684532665792122167249 53519013399499344091625437)
        ·
          refine ⟨20069630024812254034359539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53519013399499344091625437 20069630024812254034359539)
          ·
            refine ⟨30104445037218381051539309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20069630024812254034359539 30104445037218381051539309)
            ·
              refine ⟨11289166888956892894327241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30104445037218381051539309 11289166888956892894327241)
              ·
                refine ⟨8466875166717669670745431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11289166888956892894327241 8466875166717669670745431)
                ·
                  refine ⟨12700312750076504506118147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466875166717669670745431 12700312750076504506118147)
                  ·
                    refine ⟨19050469125114756759177221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12700312750076504506118147 19050469125114756759177221)
                    ·
                      refine ⟨3571962960959016892345729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19050469125114756759177221 3571962960959016892345729)
                      ·
                        rfl

theorem cell23_6956373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6956373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956373 prefixEnd_6956373 := by exact prefixLift 6956373
  have htrace : WordTrace (prefixWord ++ tailWord_6956373) baseStart_6956373 baseEnd_6956373 := by
    simpa [prefixWord, tailWord_6956373, baseEnd_6956373] using wordTrace_append hprefix tailTrace_6956373
  have hstable : (prefixWord ++ tailWord_6956373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956373).length < 2 ^ (prefixWord ++ tailWord_6956373).sum := by decide
  have hdescent : baseEnd_6956373 < baseStart_6956373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956376 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_6956376 : Nat := 118140960795 + 6956376 * 2 ^ 59
def prefixEnd_6956376 : Nat := 4983230072969 + 3 ^ 40 * 6956376 * 2
def baseEnd_6956376 : Nat := 3571964501400980380608215

theorem tailTrace_6956376 : CollatzResearch.WordTrace tailWord_6956376 prefixEnd_6956376 3571964501400980380608215 := by
  unfold tailWord_6956376
  simp only [CollatzResearch.WordTrace]
  refine ⟨126859938323122640640032491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169146584430830187520043321 126859938323122640640032491)
  ·
    refine ⟨190289907484683960960048737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126859938323122640640032491 190289907484683960960048737)
    ·
      refine ⟨142717430613512970720036553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190289907484683960960048737 142717430613512970720036553)
      ·
        refine ⟨107038072960134728040027415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142717430613512970720036553 107038072960134728040027415)
        ·
          refine ⟨160557109440202092060041123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107038072960134728040027415 160557109440202092060041123)
          ·
            refine ⟨240835664160303138090061685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160557109440202092060041123 240835664160303138090061685)
            ·
              refine ⟨22578343515028419195943283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240835664160303138090061685 22578343515028419195943283)
              ·
                refine ⟨33867515272542628793914925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22578343515028419195943283 33867515272542628793914925)
                ·
                  refine ⟨12700318227203485797718097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33867515272542628793914925 12700318227203485797718097)
                  ·
                    refine ⟨9525238670402614348288573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12700318227203485797718097 9525238670402614348288573)
                    ·
                      refine ⟨3571964501400980380608215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9525238670402614348288573 3571964501400980380608215)
                      ·
                        rfl

theorem cell23_6956376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_6956376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956376 prefixEnd_6956376 := by exact prefixLift 6956376
  have htrace : WordTrace (prefixWord ++ tailWord_6956376) baseStart_6956376 baseEnd_6956376 := by
    simpa [prefixWord, tailWord_6956376, baseEnd_6956376] using wordTrace_append hprefix tailTrace_6956376
  have hstable : (prefixWord ++ tailWord_6956376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956376).length < 2 ^ (prefixWord ++ tailWord_6956376).sum := by decide
  have hdescent : baseEnd_6956376 < baseStart_6956376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956409 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 2, 7]
def baseStart_6956409 : Nat := 118140960795 + 6956409 * 2 ^ 59
def prefixEnd_6956409 : Nat := 4983230072969 + 3 ^ 40 * 6956409 * 2
def baseEnd_6956409 : Nat := 1190660482087526250498521

theorem tailTrace_6956409 : CollatzResearch.WordTrace tailWord_6956409 prefixEnd_6956409 1190660482087526250498521 := by
  unfold tailWord_6956409
  simp only [CollatzResearch.WordTrace]
  refine ⟨253721080255125727916016281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169147386836750485277344187 253721080255125727916016281)
  ·
    refine ⟨190290810191344295937012211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253721080255125727916016281 190290810191344295937012211)
    ·
      refine ⟨285436215287016443905518317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190290810191344295937012211 285436215287016443905518317)
      ·
        refine ⟨107038580732631166464569369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285436215287016443905518317 107038580732631166464569369)
        ·
          refine ⟨80278935549473374848427027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107038580732631166464569369 80278935549473374848427027)
          ·
            refine ⟨120418403324210062272640541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80278935549473374848427027 120418403324210062272640541)
            ·
              refine ⟨45156901246578773352240203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120418403324210062272640541 45156901246578773352240203)
              ·
                refine ⟨67735351869868160028360305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45156901246578773352240203 67735351869868160028360305)
                ·
                  refine ⟨50801513902401120021270229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67735351869868160028360305 50801513902401120021270229)
                  ·
                    refine ⟨1190660482087526250498521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50801513902401120021270229 1190660482087526250498521)
                    ·
                      rfl

theorem cell23_6956409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_6956409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956409 prefixEnd_6956409 := by exact prefixLift 6956409
  have htrace : WordTrace (prefixWord ++ tailWord_6956409) baseStart_6956409 baseEnd_6956409 := by
    simpa [prefixWord, tailWord_6956409, baseEnd_6956409] using wordTrace_append hprefix tailTrace_6956409
  have hstable : (prefixWord ++ tailWord_6956409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956409).length < 2 ^ (prefixWord ++ tailWord_6956409).sum := by decide
  have hdescent : baseEnd_6956409 < baseStart_6956409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956423 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_6956423 : Nat := 118140960795 + 6956423 * 2 ^ 59
def prefixEnd_6956423 : Nat := 4983230072969 + 3 ^ 40 * 6956423 * 2
def baseEnd_6956423 : Nat := 3571988634991741696720499

theorem tailTrace_6956423 : CollatzResearch.WordTrace tailWord_6956423 prefixEnd_6956423 3571988634991741696720499 := by
  unfold tailWord_6956423
  simp only [CollatzResearch.WordTrace]
  refine ⟨253721590877075008307025923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169147727251383338871350615 253721590877075008307025923)
  ·
    refine ⟨380582386315612512460538885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253721590877075008307025923 380582386315612512460538885)
    ·
      refine ⟨71359197434177346086351041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380582386315612512460538885 71359197434177346086351041)
      ·
        refine ⟨53519398075633009564763281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71359197434177346086351041 53519398075633009564763281)
        ·
          refine ⟨40139548556724757173572461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53519398075633009564763281 40139548556724757173572461)
          ·
            refine ⟨15052330708771783940089673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40139548556724757173572461 15052330708771783940089673)
            ·
              refine ⟨11289248031578837955067255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15052330708771783940089673 11289248031578837955067255)
              ·
                refine ⟨16933872047368256932600883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11289248031578837955067255 16933872047368256932600883)
                ·
                  refine ⟨25400808071052385398901325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16933872047368256932600883 25400808071052385398901325)
                  ·
                    refine ⟨9525303026644644524587997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25400808071052385398901325 9525303026644644524587997)
                    ·
                      refine ⟨3571988634991741696720499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9525303026644644524587997 3571988634991741696720499)
                      ·
                        rfl

theorem cell23_6956423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_6956423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956423 prefixEnd_6956423 := by exact prefixLift 6956423
  have htrace : WordTrace (prefixWord ++ tailWord_6956423) baseStart_6956423 baseEnd_6956423 := by
    simpa [prefixWord, tailWord_6956423, baseEnd_6956423] using wordTrace_append hprefix tailTrace_6956423
  have hstable : (prefixWord ++ tailWord_6956423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956423).length < 2 ^ (prefixWord ++ tailWord_6956423).sum := by decide
  have hdescent : baseEnd_6956423 < baseStart_6956423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956439 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 8]
def baseStart_6956439 : Nat := 118140960795 + 6956439 * 2 ^ 59
def prefixEnd_6956439 : Nat := 4983230072969 + 3 ^ 40 * 6956439 * 2
def baseEnd_6956439 : Nat := 1190665616894071211373475

theorem tailTrace_6956439 : CollatzResearch.WordTrace tailWord_6956439 prefixEnd_6956439 1190665616894071211373475 := by
  unfold tailWord_6956439
  simp only [CollatzResearch.WordTrace]
  refine ⟨253722174445017043039608371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169148116296678028693072247 253722174445017043039608371)
  ·
    refine ⟨380583261667525564559412557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253722174445017043039608371 380583261667525564559412557)
    ·
      refine ⟨142718723125322086709779709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380583261667525564559412557 142718723125322086709779709)
      ·
        refine ⟨53519521171995782516167391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142718723125322086709779709 53519521171995782516167391)
        ·
          refine ⟨80279281757993673774251087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53519521171995782516167391 80279281757993673774251087)
          ·
            refine ⟨120418922636990510661376631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80279281757993673774251087 120418922636990510661376631)
            ·
              refine ⟨180628383955485765992064947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120418922636990510661376631 180628383955485765992064947)
              ·
                refine ⟨270942575933228648988097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180628383955485765992064947 270942575933228648988097421)
                ·
                  refine ⟨101603465974960743370536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270942575933228648988097421 101603465974960743370536533)
                  ·
                    refine ⟨1190665616894071211373475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101603465974960743370536533 1190665616894071211373475)
                    ·
                      rfl

theorem cell23_6956439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_6956439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956439 prefixEnd_6956439 := by exact prefixLift 6956439
  have htrace : WordTrace (prefixWord ++ tailWord_6956439) baseStart_6956439 baseEnd_6956439 := by
    simpa [prefixWord, tailWord_6956439, baseEnd_6956439] using wordTrace_append hprefix tailTrace_6956439
  have hstable : (prefixWord ++ tailWord_6956439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956439).length < 2 ^ (prefixWord ++ tailWord_6956439).sum := by decide
  have hdescent : baseEnd_6956439 < baseStart_6956439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956444 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6956444 : Nat := 118140960795 + 6956444 * 2 ^ 59
def prefixEnd_6956444 : Nat := 4983230072969 + 3 ^ 40 * 6956444 * 2
def baseEnd_6956444 : Nat := 3571999418085486114557903

theorem tailTrace_6956444 : CollatzResearch.WordTrace tailWord_6956444 prefixEnd_6956444 3571999418085486114557903 := by
  unfold tailWord_6956444
  simp only [CollatzResearch.WordTrace]
  refine ⟨126861178404999464446770193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169148237873332619262360257 126861178404999464446770193)
  ·
    refine ⟨95145883803749598335077645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126861178404999464446770193 95145883803749598335077645)
    ·
      refine ⟨35679706426406099375654117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95145883803749598335077645 35679706426406099375654117)
      ·
        refine ⟨6689944954951143632935147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35679706426406099375654117 6689944954951143632935147)
        ·
          refine ⟨10034917432426715449402721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6689944954951143632935147 10034917432426715449402721)
          ·
            refine ⟨7526188074320036587052041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10034917432426715449402721 7526188074320036587052041)
            ·
              refine ⟨5644641055740027440289031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526188074320036587052041 5644641055740027440289031)
              ·
                refine ⟨8466961583610041160433547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644641055740027440289031 8466961583610041160433547)
                ·
                  refine ⟨12700442375415061740650321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8466961583610041160433547 12700442375415061740650321)
                  ·
                    refine ⟨9525331781561296305487741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12700442375415061740650321 9525331781561296305487741)
                    ·
                      refine ⟨3571999418085486114557903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9525331781561296305487741 3571999418085486114557903)
                      ·
                        rfl

theorem cell23_6956444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6956444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956444 prefixEnd_6956444 := by exact prefixLift 6956444
  have htrace : WordTrace (prefixWord ++ tailWord_6956444) baseStart_6956444 baseEnd_6956444 := by
    simpa [prefixWord, tailWord_6956444, baseEnd_6956444] using wordTrace_append hprefix tailTrace_6956444
  have hstable : (prefixWord ++ tailWord_6956444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956444).length < 2 ^ (prefixWord ++ tailWord_6956444).sum := by decide
  have hdescent : baseEnd_6956444 < baseStart_6956444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956466 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_6956466 : Nat := 118140960795 + 6956466 * 2 ^ 59
def prefixEnd_6956466 : Nat := 4983230072969 + 3 ^ 40 * 6956466 * 2
def baseEnd_6956466 : Nat := 3572010714659885028482801

theorem tailTrace_6956466 : CollatzResearch.WordTrace tailWord_6956466 prefixEnd_6956466 3572010714659885028482801 := by
  unfold tailWord_6956466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63430789803979806662710313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169148772810612817767227501 63430789803979806662710313)
  ·
    refine ⟨47573092352984854997032735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63430789803979806662710313 47573092352984854997032735)
    ·
      refine ⟨71359638529477282495549103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47573092352984854997032735 71359638529477282495549103)
      ·
        refine ⟨107039457794215923743323655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71359638529477282495549103 107039457794215923743323655)
        ·
          refine ⟨160559186691323885614985483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107039457794215923743323655 160559186691323885614985483)
          ·
            refine ⟨240838780036985828422478225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160559186691323885614985483 240838780036985828422478225)
            ·
              refine ⟨180629085027739371316858669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240838780036985828422478225 180629085027739371316858669)
              ·
                refine ⟨67735906885402264243822001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180629085027739371316858669 67735906885402264243822001)
                ·
                  refine ⟨50801930164051698182866501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67735906885402264243822001 50801930164051698182866501)
                  ·
                    refine ⟨9525361905759693409287469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50801930164051698182866501 9525361905759693409287469)
                    ·
                      refine ⟨3572010714659885028482801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9525361905759693409287469 3572010714659885028482801)
                      ·
                        rfl

theorem cell23_6956466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_6956466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956466 prefixEnd_6956466 := by exact prefixLift 6956466
  have htrace : WordTrace (prefixWord ++ tailWord_6956466) baseStart_6956466 baseEnd_6956466 := by
    simpa [prefixWord, tailWord_6956466, baseEnd_6956466] using wordTrace_append hprefix tailTrace_6956466
  have hstable : (prefixWord ++ tailWord_6956466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956466).length < 2 ^ (prefixWord ++ tailWord_6956466).sum := by decide
  have hdescent : baseEnd_6956466 < baseStart_6956466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956479 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_6956479 : Nat := 118140960795 + 6956479 * 2 ^ 59
def prefixEnd_6956479 : Nat := 4983230072969 + 3 ^ 40 * 6956479 * 2
def baseEnd_6956479 : Nat := 3572017389908393477620241

theorem tailTrace_6956479 : CollatzResearch.WordTrace tailWord_6956479 prefixEnd_6956479 3572017389908393477620241 := by
  unfold tailWord_6956479
  simp only [CollatzResearch.WordTrace]
  refine ⟨253723633364872129871064491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169149088909914753247376327 253723633364872129871064491)
  ·
    refine ⟨380585450047308194806596737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253723633364872129871064491 380585450047308194806596737)
    ·
      refine ⟨285439087535481146104947553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380585450047308194806596737 285439087535481146104947553)
      ·
        refine ⟨214079315651610859578710665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285439087535481146104947553 214079315651610859578710665)
        ·
          refine ⟨160559486738708144684032999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214079315651610859578710665 160559486738708144684032999)
          ·
            refine ⟨240839230108062217026049499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160559486738708144684032999 240839230108062217026049499)
            ·
              refine ⟨361258845162093325539074249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240839230108062217026049499 361258845162093325539074249)
              ·
                refine ⟨270944133871569994154305687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361258845162093325539074249 270944133871569994154305687)
                ·
                  refine ⟨406416200807354991231458531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270944133871569994154305687 406416200807354991231458531)
                  ·
                    refine ⟨609624301211032486847187797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 406416200807354991231458531 609624301211032486847187797)
                    ·
                      refine ⟨3572017389908393477620241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 609624301211032486847187797 3572017389908393477620241)
                      ·
                        rfl

theorem cell23_6956479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_6956479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956479 prefixEnd_6956479 := by exact prefixLift 6956479
  have htrace : WordTrace (prefixWord ++ tailWord_6956479) baseStart_6956479 baseEnd_6956479 := by
    simpa [prefixWord, tailWord_6956479, baseEnd_6956479] using wordTrace_append hprefix tailTrace_6956479
  have hstable : (prefixWord ++ tailWord_6956479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956479).length < 2 ^ (prefixWord ++ tailWord_6956479).sum := by decide
  have hdescent : baseEnd_6956479 < baseStart_6956479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956480 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 2, 2, 2]
def baseStart_6956480 : Nat := 118140960795 + 6956480 * 2 ^ 59
def prefixEnd_6956480 : Nat := 4983230072969 + 3 ^ 40 * 6956480 * 2
def baseEnd_6956480 : Nat := 3572017903389047973707737

theorem tailTrace_6956480 : CollatzResearch.WordTrace tailWord_6956480 prefixEnd_6956480 3572017903389047973707737 := by
  unfold tailWord_6956480
  simp only [CollatzResearch.WordTrace]
  refine ⟨126861834918934253520925447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169149113225245671361233929 126861834918934253520925447)
  ·
    refine ⟨190292752378401380281388171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126861834918934253520925447 190292752378401380281388171)
    ·
      refine ⟨285439128567602070422082257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190292752378401380281388171 285439128567602070422082257)
      ·
        refine ⟨214079346425701552816561693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285439128567602070422082257 214079346425701552816561693)
        ·
          refine ⟨80279754909638082306210635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214079346425701552816561693 80279754909638082306210635)
          ·
            refine ⟨120419632364457123459315953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80279754909638082306210635 120419632364457123459315953)
            ·
              refine ⟨90314724273342842594486965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120419632364457123459315953 90314724273342842594486965)
              ·
                refine ⟨8467005400625891493233153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90314724273342842594486965 8467005400625891493233153)
                ·
                  refine ⟨6350254050469418619924865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467005400625891493233153 6350254050469418619924865)
                  ·
                    refine ⟨4762690537852063964943649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6350254050469418619924865 4762690537852063964943649)
                    ·
                      refine ⟨3572017903389047973707737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762690537852063964943649 3572017903389047973707737)
                      ·
                        rfl

theorem cell23_6956480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_6956480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956480 prefixEnd_6956480 := by exact prefixLift 6956480
  have htrace : WordTrace (prefixWord ++ tailWord_6956480) baseStart_6956480 baseEnd_6956480 := by
    simpa [prefixWord, tailWord_6956480, baseEnd_6956480] using wordTrace_append hprefix tailTrace_6956480
  have hstable : (prefixWord ++ tailWord_6956480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956480).length < 2 ^ (prefixWord ++ tailWord_6956480).sum := by decide
  have hdescent : baseEnd_6956480 < baseStart_6956480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956520 : List Nat := [2, 1, 4, 1, 1, 2, 5, 2, 5]
def baseStart_6956520 : Nat := 118140960795 + 6956520 * 2 ^ 59
def prefixEnd_6956520 : Nat := 4983230072969 + 3 ^ 40 * 6956520 * 2
def baseEnd_6956520 : Nat := 396893160290580868578617

theorem tailTrace_6956520 : CollatzResearch.WordTrace tailWord_6956520 prefixEnd_6956520 396893160290580868578617 := by
  unfold tailWord_6956520
  simp only [CollatzResearch.WordTrace]
  refine ⟨126862564378861796936653507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169150085838482395915538009 126862564378861796936653507)
  ·
    refine ⟨190293846568292695404980261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126862564378861796936653507 190293846568292695404980261)
    ·
      refine ⟨35680096231554880388433799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190293846568292695404980261 35680096231554880388433799)
      ·
        refine ⟨53520144347332320582650699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35680096231554880388433799 53520144347332320582650699)
        ·
          refine ⟨80280216520998480873976049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53520144347332320582650699 80280216520998480873976049)
          ·
            refine ⟨60210162390748860655482037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80280216520998480873976049 60210162390748860655482037)
            ·
              refine ⟨5644702724132705686451441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60210162390748860655482037 5644702724132705686451441)
              ·
                refine ⟨4233527043099529264838581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644702724132705686451441 4233527043099529264838581)
                ·
                  refine ⟨396893160290580868578617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4233527043099529264838581 396893160290580868578617)
                  ·
                    rfl

theorem cell23_6956520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 5].length) (baseStart_6956520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956520 prefixEnd_6956520 := by exact prefixLift 6956520
  have htrace : WordTrace (prefixWord ++ tailWord_6956520) baseStart_6956520 baseEnd_6956520 := by
    simpa [prefixWord, tailWord_6956520, baseEnd_6956520] using wordTrace_append hprefix tailTrace_6956520
  have hstable : (prefixWord ++ tailWord_6956520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956520).length < 2 ^ (prefixWord ++ tailWord_6956520).sum := by decide
  have hdescent : baseEnd_6956520 < baseStart_6956520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956553 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_6956553 : Nat := 118140960795 + 6956553 * 2 ^ 59
def prefixEnd_6956553 : Nat := 4983230072969 + 3 ^ 40 * 6956553 * 2
def baseEnd_6956553 : Nat := 3572055387476826188094901

theorem tailTrace_6956553 : CollatzResearch.WordTrace tailWord_6956553 prefixEnd_6956553 3572055387476826188094901 := by
  unfold tailWord_6956553
  simp only [CollatzResearch.WordTrace]
  refine ⟨253726332366604040509258313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169150888244402693672838875 253726332366604040509258313)
  ·
    refine ⟨190294749274953030381943735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253726332366604040509258313 190294749274953030381943735)
    ·
      refine ⟨285442123912429545572915603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190294749274953030381943735 285442123912429545572915603)
      ·
        refine ⟨428163185868644318359373405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285442123912429545572915603 428163185868644318359373405)
        ·
          refine ⟨160561194700741619384765027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428163185868644318359373405 160561194700741619384765027)
          ·
            refine ⟨240841792051112429077147541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160561194700741619384765027 240841792051112429077147541)
            ·
              refine ⟨11289459002395895112991291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240841792051112429077147541 11289459002395895112991291)
              ·
                refine ⟨16934188503593842669486937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11289459002395895112991291 16934188503593842669486937)
                ·
                  refine ⟨12700641377695382002115203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16934188503593842669486937 12700641377695382002115203)
                  ·
                    refine ⟨19050962066543073003172805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12700641377695382002115203 19050962066543073003172805)
                    ·
                      refine ⟨3572055387476826188094901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19050962066543073003172805 3572055387476826188094901)
                      ·
                        rfl

theorem cell23_6956553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_6956553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956553 prefixEnd_6956553 := by exact prefixLift 6956553
  have htrace : WordTrace (prefixWord ++ tailWord_6956553) baseStart_6956553 baseEnd_6956553 := by
    simpa [prefixWord, tailWord_6956553, baseEnd_6956553] using wordTrace_append hprefix tailTrace_6956553
  have hstable : (prefixWord ++ tailWord_6956553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956553).length < 2 ^ (prefixWord ++ tailWord_6956553).sum := by decide
  have hdescent : baseEnd_6956553 < baseStart_6956553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956616 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_6956616 : Nat := 118140960795 + 6956616 * 2 ^ 59
def prefixEnd_6956616 : Nat := 4983230072969 + 3 ^ 40 * 6956616 * 2
def baseEnd_6956616 : Nat := 3572087736758059441607111

theorem tailTrace_6956616 : CollatzResearch.WordTrace tailWord_6956616 prefixEnd_6956616 3572087736758059441607111 := by
  unfold tailWord_6956616
  simp only [CollatzResearch.WordTrace]
  refine ⟨126864315082687901134400851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169152420110250534845867801 126864315082687901134400851)
  ·
    refine ⟨190296472624031851701601277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126864315082687901134400851 190296472624031851701601277)
    ·
      refine ⟨71361177234011944388100479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190296472624031851701601277 71361177234011944388100479)
      ·
        refine ⟨107041765851017916582150719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71361177234011944388100479 107041765851017916582150719)
        ·
          refine ⟨160562648776526874873226079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107041765851017916582150719 160562648776526874873226079)
          ·
            refine ⟨240843973164790312309839119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160562648776526874873226079 240843973164790312309839119)
            ·
              refine ⟨361265959747185468464758679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240843973164790312309839119 361265959747185468464758679)
              ·
                refine ⟨541898939620778202697138019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361265959747185468464758679 541898939620778202697138019)
                ·
                  refine ⟨812848409431167304045707029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541898939620778202697138019 812848409431167304045707029)
                  ·
                    refine ⟨38102269192085967377142517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 812848409431167304045707029 38102269192085967377142517)
                    ·
                      refine ⟨3572087736758059441607111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38102269192085967377142517 3572087736758059441607111)
                      ·
                        rfl

theorem cell23_6956616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_6956616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956616 prefixEnd_6956616 := by exact prefixLift 6956616
  have htrace : WordTrace (prefixWord ++ tailWord_6956616) baseStart_6956616 baseEnd_6956616 := by
    simpa [prefixWord, tailWord_6956616, baseEnd_6956616] using wordTrace_append hprefix tailTrace_6956616
  have hstable : (prefixWord ++ tailWord_6956616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956616).length < 2 ^ (prefixWord ++ tailWord_6956616).sum := by decide
  have hdescent : baseEnd_6956616 < baseStart_6956616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956700 : List Nat := [2, 2, 3, 2, 3, 1, 2, 8]
def baseStart_6956700 : Nat := 118140960795 + 6956700 * 2 ^ 59
def prefixEnd_6956700 : Nat := 4983230072969 + 3 ^ 40 * 6956700 * 2
def baseEnd_6956700 : Nat := 132301143301223596776175

theorem tailTrace_6956700 : CollatzResearch.WordTrace tailWord_6956700 prefixEnd_6956700 132301143301223596776175 := by
  unfold tailWord_6956700
  simp only [CollatzResearch.WordTrace]
  refine ⟨126865846948535742307429777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169154462598047656409906369 126865846948535742307429777)
  ·
    refine ⟨95149385211401806730572333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126865846948535742307429777 95149385211401806730572333)
    ·
      refine ⟨35681019454275677523964625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95149385211401806730572333 35681019454275677523964625)
      ·
        refine ⟨26760764590706758142973469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35681019454275677523964625 26760764590706758142973469)
        ·
          refine ⟨10035286721515034303615051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26760764590706758142973469 10035286721515034303615051)
          ·
            refine ⟨15052930082272551455422577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10035286721515034303615051 15052930082272551455422577)
            ·
              refine ⟨11289697561704413591566933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15052930082272551455422577 11289697561704413591566933)
              ·
                refine ⟨132301143301223596776175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11289697561704413591566933 132301143301223596776175)
                ·
                  rfl

theorem cell23_6956700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 8].length) (baseStart_6956700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956700 prefixEnd_6956700 := by exact prefixLift 6956700
  have htrace : WordTrace (prefixWord ++ tailWord_6956700) baseStart_6956700 baseEnd_6956700 := by
    simpa [prefixWord, tailWord_6956700, baseEnd_6956700] using wordTrace_append hprefix tailTrace_6956700
  have hstable : (prefixWord ++ tailWord_6956700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956700).length < 2 ^ (prefixWord ++ tailWord_6956700).sum := by decide
  have hdescent : baseEnd_6956700 < baseStart_6956700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956704 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 2, 4]
def baseStart_6956704 : Nat := 118140960795 + 6956704 * 2 ^ 59
def prefixEnd_6956704 : Nat := 4983230072969 + 3 ^ 40 * 6956704 * 2
def baseEnd_6956704 : Nat := 1190710974351885032435569

theorem tailTrace_6956704 : CollatzResearch.WordTrace tailWord_6956704 prefixEnd_6956704 1190710974351885032435569 := by
  unfold tailWord_6956704
  simp only [CollatzResearch.WordTrace]
  refine ⟨126865919894528496649002583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169154559859371328865336777 126865919894528496649002583)
  ·
    refine ⟨190298879841792744973503875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126865919894528496649002583 190298879841792744973503875)
    ·
      refine ⟨285448319762689117460255813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190298879841792744973503875 285448319762689117460255813)
      ·
        refine ⟨53521559955504209523797965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285448319762689117460255813 53521559955504209523797965)
        ·
          refine ⟨20070584983314078571424237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53521559955504209523797965 20070584983314078571424237)
          ·
            refine ⟨7526469368742779464284089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20070584983314078571424237 7526469368742779464284089)
            ·
              refine ⟨5644852026557084598213067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526469368742779464284089 5644852026557084598213067)
              ·
                refine ⟨8467278039835626897319601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5644852026557084598213067 8467278039835626897319601)
                ·
                  refine ⟨6350458529876720172989701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467278039835626897319601 6350458529876720172989701)
                  ·
                    refine ⟨1190710974351885032435569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6350458529876720172989701 1190710974351885032435569)
                    ·
                      rfl

theorem cell23_6956704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 2, 4].length) (baseStart_6956704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956704 prefixEnd_6956704 := by exact prefixLift 6956704
  have htrace : WordTrace (prefixWord ++ tailWord_6956704) baseStart_6956704 baseEnd_6956704 := by
    simpa [prefixWord, tailWord_6956704, baseEnd_6956704] using wordTrace_append hprefix tailTrace_6956704
  have hstable : (prefixWord ++ tailWord_6956704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956704).length < 2 ^ (prefixWord ++ tailWord_6956704).sum := by decide
  have hdescent : baseEnd_6956704 < baseStart_6956704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956738 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6956738 : Nat := 118140960795 + 6956738 * 2 ^ 59
def prefixEnd_6956738 : Nat := 4983230072969 + 3 ^ 40 * 6956738 * 2
def baseEnd_6956738 : Nat := 1190716793799302654760517

theorem tailTrace_6956738 : CollatzResearch.WordTrace tailWord_6956738 prefixEnd_6956738 1190716793799302654760517 := by
  unfold tailWord_6956738
  simp only [CollatzResearch.WordTrace]
  refine ⟨63433269967733454276185717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169155386580622544736495245 63433269967733454276185717)
  ·
    refine ⟨5946869059475011338392411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63433269967733454276185717 5946869059475011338392411)
    ·
      refine ⟨8920303589212517007588617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946869059475011338392411 8920303589212517007588617)
      ·
        refine ⟨6690227691909387755691463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8920303589212517007588617 6690227691909387755691463)
        ·
          refine ⟨10035341537864081633537195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6690227691909387755691463 10035341537864081633537195)
          ·
            refine ⟨15053012306796122450305793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10035341537864081633537195 15053012306796122450305793)
            ·
              refine ⟨11289759230097091837729345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15053012306796122450305793 11289759230097091837729345)
              ·
                refine ⟨8467319422572818878297009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11289759230097091837729345 8467319422572818878297009)
                ·
                  refine ⟨6350489566929614158722757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8467319422572818878297009 6350489566929614158722757)
                  ·
                    refine ⟨1190716793799302654760517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6350489566929614158722757 1190716793799302654760517)
                    ·
                      rfl

theorem cell23_6956738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6956738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956738 prefixEnd_6956738 := by exact prefixLift 6956738
  have htrace : WordTrace (prefixWord ++ tailWord_6956738) baseStart_6956738 baseEnd_6956738 := by
    simpa [prefixWord, tailWord_6956738, baseEnd_6956738] using wordTrace_append hprefix tailTrace_6956738
  have hstable : (prefixWord ++ tailWord_6956738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956738).length < 2 ^ (prefixWord ++ tailWord_6956738).sum := by decide
  have hdescent : baseEnd_6956738 < baseStart_6956738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956743 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 2, 6]
def baseStart_6956743 : Nat := 118140960795 + 6956743 * 2 ^ 59
def prefixEnd_6956743 : Nat := 4983230072969 + 3 ^ 40 * 6956743 * 2
def baseEnd_6956743 : Nat := 1190717649600393481573009

theorem tailTrace_6956743 : CollatzResearch.WordTrace tailWord_6956743 prefixEnd_6956743 1190717649600393481573009 := by
  unfold tailWord_6956743
  simp only [CollatzResearch.WordTrace]
  refine ⟨253733262235915702958674883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169155508157277135305783255 253733262235915702958674883)
  ·
    refine ⟨380599893353873554438012325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253733262235915702958674883 380599893353873554438012325)
    ·
      refine ⟨71362480003851291457127311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380599893353873554438012325 71362480003851291457127311)
      ·
        refine ⟨107043720005776937185690967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71362480003851291457127311 107043720005776937185690967)
        ·
          refine ⟨160565580008665405778536451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107043720005776937185690967 160565580008665405778536451)
          ·
            refine ⟨240848370012998108667804677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160565580008665405778536451 240848370012998108667804677)
            ·
              refine ⟨45159069377437145375213377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240848370012998108667804677 45159069377437145375213377)
              ·
                refine ⟨33869302033077859031410033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45159069377437145375213377 33869302033077859031410033)
                ·
                  refine ⟨25401976524808394273557525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33869302033077859031410033 25401976524808394273557525)
                  ·
                    refine ⟨1190717649600393481573009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25401976524808394273557525 1190717649600393481573009)
                    ·
                      rfl

theorem cell23_6956743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_6956743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956743 prefixEnd_6956743 := by exact prefixLift 6956743
  have htrace : WordTrace (prefixWord ++ tailWord_6956743) baseStart_6956743 baseEnd_6956743 := by
    simpa [prefixWord, tailWord_6956743, baseEnd_6956743] using wordTrace_append hprefix tailTrace_6956743
  have hstable : (prefixWord ++ tailWord_6956743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956743).length < 2 ^ (prefixWord ++ tailWord_6956743).sum := by decide
  have hdescent : baseEnd_6956743 < baseStart_6956743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956767 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 1, 4, 2]
def baseStart_6956767 : Nat := 118140960795 + 6956767 * 2 ^ 59
def prefixEnd_6956767 : Nat := 4983230072969 + 3 ^ 40 * 6956767 * 2
def baseEnd_6956767 : Nat := 3572165272336888350818917

theorem tailTrace_6956767 : CollatzResearch.WordTrace tailWord_6956767 prefixEnd_6956767 3572165272336888350818917 := by
  unfold tailWord_6956767
  simp only [CollatzResearch.WordTrace]
  refine ⟨253734137587828755057548555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169156091725219170038365703 253734137587828755057548555)
  ·
    refine ⟨380601206381743132586322833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253734137587828755057548555 380601206381743132586322833)
    ·
      refine ⟨285450904786307349439742125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380601206381743132586322833 285450904786307349439742125)
      ·
        refine ⟨107044089294865256039903297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285450904786307349439742125 107044089294865256039903297)
        ·
          refine ⟨80283066971148942029927473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107044089294865256039903297 80283066971148942029927473)
          ·
            refine ⟨60212300228361706522445605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80283066971148942029927473 60212300228361706522445605)
            ·
              refine ⟨11289806292817819972958551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60212300228361706522445605 11289806292817819972958551)
              ·
                refine ⟨16934709439226729959437827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11289806292817819972958551 16934709439226729959437827)
                ·
                  refine ⟨25402064158840094939156741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16934709439226729959437827 25402064158840094939156741)
                  ·
                    refine ⟨4762887029782517801091889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25402064158840094939156741 4762887029782517801091889)
                    ·
                      refine ⟨3572165272336888350818917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762887029782517801091889 3572165272336888350818917)
                      ·
                        rfl

theorem cell23_6956767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_6956767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956767 prefixEnd_6956767 := by exact prefixLift 6956767
  have htrace : WordTrace (prefixWord ++ tailWord_6956767) baseStart_6956767 baseEnd_6956767 := by
    simpa [prefixWord, tailWord_6956767, baseEnd_6956767] using wordTrace_append hprefix tailTrace_6956767
  have hstable : (prefixWord ++ tailWord_6956767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956767).length < 2 ^ (prefixWord ++ tailWord_6956767).sum := by decide
  have hdescent : baseEnd_6956767 < baseStart_6956767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956788 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6956788 : Nat := 118140960795 + 6956788 * 2 ^ 59
def prefixEnd_6956788 : Nat := 4983230072969 + 3 ^ 40 * 6956788 * 2
def baseEnd_6956788 : Nat := 3572176055430632768656321

theorem tailTrace_6956788 : CollatzResearch.WordTrace tailWord_6956788 prefixEnd_6956788 3572176055430632768656321 := by
  unfold tailWord_6956788
  simp only [CollatzResearch.WordTrace]
  refine ⟨126867451760376337822031509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169156602347168450429375345 126867451760376337822031509)
  ·
    refine ⟨5946911801267640835407727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126867451760376337822031509 5946911801267640835407727)
    ·
      refine ⟨8920367701901461253111591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946911801267640835407727 8920367701901461253111591)
      ·
        refine ⟨13380551552852191879667387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8920367701901461253111591 13380551552852191879667387)
        ·
          refine ⟨20070827329278287819501081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13380551552852191879667387 20070827329278287819501081)
          ·
            refine ⟨15053120496958715864625811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20070827329278287819501081 15053120496958715864625811)
            ·
              refine ⟨22579680745438073796938717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15053120496958715864625811 22579680745438073796938717)
              ·
                refine ⟨8467380279539277673852019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22579680745438073796938717 8467380279539277673852019)
                ·
                  refine ⟨12701070419308916510778029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8467380279539277673852019 12701070419308916510778029)
                  ·
                    refine ⟨4762901407240843691541761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12701070419308916510778029 4762901407240843691541761)
                    ·
                      refine ⟨3572176055430632768656321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4762901407240843691541761 3572176055430632768656321)
                      ·
                        rfl

theorem cell23_6956788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6956788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956788 prefixEnd_6956788 := by exact prefixLift 6956788
  have htrace : WordTrace (prefixWord ++ tailWord_6956788) baseStart_6956788 baseEnd_6956788 := by
    simpa [prefixWord, tailWord_6956788, baseEnd_6956788] using wordTrace_append hprefix tailTrace_6956788
  have hstable : (prefixWord ++ tailWord_6956788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956788).length < 2 ^ (prefixWord ++ tailWord_6956788).sum := by decide
  have hdescent : baseEnd_6956788 < baseStart_6956788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956807 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 7]
def baseStart_6956807 : Nat := 118140960795 + 6956807 * 2 ^ 59
def prefixEnd_6956807 : Nat := 4983230072969 + 3 ^ 40 * 6956807 * 2
def baseEnd_6956807 : Nat := 396909534618118688257637

theorem tailTrace_6956807 : CollatzResearch.WordTrace tailWord_6956807 prefixEnd_6956807 396909534618118688257637 := by
  unfold tailWord_6956807
  simp only [CollatzResearch.WordTrace]
  refine ⟨253735596507683841889004675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169157064338455894592669783 253735596507683841889004675)
  ·
    refine ⟨380603394761525762833507013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253735596507683841889004675 380603394761525762833507013)
    ·
      refine ⟨71363136517786080531282565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380603394761525762833507013 71363136517786080531282565)
      ·
        refine ⟨13380588097084890099615481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71363136517786080531282565 13380588097084890099615481)
        ·
          refine ⟨10035441072813667574711611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13380588097084890099615481 10035441072813667574711611)
          ·
            refine ⟨15053161609220501362067417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10035441072813667574711611 15053161609220501362067417)
            ·
              refine ⟨11289871206915376021550563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15053161609220501362067417 11289871206915376021550563)
              ·
                refine ⟨16934806810373064032325845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11289871206915376021550563 16934806810373064032325845)
                ·
                  refine ⟨396909534618118688257637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16934806810373064032325845 396909534618118688257637)
                  ·
                    rfl

theorem cell23_6956807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 7].length) (baseStart_6956807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956807 prefixEnd_6956807 := by exact prefixLift 6956807
  have htrace : WordTrace (prefixWord ++ tailWord_6956807) baseStart_6956807 baseEnd_6956807 := by
    simpa [prefixWord, tailWord_6956807, baseEnd_6956807] using wordTrace_append hprefix tailTrace_6956807
  have hstable : (prefixWord ++ tailWord_6956807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956807).length < 2 ^ (prefixWord ++ tailWord_6956807).sum := by decide
  have hdescent : baseEnd_6956807 < baseStart_6956807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956854 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_6956854 : Nat := 118140960795 + 6956854 * 2 ^ 59
def prefixEnd_6956854 : Nat := 4983230072969 + 3 ^ 40 * 6956854 * 2
def baseEnd_6956854 : Nat := 1190736648384609836810339

theorem tailTrace_6956854 : CollatzResearch.WordTrace tailWord_6956854 prefixEnd_6956854 1190736648384609836810339 := by
  unfold tailWord_6956854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858581921157098057247851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169158207159009045943977077 15858581921157098057247851)
  ·
    refine ⟨23787872881735647085871777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15858581921157098057247851 23787872881735647085871777)
    ·
      refine ⟨17840904661301735314403833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23787872881735647085871777 17840904661301735314403833)
      ·
        refine ⟨13380678495976301485802875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17840904661301735314403833 13380678495976301485802875)
        ·
          refine ⟨20071017743964452228704313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13380678495976301485802875 20071017743964452228704313)
          ·
            refine ⟨15053263307973339171528235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20071017743964452228704313 15053263307973339171528235)
            ·
              refine ⟨22579894961960008757292353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15053263307973339171528235 22579894961960008757292353)
              ·
                refine ⟨16934921221470006567969265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22579894961960008757292353 16934921221470006567969265)
                ·
                  refine ⟨12701190916102504925976949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16934921221470006567969265 12701190916102504925976949)
                  ·
                    refine ⟨1190736648384609836810339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12701190916102504925976949 1190736648384609836810339)
                    ·
                      rfl

theorem cell23_6956854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_6956854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956854 prefixEnd_6956854 := by exact prefixLift 6956854
  have htrace : WordTrace (prefixWord ++ tailWord_6956854) baseStart_6956854 baseEnd_6956854 := by
    simpa [prefixWord, tailWord_6956854, baseEnd_6956854] using wordTrace_append hprefix tailTrace_6956854
  have hstable : (prefixWord ++ tailWord_6956854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956854).length < 2 ^ (prefixWord ++ tailWord_6956854).sum := by decide
  have hdescent : baseEnd_6956854 < baseStart_6956854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956867 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 3, 4]
def baseStart_6956867 : Nat := 118140960795 + 6956867 * 2 ^ 59
def prefixEnd_6956867 : Nat := 4983230072969 + 3 ^ 40 * 6956867 * 2
def baseEnd_6956867 : Nat := 1190738873467445986522819

theorem tailTrace_6956867 : CollatzResearch.WordTrace tailWord_6956867 prefixEnd_6956867 1190738873467445986522819 := by
  unfold tailWord_6956867
  simp only [CollatzResearch.WordTrace]
  refine ⟨253737784887466472136188855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169158523258310981424125903 253737784887466472136188855)
  ·
    refine ⟨380606677331199708204283283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253737784887466472136188855 380606677331199708204283283)
    ·
      refine ⟨570910015996799562306424925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380606677331199708204283283 570910015996799562306424925)
      ·
        refine ⟨214091255998799835864909347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 570910015996799562306424925 214091255998799835864909347)
        ·
          refine ⟨321136883998199753797364021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214091255998799835864909347 321136883998199753797364021)
          ·
            refine ⟨30106582874831226918502877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321136883998199753797364021 30106582874831226918502877)
            ·
              refine ⟨11289968578061710094438579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30106582874831226918502877 11289968578061710094438579)
              ·
                refine ⟨16934952867092565141657869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11289968578061710094438579 16934952867092565141657869)
                ·
                  refine ⟨6350607325159711928121701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16934952867092565141657869 6350607325159711928121701)
                  ·
                    refine ⟨1190738873467445986522819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6350607325159711928121701 1190738873467445986522819)
                    ·
                      rfl

theorem cell23_6956867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 4].length) (baseStart_6956867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956867 prefixEnd_6956867 := by exact prefixLift 6956867
  have htrace : WordTrace (prefixWord ++ tailWord_6956867) baseStart_6956867 baseEnd_6956867 := by
    simpa [prefixWord, tailWord_6956867, baseEnd_6956867] using wordTrace_append hprefix tailTrace_6956867
  have hstable : (prefixWord ++ tailWord_6956867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956867).length < 2 ^ (prefixWord ++ tailWord_6956867).sum := by decide
  have hdescent : baseEnd_6956867 < baseStart_6956867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956918 : List Nat := [5, 1, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6956918 : Nat := 118140960795 + 6956918 * 2 ^ 59
def prefixEnd_6956918 : Nat := 4983230072969 + 3 ^ 40 * 6956918 * 2
def baseEnd_6956918 : Nat := 1190747602638572420010241

theorem tailTrace_6956918 : CollatzResearch.WordTrace tailWord_6956918 prefixEnd_6956918 1190747602638572420010241 := by
  unfold tailWord_6956918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858727813142606740393463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169159763340187805230863605 15858727813142606740393463)
  ·
    refine ⟨23788091719713910110590195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15858727813142606740393463 23788091719713910110590195)
    ·
      refine ⟨35682137579570865165885293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23788091719713910110590195 35682137579570865165885293)
      ·
        refine ⟨13380801592339074437206985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35682137579570865165885293 13380801592339074437206985)
        ·
          refine ⟨10035601194254305827905239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13380801592339074437206985 10035601194254305827905239)
          ·
            refine ⟨15053401791381458741857859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10035601194254305827905239 15053401791381458741857859)
            ·
              refine ⟨22580102687072188112786789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15053401791381458741857859 22580102687072188112786789)
              ·
                refine ⟨4233769253826035271147523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22580102687072188112786789 4233769253826035271147523)
                ·
                  refine ⟨6350653880739052906721285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233769253826035271147523 6350653880739052906721285)
                  ·
                    refine ⟨1190747602638572420010241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6350653880739052906721285 1190747602638572420010241)
                    ·
                      rfl

theorem cell23_6956918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6956918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956918 prefixEnd_6956918 := by exact prefixLift 6956918
  have htrace : WordTrace (prefixWord ++ tailWord_6956918) baseStart_6956918 baseEnd_6956918 := by
    simpa [prefixWord, tailWord_6956918, baseEnd_6956918] using wordTrace_append hprefix tailTrace_6956918
  have hstable : (prefixWord ++ tailWord_6956918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956918).length < 2 ^ (prefixWord ++ tailWord_6956918).sum := by decide
  have hdescent : baseEnd_6956918 < baseStart_6956918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956951 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 2, 3, 2]
def baseStart_6956951 : Nat := 118140960795 + 6956951 * 2 ^ 59
def prefixEnd_6956951 : Nat := 4983230072969 + 3 ^ 40 * 6956951 * 2
def baseEnd_6956951 : Nat := 3572259752777315630918071

theorem tailTrace_6956951 : CollatzResearch.WordTrace tailWord_6956951 prefixEnd_6956951 3572259752777315630918071 := by
  unfold tailWord_6956951
  simp only [CollatzResearch.WordTrace]
  refine ⟨253740848619162154482246707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169160565746108102988164471 253740848619162154482246707)
  ·
    refine ⟨380611272928743231723370061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253740848619162154482246707 380611272928743231723370061)
    ·
      refine ⟨142729227348278711896263773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380611272928743231723370061 142729227348278711896263773)
      ·
        refine ⟨53523460255604516961098915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142729227348278711896263773 53523460255604516961098915)
        ·
          refine ⟨80285190383406775441648373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53523460255604516961098915 80285190383406775441648373)
          ·
            refine ⟨7526736598444385197654535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80285190383406775441648373 7526736598444385197654535)
            ·
              refine ⟨11290104897666577796481803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7526736598444385197654535 11290104897666577796481803)
              ·
                refine ⟨16935157346499866694722705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11290104897666577796481803 16935157346499866694722705)
                ·
                  refine ⟨12701368009874900021042029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16935157346499866694722705 12701368009874900021042029)
                  ·
                    refine ⟨4763013003703087507890761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12701368009874900021042029 4763013003703087507890761)
                    ·
                      refine ⟨3572259752777315630918071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763013003703087507890761 3572259752777315630918071)
                      ·
                        rfl

theorem cell23_6956951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_6956951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956951 prefixEnd_6956951 := by exact prefixLift 6956951
  have htrace : WordTrace (prefixWord ++ tailWord_6956951) baseStart_6956951 baseEnd_6956951 := by
    simpa [prefixWord, tailWord_6956951, baseEnd_6956951] using wordTrace_append hprefix tailTrace_6956951
  have hstable : (prefixWord ++ tailWord_6956951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956951).length < 2 ^ (prefixWord ++ tailWord_6956951).sum := by decide
  have hdescent : baseEnd_6956951 < baseStart_6956951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956957 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6956957 : Nat := 118140960795 + 6956957 * 2 ^ 59
def prefixEnd_6956957 : Nat := 4983230072969 + 3 ^ 40 * 6956957 * 2
def baseEnd_6956957 : Nat := 1190754277887080869147681

theorem tailTrace_6956957 : CollatzResearch.WordTrace tailWord_6956957 prefixEnd_6956957 1190754277887080869147681 := by
  unfold tailWord_6956957
  simp only [CollatzResearch.WordTrace]
  refine ⟨253741067457140417506965125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169160711638093611671310083 253741067457140417506965125)
  ·
    refine ⟨47576450148213828282555961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253741067457140417506965125 47576450148213828282555961)
    ·
      refine ⟨35682337611160371211916971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47576450148213828282555961 35682337611160371211916971)
      ·
        refine ⟨53523506416740556817875457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35682337611160371211916971 53523506416740556817875457)
        ·
          refine ⟨40142629812555417613406593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53523506416740556817875457 40142629812555417613406593)
          ·
            refine ⟨30106972359416563210054945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40142629812555417613406593 30106972359416563210054945)
            ·
              refine ⟨22580229269562422407541209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30106972359416563210054945 22580229269562422407541209)
              ·
                refine ⟨16935171952171816805655907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22580229269562422407541209 16935171952171816805655907)
                ·
                  refine ⟨25402757928257725208483861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16935171952171816805655907 25402757928257725208483861)
                  ·
                    refine ⟨1190754277887080869147681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25402757928257725208483861 1190754277887080869147681)
                    ·
                      rfl

theorem cell23_6956957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6956957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956957 prefixEnd_6956957 := by exact prefixLift 6956957
  have htrace : WordTrace (prefixWord ++ tailWord_6956957) baseStart_6956957 baseEnd_6956957 := by
    simpa [prefixWord, tailWord_6956957, baseEnd_6956957] using wordTrace_append hprefix tailTrace_6956957
  have hstable : (prefixWord ++ tailWord_6956957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956957).length < 2 ^ (prefixWord ++ tailWord_6956957).sum := by decide
  have hdescent : baseEnd_6956957 < baseStart_6956957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956960 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_6956960 : Nat := 118140960795 + 6956960 * 2 ^ 59
def prefixEnd_6956960 : Nat := 4983230072969 + 3 ^ 40 * 6956960 * 2
def baseEnd_6956960 : Nat := 3572264374103206095705529

theorem tailTrace_6956960 : CollatzResearch.WordTrace tailWord_6956960 prefixEnd_6956960 3572264374103206095705529 := by
  unfold tailWord_6956960
  simp only [CollatzResearch.WordTrace]
  refine ⟨126870588438064774509662167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169160784584086366012882889 126870588438064774509662167)
  ·
    refine ⟨190305882657097161764493251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126870588438064774509662167 190305882657097161764493251)
    ·
      refine ⟨285458823985645742646739877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190305882657097161764493251 285458823985645742646739877)
      ·
        refine ⟨53523529497308576746263727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285458823985645742646739877 53523529497308576746263727)
        ·
          refine ⟨80285294245962865119395591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53523529497308576746263727 80285294245962865119395591)
          ·
            refine ⟨120427941368944297679093387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80285294245962865119395591 120427941368944297679093387)
            ·
              refine ⟨180641912053416446518640081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120427941368944297679093387 180641912053416446518640081)
              ·
                refine ⟨135481434040062334888980061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180641912053416446518640081 135481434040062334888980061)
                ·
                  refine ⟨50805537765023375583367523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135481434040062334888980061 50805537765023375583367523)
                  ·
                    refine ⟨76208306647535063375051285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50805537765023375583367523 76208306647535063375051285)
                    ·
                      refine ⟨3572264374103206095705529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76208306647535063375051285 3572264374103206095705529)
                      ·
                        rfl

theorem cell23_6956960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_6956960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956960 prefixEnd_6956960 := by exact prefixLift 6956960
  have htrace : WordTrace (prefixWord ++ tailWord_6956960) baseStart_6956960 baseEnd_6956960 := by
    simpa [prefixWord, tailWord_6956960, baseEnd_6956960] using wordTrace_append hprefix tailTrace_6956960
  have hstable : (prefixWord ++ tailWord_6956960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956960).length < 2 ^ (prefixWord ++ tailWord_6956960).sum := by decide
  have hdescent : baseEnd_6956960 < baseStart_6956960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956964 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_6956964 : Nat := 118140960795 + 6956964 * 2 ^ 59
def prefixEnd_6956964 : Nat := 4983230072969 + 3 ^ 40 * 6956964 * 2
def baseEnd_6956964 : Nat := 3572266428025824080055511

theorem tailTrace_6956964 : CollatzResearch.WordTrace tailWord_6956964 prefixEnd_6956964 3572266428025824080055511 := by
  unfold tailWord_6956964
  simp only [CollatzResearch.WordTrace]
  refine ⟨126870661384057528851234973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169160881845410038468313297 126870661384057528851234973)
  ·
    refine ⟨47576498019021573319213115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126870661384057528851234973 47576498019021573319213115)
    ·
      refine ⟨71364747028532359978819673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47576498019021573319213115 71364747028532359978819673)
      ·
        refine ⟨53523560271399269984114755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71364747028532359978819673 53523560271399269984114755)
        ·
          refine ⟨80285340407098904976172133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53523560271399269984114755 80285340407098904976172133)
          ·
            refine ⟨15053501326331044683032275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80285340407098904976172133 15053501326331044683032275)
            ·
              refine ⟨22580251989496567024548413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15053501326331044683032275 22580251989496567024548413)
              ·
                refine ⟨8467594496061212634205655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22580251989496567024548413 8467594496061212634205655)
                ·
                  refine ⟨12701391744091818951308483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8467594496061212634205655 12701391744091818951308483)
                  ·
                    refine ⟨19052087616137728426962725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12701391744091818951308483 19052087616137728426962725)
                    ·
                      refine ⟨3572266428025824080055511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19052087616137728426962725 3572266428025824080055511)
                      ·
                        rfl

theorem cell23_6956964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_6956964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956964 prefixEnd_6956964 := by exact prefixLift 6956964
  have htrace : WordTrace (prefixWord ++ tailWord_6956964) baseStart_6956964 baseEnd_6956964 := by
    simpa [prefixWord, tailWord_6956964, baseEnd_6956964] using wordTrace_append hprefix tailTrace_6956964
  have hstable : (prefixWord ++ tailWord_6956964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956964).length < 2 ^ (prefixWord ++ tailWord_6956964).sum := by decide
  have hdescent : baseEnd_6956964 < baseStart_6956964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956981 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_6956981 : Nat := 118140960795 + 6956981 * 2 ^ 59
def prefixEnd_6956981 : Nat := 4983230072969 + 3 ^ 40 * 6956981 * 2
def baseEnd_6956981 : Nat := 3572275157196950513542933

theorem tailTrace_6956981 : CollatzResearch.WordTrace tailWord_6956981 prefixEnd_6956981 3572275157196950513542933 := by
  unfold tailWord_6956981
  simp only [CollatzResearch.WordTrace]
  refine ⟨253741942809053469605838797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169161295206035646403892531 253741942809053469605838797)
  ·
    refine ⟨95153228553395051102189549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253741942809053469605838797 95153228553395051102189549)
    ·
      refine ⟨35682460707523144163321081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95153228553395051102189549 35682460707523144163321081)
      ·
        refine ⟨26761845530642358122490811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35682460707523144163321081 26761845530642358122490811)
        ·
          refine ⟨40142768295963537183736217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26761845530642358122490811 40142768295963537183736217)
          ·
            refine ⟨30107076221972652887802163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40142768295963537183736217 30107076221972652887802163)
            ·
              refine ⟨45160614332958979331703245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30107076221972652887802163 45160614332958979331703245)
              ·
                refine ⟨16935230374859617249388717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45160614332958979331703245 16935230374859617249388717)
                ·
                  refine ⟨6350711390572356468520769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16935230374859617249388717 6350711390572356468520769)
                  ·
                    refine ⟨4763033542929267351390577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6350711390572356468520769 4763033542929267351390577)
                    ·
                      refine ⟨3572275157196950513542933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763033542929267351390577 3572275157196950513542933)
                      ·
                        rfl

theorem cell23_6956981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_6956981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956981 prefixEnd_6956981 := by exact prefixLift 6956981
  have htrace : WordTrace (prefixWord ++ tailWord_6956981) baseStart_6956981 baseEnd_6956981 := by
    simpa [prefixWord, tailWord_6956981, baseEnd_6956981] using wordTrace_append hprefix tailTrace_6956981
  have hstable : (prefixWord ++ tailWord_6956981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956981).length < 2 ^ (prefixWord ++ tailWord_6956981).sum := by decide
  have hdescent : baseEnd_6956981 < baseStart_6956981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6956997 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_6956997 : Nat := 118140960795 + 6956997 * 2 ^ 59
def prefixEnd_6956997 : Nat := 4983230072969 + 3 ^ 40 * 6956997 * 2
def baseEnd_6956997 : Nat := 3572283372887422450942859

theorem tailTrace_6956997 : CollatzResearch.WordTrace tailWord_6956997 prefixEnd_6956997 3572283372887422450942859 := by
  unfold tailWord_6956997
  simp only [CollatzResearch.WordTrace]
  refine ⟨253742526376995504338421245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169161684251330336225614163 253742526376995504338421245)
  ·
    refine ⟨95153447391373314126907967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253742526376995504338421245 95153447391373314126907967)
    ·
      refine ⟨142730171087059971190361951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95153447391373314126907967 142730171087059971190361951)
      ·
        refine ⟨214095256630589956785542927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142730171087059971190361951 214095256630589956785542927)
        ·
          refine ⟨321142884945884935178314391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214095256630589956785542927 321142884945884935178314391)
          ·
            refine ⟨481714327418827402767471587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321142884945884935178314391 481714327418827402767471587)
            ·
              refine ⟨722571491128241104151207381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481714327418827402767471587 722571491128241104151207381)
              ·
                refine ⟨16935269323318150878543923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 722571491128241104151207381 16935269323318150878543923)
                ·
                  refine ⟨25402903984977226317815885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16935269323318150878543923 25402903984977226317815885)
                  ·
                    refine ⟨9526088994366459869180957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25402903984977226317815885 9526088994366459869180957)
                    ·
                      refine ⟨3572283372887422450942859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526088994366459869180957 3572283372887422450942859)
                      ·
                        rfl

theorem cell23_6956997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_6956997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6956997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6956997 prefixEnd_6956997 := by exact prefixLift 6956997
  have htrace : WordTrace (prefixWord ++ tailWord_6956997) baseStart_6956997 baseEnd_6956997 := by
    simpa [prefixWord, tailWord_6956997, baseEnd_6956997] using wordTrace_append hprefix tailTrace_6956997
  have hstable : (prefixWord ++ tailWord_6956997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6956997).length < 2 ^ (prefixWord ++ tailWord_6956997).sum := by decide
  have hdescent : baseEnd_6956997 < baseStart_6956997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6956997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957004 : List Nat := [2, 2, 1, 4, 1, 4, 2, 7]
def baseStart_6957004 : Nat := 118140960795 + 6957004 * 2 ^ 59
def prefixEnd_6957004 : Nat := 4983230072969 + 3 ^ 40 * 6957004 * 2
def baseEnd_6957004 : Nat := 132306924713037182353901

theorem tailTrace_6957004 : CollatzResearch.WordTrace tailWord_6957004 prefixEnd_6957004 132306924713037182353901 := by
  unfold tailWord_6957004
  simp only [CollatzResearch.WordTrace]
  refine ⟨126871390843985072266963033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169161854458646763022617377 126871390843985072266963033)
  ·
    refine ⟨95153543132988804200222275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126871390843985072266963033 95153543132988804200222275)
    ·
      refine ⟨142730314699483206300333413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95153543132988804200222275 142730314699483206300333413)
      ·
        refine ⟨26761934006153101181312515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142730314699483206300333413 26761934006153101181312515)
        ·
          refine ⟨40142901009229651771968773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26761934006153101181312515 40142901009229651771968773)
          ·
            refine ⟨7526793939230559707244145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40142901009229651771968773 7526793939230559707244145)
            ·
              refine ⟨5645095454422919780433109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526793939230559707244145 5645095454422919780433109)
              ·
                refine ⟨132306924713037182353901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5645095454422919780433109 132306924713037182353901)
                ·
                  rfl

theorem cell23_6957004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 7].length) (baseStart_6957004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957004 prefixEnd_6957004 := by exact prefixLift 6957004
  have htrace : WordTrace (prefixWord ++ tailWord_6957004) baseStart_6957004 baseEnd_6957004 := by
    simpa [prefixWord, tailWord_6957004, baseEnd_6957004] using wordTrace_append hprefix tailTrace_6957004
  have hstable : (prefixWord ++ tailWord_6957004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957004).length < 2 ^ (prefixWord ++ tailWord_6957004).sum := by decide
  have hdescent : baseEnd_6957004 < baseStart_6957004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957057 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6957057 : Nat := 118140960795 + 6957057 * 2 ^ 59
def prefixEnd_6957057 : Nat := 4983230072969 + 3 ^ 40 * 6957057 * 2
def baseEnd_6957057 : Nat := 3572314181726692216192583

theorem tailTrace_6957057 : CollatzResearch.WordTrace tailWord_6957057 prefixEnd_6957057 3572314181726692216192583 := by
  unfold tailWord_6957057
  simp only [CollatzResearch.WordTrace]
  refine ⟨253744714756778134585605425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169163143171185423057070283 253744714756778134585605425)
  ·
    refine ⟨190308536067583600939204069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253744714756778134585605425 190308536067583600939204069)
    ·
      refine ⟨35682850512671925176100763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190308536067583600939204069 35682850512671925176100763)
      ·
        refine ⟨53524275769007887764151145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35682850512671925176100763 53524275769007887764151145)
        ·
          refine ⟨40143206826755915823113359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53524275769007887764151145 40143206826755915823113359)
          ·
            refine ⟨60214810240133873734670039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40143206826755915823113359 60214810240133873734670039)
            ·
              refine ⟨90322215360200810602005059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60214810240133873734670039 90322215360200810602005059)
              ·
                refine ⟨135483323040301215903007589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90322215360200810602005059 135483323040301215903007589)
                ·
                  refine ⟨25403123070056477981813923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135483323040301215903007589 25403123070056477981813923)
                  ·
                    refine ⟨38104684605084716972720885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25403123070056477981813923 38104684605084716972720885)
                    ·
                      refine ⟨3572314181726692216192583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38104684605084716972720885 3572314181726692216192583)
                      ·
                        rfl

theorem cell23_6957057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6957057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957057 prefixEnd_6957057 := by exact prefixLift 6957057
  have htrace : WordTrace (prefixWord ++ tailWord_6957057) baseStart_6957057 baseEnd_6957057 := by
    simpa [prefixWord, tailWord_6957057, baseEnd_6957057] using wordTrace_append hprefix tailTrace_6957057
  have hstable : (prefixWord ++ tailWord_6957057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957057).length < 2 ^ (prefixWord ++ tailWord_6957057).sum := by decide
  have hdescent : baseEnd_6957057 < baseStart_6957057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957104 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3]
def baseStart_6957104 : Nat := 118140960795 + 6957104 * 2 ^ 59
def prefixEnd_6957104 : Nat := 4983230072969 + 3 ^ 40 * 6957104 * 2
def baseEnd_6957104 : Nat := 3572338315317453532304867

theorem tailTrace_6957104 : CollatzResearch.WordTrace tailWord_6957104 prefixEnd_6957104 3572338315317453532304867 := by
  unfold tailWord_6957104
  simp only [CollatzResearch.WordTrace]
  refine ⟨126873214493803930806283183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169164285991738574408377577 126873214493803930806283183)
  ·
    refine ⟨190309821740705896209424775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126873214493803930806283183 190309821740705896209424775)
    ·
      refine ⟨285464732611058844314137163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190309821740705896209424775 285464732611058844314137163)
      ·
        refine ⟨428197098916588266471205745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285464732611058844314137163 428197098916588266471205745)
        ·
          refine ⟨321147824187441199853404309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428197098916588266471205745 321147824187441199853404309)
          ·
            refine ⟨15053804258786306243128327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 321147824187441199853404309 15053804258786306243128327)
            ·
              refine ⟨22580706388179459364692491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15053804258786306243128327 22580706388179459364692491)
              ·
                refine ⟨33871059582269189047038737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22580706388179459364692491 33871059582269189047038737)
                ·
                  refine ⟨25403294686701891785279053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33871059582269189047038737 25403294686701891785279053)
                  ·
                    refine ⟨9526235507513209419479645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25403294686701891785279053 9526235507513209419479645)
                    ·
                      refine ⟨3572338315317453532304867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526235507513209419479645 3572338315317453532304867)
                      ·
                        rfl

theorem cell23_6957104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_6957104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957104 prefixEnd_6957104 := by exact prefixLift 6957104
  have htrace : WordTrace (prefixWord ++ tailWord_6957104) baseStart_6957104 baseEnd_6957104 := by
    simpa [prefixWord, tailWord_6957104, baseEnd_6957104] using wordTrace_append hprefix tailTrace_6957104
  have hstable : (prefixWord ++ tailWord_6957104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957104).length < 2 ^ (prefixWord ++ tailWord_6957104).sum := by decide
  have hdescent : baseEnd_6957104 < baseStart_6957104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957107 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 4, 5]
def baseStart_6957107 : Nat := 118140960795 + 6957107 * 2 ^ 59
def prefixEnd_6957107 : Nat := 4983230072969 + 3 ^ 40 * 6957107 * 2
def baseEnd_6957107 : Nat := 1190779951919805673522451

theorem tailTrace_6957107 : CollatzResearch.WordTrace tailWord_6957107 prefixEnd_6957107 1190779951919805673522451 := by
  unfold tailWord_6957107
  simp only [CollatzResearch.WordTrace]
  refine ⟨253746538406596993124925575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169164358937731328749950383 253746538406596993124925575)
  ·
    refine ⟨380619807609895489687388363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253746538406596993124925575 380619807609895489687388363)
    ·
      refine ⟨570929711414843234531082545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380619807609895489687388363 570929711414843234531082545)
      ·
        refine ⟨428197283561132425898311909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570929711414843234531082545 428197283561132425898311909)
        ·
          refine ⟨80286990667712329855933483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428197283561132425898311909 80286990667712329855933483)
          ·
            refine ⟨120430486001568494783900225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80286990667712329855933483 120430486001568494783900225)
            ·
              refine ⟨90322864501176371087925169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120430486001568494783900225 90322864501176371087925169)
              ·
                refine ⟨67742148375882278315943877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90322864501176371087925169 67742148375882278315943877)
                ·
                  refine ⟨12701652820477927184239477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67742148375882278315943877 12701652820477927184239477)
                  ·
                    refine ⟨1190779951919805673522451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12701652820477927184239477 1190779951919805673522451)
                    ·
                      rfl

theorem cell23_6957107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 5].length) (baseStart_6957107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957107 prefixEnd_6957107 := by exact prefixLift 6957107
  have htrace : WordTrace (prefixWord ++ tailWord_6957107) baseStart_6957107 baseEnd_6957107 := by
    simpa [prefixWord, tailWord_6957107, baseEnd_6957107] using wordTrace_append hprefix tailTrace_6957107
  have hstable : (prefixWord ++ tailWord_6957107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957107).length < 2 ^ (prefixWord ++ tailWord_6957107).sum := by decide
  have hdescent : baseEnd_6957107 < baseStart_6957107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957114 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2]
def baseStart_6957114 : Nat := 118140960795 + 6957114 * 2 ^ 59
def prefixEnd_6957114 : Nat := 4983230072969 + 3 ^ 40 * 6957114 * 2
def baseEnd_6957114 : Nat := 3572343450123998493179821

theorem tailTrace_6957114 : CollatzResearch.WordTrace tailWord_6957114 prefixEnd_6957114 3572343450123998493179821 := by
  unfold tailWord_6957114
  simp only [CollatzResearch.WordTrace]
  refine ⟨63436698429392908330107599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169164529145047755546953597 63436698429392908330107599)
  ·
    refine ⟨95155047644089362495161399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63436698429392908330107599 95155047644089362495161399)
    ·
      refine ⟨142732571466134043742742099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95155047644089362495161399 142732571466134043742742099)
      ·
        refine ⟨214098857199201065614113149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142732571466134043742742099 214098857199201065614113149)
        ·
          refine ⟨80287071449700399605292431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214098857199201065614113149 80287071449700399605292431)
          ·
            refine ⟨120430607174550599407938647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80287071449700399605292431 120430607174550599407938647)
            ·
              refine ⟨180645910761825899111907971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120430607174550599407938647 180645910761825899111907971)
              ·
                refine ⟨270968866142738848667861957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180645910761825899111907971 270968866142738848667861957)
                ·
                  refine ⟨50806662401763534125224117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270968866142738848667861957 50806662401763534125224117)
                  ·
                    refine ⟨4763124600165331324239761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50806662401763534125224117 4763124600165331324239761)
                    ·
                      refine ⟨3572343450123998493179821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763124600165331324239761 3572343450123998493179821)
                      ·
                        rfl

theorem cell23_6957114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_6957114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957114 prefixEnd_6957114 := by exact prefixLift 6957114
  have htrace : WordTrace (prefixWord ++ tailWord_6957114) baseStart_6957114 baseEnd_6957114 := by
    simpa [prefixWord, tailWord_6957114, baseEnd_6957114] using wordTrace_append hprefix tailTrace_6957114
  have hstable : (prefixWord ++ tailWord_6957114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957114).length < 2 ^ (prefixWord ++ tailWord_6957114).sum := by decide
  have hdescent : baseEnd_6957114 < baseStart_6957114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957164 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_6957164 : Nat := 118140960795 + 6957164 * 2 ^ 59
def prefixEnd_6957164 : Nat := 4983230072969 + 3 ^ 40 * 6957164 * 2
def baseEnd_6957164 : Nat := 3572369124156723297554591

theorem tailTrace_6957164 : CollatzResearch.WordTrace tailWord_6957164 prefixEnd_6957164 3572369124156723297554591 := by
  unfold tailWord_6957164
  simp only [CollatzResearch.WordTrace]
  refine ⟨126874308683695245929875273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169165744911593661239833697 126874308683695245929875273)
  ·
    refine ⟨95155731512771434447406455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126874308683695245929875273 95155731512771434447406455)
    ·
      refine ⟨142733597269157151671109683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95155731512771434447406455 142733597269157151671109683)
      ·
        refine ⟨214100395903735727506664525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142733597269157151671109683 214100395903735727506664525)
        ·
          refine ⟨80287648463900897814999197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214100395903735727506664525 80287648463900897814999197)
          ·
            refine ⟨30107868173962836680624699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80287648463900897814999197 30107868173962836680624699)
            ·
              refine ⟨45161802260944255020937049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30107868173962836680624699 45161802260944255020937049)
              ·
                refine ⟨33871351695708191265702787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45161802260944255020937049 33871351695708191265702787)
                ·
                  refine ⟨50807027543562286898554181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33871351695708191265702787 50807027543562286898554181)
                  ·
                    refine ⟨9526317664417928793478909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50807027543562286898554181 9526317664417928793478909)
                    ·
                      refine ⟨3572369124156723297554591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526317664417928793478909 3572369124156723297554591)
                      ·
                        rfl

theorem cell23_6957164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_6957164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957164 prefixEnd_6957164 := by exact prefixLift 6957164
  have htrace : WordTrace (prefixWord ++ tailWord_6957164) baseStart_6957164 baseEnd_6957164 := by
    simpa [prefixWord, tailWord_6957164, baseEnd_6957164] using wordTrace_append hprefix tailTrace_6957164
  have hstable : (prefixWord ++ tailWord_6957164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957164).length < 2 ^ (prefixWord ++ tailWord_6957164).sum := by decide
  have hdescent : baseEnd_6957164 < baseStart_6957164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957198 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6957198 : Nat := 118140960795 + 6957198 * 2 ^ 59
def prefixEnd_6957198 : Nat := 4983230072969 + 3 ^ 40 * 6957198 * 2
def baseEnd_6957198 : Nat := 3572386582498976164529435

theorem tailTrace_6957198 : CollatzResearch.WordTrace tailWord_6957198 prefixEnd_6957198 3572386582498976164529435 := by
  unfold tailWord_6957198
  simp only [CollatzResearch.WordTrace]
  refine ⟨31718732181158414458311031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169166571632844877110992165 31718732181158414458311031)
  ·
    refine ⟨47578098271737621687466547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31718732181158414458311031 47578098271737621687466547)
    ·
      refine ⟨71367147407606432531199821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47578098271737621687466547 71367147407606432531199821)
      ·
        refine ⟨26762680277852412199199933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71367147407606432531199821 26762680277852412199199933)
        ·
          refine ⟨10036005104194654574699975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26762680277852412199199933 10036005104194654574699975)
          ·
            refine ⟨15054007656291981862049963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036005104194654574699975 15054007656291981862049963)
            ·
              refine ⟨22581011484437972793074945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15054007656291981862049963 22581011484437972793074945)
              ·
                refine ⟨16935758613328479594806209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22581011484437972793074945 16935758613328479594806209)
                ·
                  refine ⟨12701818959996359696104657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16935758613328479594806209 12701818959996359696104657)
                  ·
                    refine ⟨9526364219997269772078493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12701818959996359696104657 9526364219997269772078493)
                    ·
                      refine ⟨3572386582498976164529435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526364219997269772078493 3572386582498976164529435)
                      ·
                        rfl

theorem cell23_6957198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6957198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957198 prefixEnd_6957198 := by exact prefixLift 6957198
  have htrace : WordTrace (prefixWord ++ tailWord_6957198) baseStart_6957198 baseEnd_6957198 := by
    simpa [prefixWord, tailWord_6957198, baseEnd_6957198] using wordTrace_append hprefix tailTrace_6957198
  have hstable : (prefixWord ++ tailWord_6957198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957198).length < 2 ^ (prefixWord ++ tailWord_6957198).sum := by decide
  have hdescent : baseEnd_6957198 < baseStart_6957198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957218 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_6957218 : Nat := 118140960795 + 6957218 * 2 ^ 59
def prefixEnd_6957218 : Nat := 4983230072969 + 3 ^ 40 * 6957218 * 2
def baseEnd_6957218 : Nat := 396932983568007342919927

theorem tailTrace_6957218 : CollatzResearch.WordTrace tailWord_6957218 prefixEnd_6957218 396932983568007342919927 := by
  unfold tailWord_6957218
  simp only [CollatzResearch.WordTrace]
  refine ⟨63437646727298714770554077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169167057939463239388144205 63437646727298714770554077)
  ·
    refine ⟨23789117522737018038957779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63437646727298714770554077 23789117522737018038957779)
    ·
      refine ⟨35683676284105527058436669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23789117522737018038957779 35683676284105527058436669)
      ·
        refine ⟨13381378606539572646913751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35683676284105527058436669 13381378606539572646913751)
        ·
          refine ⟨20072067909809358970370627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381378606539572646913751 20072067909809358970370627)
          ·
            refine ⟨30108101864714038455555941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20072067909809358970370627 30108101864714038455555941)
            ·
              refine ⟨5645269099633882210416739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30108101864714038455555941 5645269099633882210416739)
              ·
                refine ⟨8467903649450823315625109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645269099633882210416739 8467903649450823315625109)
                ·
                  refine ⟨396932983568007342919927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8467903649450823315625109 396932983568007342919927)
                  ·
                    rfl

theorem cell23_6957218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_6957218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957218 prefixEnd_6957218 := by exact prefixLift 6957218
  have htrace : WordTrace (prefixWord ++ tailWord_6957218) baseStart_6957218 baseEnd_6957218 := by
    simpa [prefixWord, tailWord_6957218, baseEnd_6957218] using wordTrace_append hprefix tailTrace_6957218
  have hstable : (prefixWord ++ tailWord_6957218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957218).length < 2 ^ (prefixWord ++ tailWord_6957218).sum := by decide
  have hdescent : baseEnd_6957218 < baseStart_6957218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957221 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 4, 3, 2]
def baseStart_6957221 : Nat := 118140960795 + 6957221 * 2 ^ 59
def prefixEnd_6957221 : Nat := 4983230072969 + 3 ^ 40 * 6957221 * 2
def baseEnd_6957221 : Nat := 3572398392554029574541829

theorem tailTrace_6957221 : CollatzResearch.WordTrace tailWord_6957221 prefixEnd_6957221 3572398392554029574541829 := by
  unfold tailWord_6957221
  simp only [CollatzResearch.WordTrace]
  refine ⟨253750696328183990594575517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169167130885455993729717011 253750696328183990594575517)
  ·
    refine ⟨95156511123068996472965819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253750696328183990594575517 95156511123068996472965819)
    ·
      refine ⟨142734766684603494709448729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95156511123068996472965819 142734766684603494709448729)
      ·
        refine ⟨107051075013452621032086547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142734766684603494709448729 107051075013452621032086547)
        ·
          refine ⟨160576612520178931548129821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107051075013452621032086547 160576612520178931548129821)
          ·
            refine ⟨60216229695067099330548683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160576612520178931548129821 60216229695067099330548683)
            ·
              refine ⟨90324344542600648995823025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60216229695067099330548683 90324344542600648995823025)
              ·
                refine ⟨67743258406950486746867269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90324344542600648995823025 67743258406950486746867269)
                ·
                  refine ⟨12701860951303216265037613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67743258406950486746867269 12701860951303216265037613)
                  ·
                    refine ⟨4763197856738706099389105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12701860951303216265037613 4763197856738706099389105)
                    ·
                      refine ⟨3572398392554029574541829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763197856738706099389105 3572398392554029574541829)
                      ·
                        rfl

theorem cell23_6957221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_6957221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957221 prefixEnd_6957221 := by exact prefixLift 6957221
  have htrace : WordTrace (prefixWord ++ tailWord_6957221) baseStart_6957221 baseEnd_6957221 := by
    simpa [prefixWord, tailWord_6957221, baseEnd_6957221] using wordTrace_append hprefix tailTrace_6957221
  have hstable : (prefixWord ++ tailWord_6957221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957221).length < 2 ^ (prefixWord ++ tailWord_6957221).sum := by decide
  have hdescent : baseEnd_6957221 < baseStart_6957221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957248 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 1, 5]
def baseStart_6957248 : Nat := 118140960795 + 6957248 * 2 ^ 59
def prefixEnd_6957248 : Nat := 4983230072969 + 3 ^ 40 * 6957248 * 2
def baseEnd_6957248 : Nat := 1190804085510566989634735

theorem tailTrace_6957248 : CollatzResearch.WordTrace tailWord_6957248 prefixEnd_6957248 1190804085510566989634735 := by
  unfold tailWord_6957248
  simp only [CollatzResearch.WordTrace]
  refine ⟨126875840549543087102904199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169167787399390782803872265 126875840549543087102904199)
  ·
    refine ⟨190313760824314630654356299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126875840549543087102904199 190313760824314630654356299)
    ·
      refine ⟨285470641236471945981534449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190313760824314630654356299 285470641236471945981534449)
      ·
        refine ⟨214102980927353959486150837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285470641236471945981534449 214102980927353959486150837)
        ·
          refine ⟨20072154461939433701826641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214102980927353959486150837 20072154461939433701826641)
          ·
            refine ⟨15054115846454575276369981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20072154461939433701826641 15054115846454575276369981)
            ·
              refine ⟨5645293442420465728638743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15054115846454575276369981 5645293442420465728638743)
              ·
                refine ⟨8467940163630698592958115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645293442420465728638743 8467940163630698592958115)
                ·
                  refine ⟨12701910245446047889437173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8467940163630698592958115 12701910245446047889437173)
                  ·
                    refine ⟨1190804085510566989634735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12701910245446047889437173 1190804085510566989634735)
                    ·
                      rfl

theorem cell23_6957248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 1, 5].length) (baseStart_6957248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957248 prefixEnd_6957248 := by exact prefixLift 6957248
  have htrace : WordTrace (prefixWord ++ tailWord_6957248) baseStart_6957248 baseEnd_6957248 := by
    simpa [prefixWord, tailWord_6957248, baseEnd_6957248] using wordTrace_append hprefix tailTrace_6957248
  have hstable : (prefixWord ++ tailWord_6957248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957248).length < 2 ^ (prefixWord ++ tailWord_6957248).sum := by decide
  have hdescent : baseEnd_6957248 < baseStart_6957248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957262 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_6957262 : Nat := 118140960795 + 6957262 * 2 ^ 59
def prefixEnd_6957262 : Nat := 4983230072969 + 3 ^ 40 * 6957262 * 2
def baseEnd_6957262 : Nat := 3572419445260863914129141

theorem tailTrace_6957262 : CollatzResearch.WordTrace tailWord_6957262 prefixEnd_6957262 3572419445260863914129141 := by
  unfold tailWord_6957262
  simp only [CollatzResearch.WordTrace]
  refine ⟨31719023965129431824602255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169168127814023636397878693 31719023965129431824602255)
  ·
    refine ⟨47578535947694147736903383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31719023965129431824602255 47578535947694147736903383)
    ·
      refine ⟨71367803921541221605355075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47578535947694147736903383 71367803921541221605355075)
      ·
        refine ⟨107051705882311832408032613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71367803921541221605355075 107051705882311832408032613)
        ·
          refine ⟨20072194852933468576506115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107051705882311832408032613 20072194852933468576506115)
          ·
            refine ⟨30108292279400202864759173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20072194852933468576506115 30108292279400202864759173)
            ·
              refine ⟨5645304802387538037142345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30108292279400202864759173 5645304802387538037142345)
              ·
                refine ⟨4233978601790653527856759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5645304802387538037142345 4233978601790653527856759)
                ·
                  refine ⟨6350967902685980291785139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4233978601790653527856759 6350967902685980291785139)
                  ·
                    refine ⟨9526451854028970437677709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6350967902685980291785139 9526451854028970437677709)
                    ·
                      refine ⟨3572419445260863914129141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526451854028970437677709 3572419445260863914129141)
                      ·
                        rfl

theorem cell23_6957262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_6957262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957262 prefixEnd_6957262 := by exact prefixLift 6957262
  have htrace : WordTrace (prefixWord ++ tailWord_6957262) baseStart_6957262 baseEnd_6957262 := by
    simpa [prefixWord, tailWord_6957262, baseEnd_6957262] using wordTrace_append hprefix tailTrace_6957262
  have hstable : (prefixWord ++ tailWord_6957262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957262).length < 2 ^ (prefixWord ++ tailWord_6957262).sum := by decide
  have hdescent : baseEnd_6957262 < baseStart_6957262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957274 : List Nat := [3, 1, 1, 2, 2, 1, 5, 8]
def baseStart_6957274 : Nat := 118140960795 + 6957274 * 2 ^ 59
def prefixEnd_6957274 : Nat := 4983230072969 + 3 ^ 40 * 6957274 * 2
def baseEnd_6957274 : Nat := 132312059519582143228855

theorem tailTrace_6957274 : CollatzResearch.WordTrace tailWord_6957274 prefixEnd_6957274 132312059519582143228855 := by
  unfold tailWord_6957274
  simp only [CollatzResearch.WordTrace]
  refine ⟨63438157349247995161563719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169168419597994653764169917 63438157349247995161563719)
  ·
    refine ⟨95157236023871992742345579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63438157349247995161563719 95157236023871992742345579)
    ·
      refine ⟨142735854035807989113518369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95157236023871992742345579 142735854035807989113518369)
      ·
        refine ⟨107051890526855991835138777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142735854035807989113518369 107051890526855991835138777)
        ·
          refine ⟨80288917895141993876354083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107051890526855991835138777 80288917895141993876354083)
          ·
            refine ⟨120433376842712990814531125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80288917895141993876354083 120433376842712990814531125)
            ·
              refine ⟨11290629079004342888862293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120433376842712990814531125 11290629079004342888862293)
              ·
                refine ⟨132312059519582143228855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11290629079004342888862293 132312059519582143228855)
                ·
                  rfl

theorem cell23_6957274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_6957274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957274 prefixEnd_6957274 := by exact prefixLift 6957274
  have htrace : WordTrace (prefixWord ++ tailWord_6957274) baseStart_6957274 baseEnd_6957274 := by
    simpa [prefixWord, tailWord_6957274, baseEnd_6957274] using wordTrace_append hprefix tailTrace_6957274
  have hstable : (prefixWord ++ tailWord_6957274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957274).length < 2 ^ (prefixWord ++ tailWord_6957274).sum := by decide
  have hdescent : baseEnd_6957274 < baseStart_6957274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957281 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_6957281 : Nat := 118140960795 + 6957281 * 2 ^ 59
def prefixEnd_6957281 : Nat := 4983230072969 + 3 ^ 40 * 6957281 * 2
def baseEnd_6957281 : Nat := 3572429201393299339791553

theorem tailTrace_6957281 : CollatzResearch.WordTrace tailWord_6957281 prefixEnd_6957281 3572429201393299339791553 := by
  unfold tailWord_6957281
  simp only [CollatzResearch.WordTrace]
  refine ⟨253752884707966620841759697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169168589805311080561173131 253752884707966620841759697)
  ·
    refine ⟨190314663530974965631319773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253752884707966620841759697 190314663530974965631319773)
    ·
      refine ⟨71367998824115612111744915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190314663530974965631319773 71367998824115612111744915)
      ·
        refine ⟨107051998236173418167617373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71367998824115612111744915 107051998236173418167617373)
        ·
          refine ⟨40144499338565031812856515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107051998236173418167617373 40144499338565031812856515)
          ·
            refine ⟨60216749007847547719284773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40144499338565031812856515 60216749007847547719284773)
            ·
              refine ⟨11290640438971415197365895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60216749007847547719284773 11290640438971415197365895)
              ·
                refine ⟨16935960658457122796048843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11290640438971415197365895 16935960658457122796048843)
                ·
                  refine ⟨25403940987685684194073265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16935960658457122796048843 25403940987685684194073265)
                  ·
                    refine ⟨19052955740764263145554949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25403940987685684194073265 19052955740764263145554949)
                    ·
                      refine ⟨3572429201393299339791553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19052955740764263145554949 3572429201393299339791553)
                      ·
                        rfl

theorem cell23_6957281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_6957281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957281 prefixEnd_6957281 := by exact prefixLift 6957281
  have htrace : WordTrace (prefixWord ++ tailWord_6957281) baseStart_6957281 baseEnd_6957281 := by
    simpa [prefixWord, tailWord_6957281, baseEnd_6957281] using wordTrace_append hprefix tailTrace_6957281
  have hstable : (prefixWord ++ tailWord_6957281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957281).length < 2 ^ (prefixWord ++ tailWord_6957281).sum := by decide
  have hdescent : baseEnd_6957281 < baseStart_6957281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957285 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6957285 : Nat := 118140960795 + 6957285 * 2 ^ 59
def prefixEnd_6957285 : Nat := 4983230072969 + 3 ^ 40 * 6957285 * 2
def baseEnd_6957285 : Nat := 3572431255315917324141535

theorem tailTrace_6957285 : CollatzResearch.WordTrace tailWord_6957285 prefixEnd_6957285 3572431255315917324141535 := by
  unfold tailWord_6957285
  simp only [CollatzResearch.WordTrace]
  refine ⟨253753030599952129524905309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169168687066634753016603539 253753030599952129524905309)
  ·
    refine ⟨95157386474982048571839491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253753030599952129524905309 95157386474982048571839491)
    ·
      refine ⟨142736079712473072857759237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95157386474982048571839491 142736079712473072857759237)
      ·
        refine ⟨26763014946088701160829857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142736079712473072857759237 26763014946088701160829857)
        ·
          refine ⟨20072261209566525870622393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26763014946088701160829857 20072261209566525870622393)
          ·
            refine ⟨15054195907174894402966795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20072261209566525870622393 15054195907174894402966795)
            ·
              refine ⟨22581293860762341604450193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15054195907174894402966795 22581293860762341604450193)
              ·
                refine ⟨16935970395571756203337645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22581293860762341604450193 16935970395571756203337645)
                ·
                  refine ⟨6350988898339408576251617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16935970395571756203337645 6350988898339408576251617)
                  ·
                    refine ⟨4763241673754556432188713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6350988898339408576251617 4763241673754556432188713)
                    ·
                      refine ⟨3572431255315917324141535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763241673754556432188713 3572431255315917324141535)
                      ·
                        rfl

theorem cell23_6957285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6957285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957285 prefixEnd_6957285 := by exact prefixLift 6957285
  have htrace : WordTrace (prefixWord ++ tailWord_6957285) baseStart_6957285 baseEnd_6957285 := by
    simpa [prefixWord, tailWord_6957285, baseEnd_6957285] using wordTrace_append hprefix tailTrace_6957285
  have hstable : (prefixWord ++ tailWord_6957285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957285).length < 2 ^ (prefixWord ++ tailWord_6957285).sum := by decide
  have hdescent : baseEnd_6957285 < baseStart_6957285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957302 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_6957302 : Nat := 118140960795 + 6957302 * 2 ^ 59
def prefixEnd_6957302 : Nat := 4983230072969 + 3 ^ 40 * 6957302 * 2
def baseEnd_6957302 : Nat := 3572439984487043757628957

theorem tailTrace_6957302 : CollatzResearch.WordTrace tailWord_6957302 prefixEnd_6957302 3572439984487043757628957 := by
  unfold tailWord_6957302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859603165055658839267135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169169100427260360952182773 15859603165055658839267135)
  ·
    refine ⟨23789404747583488258900703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15859603165055658839267135 23789404747583488258900703)
    ·
      refine ⟨35684107121375232388351055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23789404747583488258900703 35684107121375232388351055)
      ·
        refine ⟨53526160682062848582526583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35684107121375232388351055 53526160682062848582526583)
        ·
          refine ⟨80289241023094272873789875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53526160682062848582526583 80289241023094272873789875)
          ·
            refine ⟨120433861534641409310684813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80289241023094272873789875 120433861534641409310684813)
            ·
              refine ⟨45162698075490528491506805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120433861534641409310684813 45162698075490528491506805)
              ·
                refine ⟨4234002944577237046078763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45162698075490528491506805 4234002944577237046078763)
                ·
                  refine ⟨6351004416865855569118145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234002944577237046078763 6351004416865855569118145)
                  ·
                    refine ⟨4763253312649391676838609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351004416865855569118145 4763253312649391676838609)
                    ·
                      refine ⟨3572439984487043757628957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763253312649391676838609 3572439984487043757628957)
                      ·
                        rfl

theorem cell23_6957302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_6957302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957302 prefixEnd_6957302 := by exact prefixLift 6957302
  have htrace : WordTrace (prefixWord ++ tailWord_6957302) baseStart_6957302 baseEnd_6957302 := by
    simpa [prefixWord, tailWord_6957302, baseEnd_6957302] using wordTrace_append hprefix tailTrace_6957302
  have hstable : (prefixWord ++ tailWord_6957302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957302).length < 2 ^ (prefixWord ++ tailWord_6957302).sum := by decide
  have hdescent : baseEnd_6957302 < baseStart_6957302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957375 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 2, 2, 2]
def baseStart_6957375 : Nat := 118140960795 + 6957375 * 2 ^ 59
def prefixEnd_6957375 : Nat := 4983230072969 + 3 ^ 40 * 6957375 * 2
def baseEnd_6957375 : Nat := 3572477468574821972016121

theorem tailTrace_6957375 : CollatzResearch.WordTrace tailWord_6957375 prefixEnd_6957375 3572477468574821972016121 := by
  unfold tailWord_6957375
  simp only [CollatzResearch.WordTrace]
  refine ⟨253756313169626074895681579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169170875446417383263787719 253756313169626074895681579)
  ·
    refine ⟨380634469754439112343522369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253756313169626074895681579 380634469754439112343522369)
    ·
      refine ⟨285475852315829334257641777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380634469754439112343522369 285475852315829334257641777)
      ·
        refine ⟨214106889236872000693231333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285475852315829334257641777 214106889236872000693231333)
        ·
          refine ⟨40145041731913500129980875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214106889236872000693231333 40145041731913500129980875)
          ·
            refine ⟨60217562597870250194971313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40145041731913500129980875 60217562597870250194971313)
            ·
              refine ⟨45163171948402687646228485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60217562597870250194971313 45163171948402687646228485)
              ·
                refine ⟨8468094740325503933667841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45163171948402687646228485 8468094740325503933667841)
                ·
                  refine ⟨6351071055244127950250881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8468094740325503933667841 6351071055244127950250881)
                  ·
                    refine ⟨4763303291433095962688161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351071055244127950250881 4763303291433095962688161)
                    ·
                      refine ⟨3572477468574821972016121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763303291433095962688161 3572477468574821972016121)
                      ·
                        rfl

theorem cell23_6957375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_6957375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957375 prefixEnd_6957375 := by exact prefixLift 6957375
  have htrace : WordTrace (prefixWord ++ tailWord_6957375) baseStart_6957375 baseEnd_6957375 := by
    simpa [prefixWord, tailWord_6957375, baseEnd_6957375] using wordTrace_append hprefix tailTrace_6957375
  have hstable : (prefixWord ++ tailWord_6957375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957375).length < 2 ^ (prefixWord ++ tailWord_6957375).sum := by decide
  have hdescent : baseEnd_6957375 < baseStart_6957375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957392 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 2, 2, 2]
def baseStart_6957392 : Nat := 118140960795 + 6957392 * 2 ^ 59
def prefixEnd_6957392 : Nat := 4983230072969 + 3 ^ 40 * 6957392 * 2
def baseEnd_6957392 : Nat := 3572486197745948405503543

theorem tailTrace_6957392 : CollatzResearch.WordTrace tailWord_6957392 prefixEnd_6957392 3572486197745948405503543 := by
  unfold tailWord_6957392
  simp only [CollatzResearch.WordTrace]
  refine ⟨126878466605282243399525215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169171288807042991199366953 126878466605282243399525215)
  ·
    refine ⟨190317699907923365099287823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126878466605282243399525215 190317699907923365099287823)
    ·
      refine ⟨285476549861885047648931735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190317699907923365099287823 285476549861885047648931735)
      ·
        refine ⟨428214824792827571473397603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285476549861885047648931735 428214824792827571473397603)
        ·
          refine ⟨642322237189241357210096405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428214824792827571473397603 642322237189241357210096405)
          ·
            refine ⟨30108854868245688619223269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 642322237189241357210096405 30108854868245688619223269)
            ·
              refine ⟨5645410287796066616104363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30108854868245688619223269 5645410287796066616104363)
              ·
                refine ⟨8468115431694099924156545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645410287796066616104363 8468115431694099924156545)
                ·
                  refine ⟨6351086573770574943117409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8468115431694099924156545 6351086573770574943117409)
                  ·
                    refine ⟨4763314930327931207338057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351086573770574943117409 4763314930327931207338057)
                    ·
                      refine ⟨3572486197745948405503543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763314930327931207338057 3572486197745948405503543)
                      ·
                        rfl

theorem cell23_6957392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 2, 2].length) (baseStart_6957392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957392 prefixEnd_6957392 := by exact prefixLift 6957392
  have htrace : WordTrace (prefixWord ++ tailWord_6957392) baseStart_6957392 baseEnd_6957392 := by
    simpa [prefixWord, tailWord_6957392, baseEnd_6957392] using wordTrace_append hprefix tailTrace_6957392
  have hstable : (prefixWord ++ tailWord_6957392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957392).length < 2 ^ (prefixWord ++ tailWord_6957392).sum := by decide
  have hdescent : baseEnd_6957392 < baseStart_6957392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957421 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6957421 : Nat := 118140960795 + 6957421 * 2 ^ 59
def prefixEnd_6957421 : Nat := 4983230072969 + 3 ^ 40 * 6957421 * 2
def baseEnd_6957421 : Nat := 3572501088684928792040909

theorem tailTrace_6957421 : CollatzResearch.WordTrace tailWord_6957421 prefixEnd_6957421 3572501088684928792040909 := by
  unfold tailWord_6957421
  simp only [CollatzResearch.WordTrace]
  refine ⟨253757990927459424751856117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169171993951639616501237411 253757990927459424751856117)
  ·
    refine ⟨23789811649449321070486511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253757990927459424751856117 23789811649449321070486511)
    ·
      refine ⟨35684717474173981605729767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23789811649449321070486511 35684717474173981605729767)
      ·
        refine ⟨53527076211260972408594651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35684717474173981605729767 53527076211260972408594651)
        ·
          refine ⟨80290614316891458612891977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53527076211260972408594651 80290614316891458612891977)
          ·
            refine ⟨60217960737668593959668983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80290614316891458612891977 60217960737668593959668983)
            ·
              refine ⟨90326941106502890939503475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60217960737668593959668983 90326941106502890939503475)
              ·
                refine ⟨135490411659754336409255213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90326941106502890939503475 135490411659754336409255213)
                ·
                  refine ⟨50808904372407876153470705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135490411659754336409255213 50808904372407876153470705)
                  ·
                    refine ⟨38106678279305907115103029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50808904372407876153470705 38106678279305907115103029)
                    ·
                      refine ⟨3572501088684928792040909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38106678279305907115103029 3572501088684928792040909)
                      ·
                        rfl

theorem cell23_6957421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6957421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957421 prefixEnd_6957421 := by exact prefixLift 6957421
  have htrace : WordTrace (prefixWord ++ tailWord_6957421) baseStart_6957421 baseEnd_6957421 := by
    simpa [prefixWord, tailWord_6957421, baseEnd_6957421] using wordTrace_append hprefix tailTrace_6957421
  have hstable : (prefixWord ++ tailWord_6957421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957421).length < 2 ^ (prefixWord ++ tailWord_6957421).sum := by decide
  have hdescent : baseEnd_6957421 < baseStart_6957421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957431 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_6957431 : Nat := 118140960795 + 6957431 * 2 ^ 59
def prefixEnd_6957431 : Nat := 4983230072969 + 3 ^ 40 * 6957431 * 2
def baseEnd_6957431 : Nat := 3572506223491473752915863

theorem tailTrace_6957431 : CollatzResearch.WordTrace tailWord_6957431 prefixEnd_6957431 3572506223491473752915863 := by
  unfold tailWord_6957431
  simp only [CollatzResearch.WordTrace]
  refine ⟨253758355657423196459720147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169172237104948797639813431 253758355657423196459720147)
  ·
    refine ⟨380637533486134794689580221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253758355657423196459720147 380637533486134794689580221)
    ·
      refine ⟨142739075057300548008592583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380637533486134794689580221 142739075057300548008592583)
      ·
        refine ⟨214108612585950822012888875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142739075057300548008592583 214108612585950822012888875)
        ·
          refine ⟨321162918878926233019333313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214108612585950822012888875 321162918878926233019333313)
          ·
            refine ⟨240872189159194674764499985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321162918878926233019333313 240872189159194674764499985)
            ·
              refine ⟨180654141869396006073374989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240872189159194674764499985 180654141869396006073374989)
              ·
                refine ⟨67745303201023502277515621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180654141869396006073374989 67745303201023502277515621)
                ·
                  refine ⟨12702244350191906677034179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67745303201023502277515621 12702244350191906677034179)
                  ·
                    refine ⟨19053366525287860015551269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12702244350191906677034179 19053366525287860015551269)
                    ·
                      refine ⟨3572506223491473752915863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19053366525287860015551269 3572506223491473752915863)
                      ·
                        rfl

theorem cell23_6957431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_6957431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957431 prefixEnd_6957431 := by exact prefixLift 6957431
  have htrace : WordTrace (prefixWord ++ tailWord_6957431) baseStart_6957431 baseEnd_6957431 := by
    simpa [prefixWord, tailWord_6957431, baseEnd_6957431] using wordTrace_append hprefix tailTrace_6957431
  have hstable : (prefixWord ++ tailWord_6957431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957431).length < 2 ^ (prefixWord ++ tailWord_6957431).sum := by decide
  have hdescent : baseEnd_6957431 < baseStart_6957431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957442 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6957442 : Nat := 118140960795 + 6957442 * 2 ^ 59
def prefixEnd_6957442 : Nat := 4983230072969 + 3 ^ 40 * 6957442 * 2
def baseEnd_6957442 : Nat := 3572511871778673209878313

theorem tailTrace_6957442 : CollatzResearch.WordTrace tailWord_6957442 prefixEnd_6957442 3572511871778673209878313 := by
  unfold tailWord_6957442
  simp only [CollatzResearch.WordTrace]
  refine ⟨63439689215095836334592645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169172504573588896892247053 63439689215095836334592645)
  ·
    refine ⟨11894941727830469312736121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63439689215095836334592645 11894941727830469312736121)
    ·
      refine ⟨8921206295872851984552091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11894941727830469312736121 8921206295872851984552091)
      ·
        refine ⟨13381809443809277976828137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8921206295872851984552091 13381809443809277976828137)
        ·
          refine ⟨10036357082856958482621103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13381809443809277976828137 10036357082856958482621103)
          ·
            refine ⟨15054535624285437723931655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036357082856958482621103 15054535624285437723931655)
            ·
              refine ⟨22581803436428156585897483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15054535624285437723931655 22581803436428156585897483)
              ·
                refine ⟨33872705154642234878846225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22581803436428156585897483 33872705154642234878846225)
                ·
                  refine ⟨25404528865981676159134669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33872705154642234878846225 25404528865981676159134669)
                  ·
                    refine ⟨9526698324743128559675501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25404528865981676159134669 9526698324743128559675501)
                    ·
                      refine ⟨3572511871778673209878313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526698324743128559675501 3572511871778673209878313)
                      ·
                        rfl

theorem cell23_6957442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6957442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957442 prefixEnd_6957442 := by exact prefixLift 6957442
  have htrace : WordTrace (prefixWord ++ tailWord_6957442) baseStart_6957442 baseEnd_6957442 := by
    simpa [prefixWord, tailWord_6957442, baseEnd_6957442] using wordTrace_append hprefix tailTrace_6957442
  have hstable : (prefixWord ++ tailWord_6957442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957442).length < 2 ^ (prefixWord ++ tailWord_6957442).sum := by decide
  have hdescent : baseEnd_6957442 < baseStart_6957442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957471 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 8]
def baseStart_6957471 : Nat := 118140960795 + 6957471 * 2 ^ 59
def prefixEnd_6957471 : Nat := 4983230072969 + 3 ^ 40 * 6957471 * 2
def baseEnd_6957471 : Nat := 396947418079739288490631

theorem tailTrace_6957471 : CollatzResearch.WordTrace tailWord_6957471 prefixEnd_6957471 396947418079739288490631 := by
  unfold tailWord_6957471
  simp only [CollatzResearch.WordTrace]
  refine ⟨253759814577278283291176267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169173209718185522194117511 253759814577278283291176267)
  ·
    refine ⟨380639721865917424936764401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253759814577278283291176267 380639721865917424936764401)
    ·
      refine ⟨285479791399438068702573301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380639721865917424936764401 285479791399438068702573301)
      ·
        refine ⟨26763730443697318940866247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285479791399438068702573301 26763730443697318940866247)
        ·
          refine ⟨40145595665545978411299371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26763730443697318940866247 40145595665545978411299371)
          ·
            refine ⟨60218393498318967616949057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40145595665545978411299371 60218393498318967616949057)
            ·
              refine ⟨45163795123739225712711793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60218393498318967616949057 45163795123739225712711793)
              ·
                refine ⟨33872846342804419284533845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45163795123739225712711793 33872846342804419284533845)
                ·
                  refine ⟨396947418079739288490631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33872846342804419284533845 396947418079739288490631)
                  ·
                    rfl

theorem cell23_6957471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 8].length) (baseStart_6957471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957471 prefixEnd_6957471 := by exact prefixLift 6957471
  have htrace : WordTrace (prefixWord ++ tailWord_6957471) baseStart_6957471 baseEnd_6957471 := by
    simpa [prefixWord, tailWord_6957471, baseEnd_6957471] using wordTrace_append hprefix tailTrace_6957471
  have hstable : (prefixWord ++ tailWord_6957471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957471).length < 2 ^ (prefixWord ++ tailWord_6957471).sum := by decide
  have hdescent : baseEnd_6957471 < baseStart_6957471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957475 : List Nat := [1, 1, 1, 4, 1, 4, 1, 5, 1, 4]
def baseStart_6957475 : Nat := 118140960795 + 6957475 * 2 ^ 59
def prefixEnd_6957475 : Nat := 4983230072969 + 3 ^ 40 * 6957475 * 2
def baseEnd_6957475 : Nat := 1190842938880090526921887

theorem tailTrace_6957475 : CollatzResearch.WordTrace tailWord_6957475 prefixEnd_6957475 1190842938880090526921887 := by
  unfold tailWord_6957475
  simp only [CollatzResearch.WordTrace]
  refine ⟨253759960469263791974321879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169173306979509194649547919 253759960469263791974321879)
  ·
    refine ⟨380639940703895687961482819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253759960469263791974321879 380639940703895687961482819)
    ·
      refine ⟨570959911055843531942224229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380639940703895687961482819 570959911055843531942224229)
      ·
        refine ⟨107054983322970662239167043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 570959911055843531942224229 107054983322970662239167043)
        ·
          refine ⟨160582474984455993358750565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107054983322970662239167043 160582474984455993358750565)
          ·
            refine ⟨30109214059585498754765731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160582474984455993358750565 30109214059585498754765731)
            ·
              refine ⟨45163821089378248132148597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30109214059585498754765731 45163821089378248132148597)
              ·
                refine ⟨4234108227129210762388931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45163821089378248132148597 4234108227129210762388931)
                ·
                  refine ⟨6351162340693816143583397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234108227129210762388931 6351162340693816143583397)
                  ·
                    refine ⟨1190842938880090526921887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351162340693816143583397 1190842938880090526921887)
                    ·
                      rfl

theorem cell23_6957475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 1, 4].length) (baseStart_6957475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957475 prefixEnd_6957475 := by exact prefixLift 6957475
  have htrace : WordTrace (prefixWord ++ tailWord_6957475) baseStart_6957475 baseEnd_6957475 := by
    simpa [prefixWord, tailWord_6957475, baseEnd_6957475] using wordTrace_append hprefix tailTrace_6957475
  have hstable : (prefixWord ++ tailWord_6957475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957475).length < 2 ^ (prefixWord ++ tailWord_6957475).sum := by decide
  have hdescent : baseEnd_6957475 < baseStart_6957475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957481 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_6957481 : Nat := 118140960795 + 6957481 * 2 ^ 59
def prefixEnd_6957481 : Nat := 4983230072969 + 3 ^ 40 * 6957481 * 2
def baseEnd_6957481 : Nat := 3572531897524198557290633

theorem tailTrace_6957481 : CollatzResearch.WordTrace tailWord_6957481 prefixEnd_6957481 3572531897524198557290633 := by
  unfold tailWord_6957481
  simp only [CollatzResearch.WordTrace]
  refine ⟨253760179307242054999040297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169173452871494703332693531 253760179307242054999040297)
  ·
    refine ⟨190320134480431541249280223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253760179307242054999040297 190320134480431541249280223)
    ·
      refine ⟨285480201720647311873920335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190320134480431541249280223 285480201720647311873920335)
      ·
        refine ⟨428220302580970967810880503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285480201720647311873920335 428220302580970967810880503)
        ·
          refine ⟨642330453871456451716320755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428220302580970967810880503 642330453871456451716320755)
          ·
            refine ⟨963495680807184677574481133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642330453871456451716320755 963495680807184677574481133)
            ·
              refine ⟨361310880302694254090430425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 963495680807184677574481133 361310880302694254090430425)
              ·
                refine ⟨270983160227020690567822819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361310880302694254090430425 270983160227020690567822819)
                ·
                  refine ⟨406474740340531035851734229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270983160227020690567822819 406474740340531035851734229)
                  ·
                    refine ⟨9526751726731196152775021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 406474740340531035851734229 9526751726731196152775021)
                    ·
                      refine ⟨3572531897524198557290633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526751726731196152775021 3572531897524198557290633)
                      ·
                        rfl

theorem cell23_6957481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_6957481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957481 prefixEnd_6957481 := by exact prefixLift 6957481
  have htrace : WordTrace (prefixWord ++ tailWord_6957481) baseStart_6957481 baseEnd_6957481 := by
    simpa [prefixWord, tailWord_6957481, baseEnd_6957481] using wordTrace_append hprefix tailTrace_6957481
  have hstable : (prefixWord ++ tailWord_6957481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957481).length < 2 ^ (prefixWord ++ tailWord_6957481).sum := by decide
  have hdescent : baseEnd_6957481 < baseStart_6957481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957521 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_6957521 : Nat := 118140960795 + 6957521 * 2 ^ 59
def prefixEnd_6957521 : Nat := 4983230072969 + 3 ^ 40 * 6957521 * 2
def baseEnd_6957521 : Nat := 3572552436750378400790449

theorem tailTrace_6957521 : CollatzResearch.WordTrace tailWord_6957521 prefixEnd_6957521 3572552436750378400790449 := by
  unfold tailWord_6957521
  simp only [CollatzResearch.WordTrace]
  refine ⟨253761638227097141830496417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169174425484731427886997611 253761638227097141830496417)
  ·
    refine ⟨190321228670322856372872313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253761638227097141830496417 190321228670322856372872313)
    ·
      refine ⟨142740921502742142279654235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190321228670322856372872313 142740921502742142279654235)
      ·
        refine ⟨214111382254113213419481353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142740921502742142279654235 214111382254113213419481353)
        ·
          refine ⟨160583536690584910064611015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214111382254113213419481353 160583536690584910064611015)
          ·
            refine ⟨240875305035877365096916523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160583536690584910064611015 240875305035877365096916523)
            ·
              refine ⟨361312957553816047645374785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240875305035877365096916523 361312957553816047645374785)
              ·
                refine ⟨270984718165362035734031089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361312957553816047645374785 270984718165362035734031089)
                ·
                  refine ⟨203238538624021526800523317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270984718165362035734031089 203238538624021526800523317)
                  ·
                    refine ⟨19053612996002018137549061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203238538624021526800523317 19053612996002018137549061)
                    ·
                      refine ⟨3572552436750378400790449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19053612996002018137549061 3572552436750378400790449)
                      ·
                        rfl

theorem cell23_6957521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_6957521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957521 prefixEnd_6957521 := by exact prefixLift 6957521
  have htrace : WordTrace (prefixWord ++ tailWord_6957521) baseStart_6957521 baseEnd_6957521 := by
    simpa [prefixWord, tailWord_6957521, baseEnd_6957521] using wordTrace_append hprefix tailTrace_6957521
  have hstable : (prefixWord ++ tailWord_6957521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957521).length < 2 ^ (prefixWord ++ tailWord_6957521).sum := by decide
  have hdescent : baseEnd_6957521 < baseStart_6957521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957525 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6957525 : Nat := 118140960795 + 6957525 * 2 ^ 59
def prefixEnd_6957525 : Nat := 4983230072969 + 3 ^ 40 * 6957525 * 2
def baseEnd_6957525 : Nat := 3572554490672996385140431

theorem tailTrace_6957525 : CollatzResearch.WordTrace tailWord_6957525 prefixEnd_6957525 3572554490672996385140431 := by
  unfold tailWord_6957525
  simp only [CollatzResearch.WordTrace]
  refine ⟨253761784119082650513642029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169174522746055100342428019 253761784119082650513642029)
  ·
    refine ⟨95160669044655993942615761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253761784119082650513642029 95160669044655993942615761)
    ·
      refine ⟨71370501783491995456961821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95160669044655993942615761 71370501783491995456961821)
      ·
        refine ⟨26763938168809498296360683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71370501783491995456961821 26763938168809498296360683)
        ·
          refine ⟨40145907253214247444541025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26763938168809498296360683 40145907253214247444541025)
          ·
            refine ⟨30109430439910685583405769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40145907253214247444541025 30109430439910685583405769)
            ·
              refine ⟨22582072829933014187554327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30109430439910685583405769 22582072829933014187554327)
              ·
                refine ⟨33873109244899521281331491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22582072829933014187554327 33873109244899521281331491)
                ·
                  refine ⟨50809663867349281921997237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33873109244899521281331491 50809663867349281921997237)
                  ·
                    refine ⟨4763405987563995180187241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50809663867349281921997237 4763405987563995180187241)
                    ·
                      refine ⟨3572554490672996385140431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763405987563995180187241 3572554490672996385140431)
                      ·
                        rfl

theorem cell23_6957525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6957525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957525 prefixEnd_6957525 := by exact prefixLift 6957525
  have htrace : WordTrace (prefixWord ++ tailWord_6957525) baseStart_6957525 baseEnd_6957525 := by
    simpa [prefixWord, tailWord_6957525, baseEnd_6957525] using wordTrace_append hprefix tailTrace_6957525
  have hstable : (prefixWord ++ tailWord_6957525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957525).length < 2 ^ (prefixWord ++ tailWord_6957525).sum := by decide
  have hdescent : baseEnd_6957525 < baseStart_6957525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957548 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_6957548 : Nat := 118140960795 + 6957548 * 2 ^ 59
def prefixEnd_6957548 : Nat := 4983230072969 + 3 ^ 40 * 6957548 * 2
def baseEnd_6957548 : Nat := 1190855433576016598384275

theorem tailTrace_6957548 : CollatzResearch.WordTrace tailWord_6957548 prefixEnd_6957548 1190855433576016598384275 := by
  unfold tailWord_6957548
  simp only [CollatzResearch.WordTrace]
  refine ⟨126881311498999662720864649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169175081998666216961152865 126881311498999662720864649)
  ·
    refine ⟨95160983624249747040648487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126881311498999662720864649 95160983624249747040648487)
    ·
      refine ⟨142741475436374620560972731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95160983624249747040648487 142741475436374620560972731)
      ·
        refine ⟨214112213154561930841459097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142741475436374620560972731 214112213154561930841459097)
        ·
          refine ⟨160584159865921448131094323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214112213154561930841459097 160584159865921448131094323)
          ·
            refine ⟨240876239798882172196641485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160584159865921448131094323 240876239798882172196641485)
            ·
              refine ⟨90328589924580814573740557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240876239798882172196641485 90328589924580814573740557)
              ·
                refine ⟨33873221221717805465152709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90328589924580814573740557 33873221221717805465152709)
                ·
                  refine ⟨6351228979072088524716133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33873221221717805465152709 6351228979072088524716133)
                  ·
                    refine ⟨1190855433576016598384275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351228979072088524716133 1190855433576016598384275)
                    ·
                      rfl

theorem cell23_6957548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_6957548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957548 prefixEnd_6957548 := by exact prefixLift 6957548
  have htrace : WordTrace (prefixWord ++ tailWord_6957548) baseStart_6957548 baseEnd_6957548 := by
    simpa [prefixWord, tailWord_6957548, baseEnd_6957548] using wordTrace_append hprefix tailTrace_6957548
  have hstable : (prefixWord ++ tailWord_6957548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957548).length < 2 ^ (prefixWord ++ tailWord_6957548).sum := by decide
  have hdescent : baseEnd_6957548 < baseStart_6957548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957549 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6957549 : Nat := 118140960795 + 6957549 * 2 ^ 59
def prefixEnd_6957549 : Nat := 4983230072969 + 3 ^ 40 * 6957549 * 2
def baseEnd_6957549 : Nat := 3572566814208704291240321

theorem tailTrace_6957549 : CollatzResearch.WordTrace tailWord_6957549 prefixEnd_6957549 3572566814208704291240321 := by
  unfold tailWord_6957549
  simp only [CollatzResearch.WordTrace]
  refine ⟨253762659470995702612515701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169175106313997135075010467 253762659470995702612515701)
  ·
    refine ⟨23790249325405847119923347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253762659470995702612515701 23790249325405847119923347)
    ·
      refine ⟨35685373988108770679885021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23790249325405847119923347 35685373988108770679885021)
      ·
        refine ⟨13382015245540789004956883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35685373988108770679885021 13382015245540789004956883)
        ·
          refine ⟨20073022868311183507435325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13382015245540789004956883 20073022868311183507435325)
          ·
            refine ⟨7527383575616693815288247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20073022868311183507435325 7527383575616693815288247)
            ·
              refine ⟨11291075363425040722932371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527383575616693815288247 11291075363425040722932371)
              ·
                refine ⟨16936613045137561084398557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11291075363425040722932371 16936613045137561084398557)
                ·
                  refine ⟨6351229891926585406649459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16936613045137561084398557 6351229891926585406649459)
                  ·
                    refine ⟨9526844837889878109974189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351229891926585406649459 9526844837889878109974189)
                    ·
                      refine ⟨3572566814208704291240321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526844837889878109974189 3572566814208704291240321)
                      ·
                        rfl

theorem cell23_6957549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6957549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957549 prefixEnd_6957549 := by exact prefixLift 6957549
  have htrace : WordTrace (prefixWord ++ tailWord_6957549) baseStart_6957549 baseEnd_6957549 := by
    simpa [prefixWord, tailWord_6957549, baseEnd_6957549] using wordTrace_append hprefix tailTrace_6957549
  have hstable : (prefixWord ++ tailWord_6957549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957549).length < 2 ^ (prefixWord ++ tailWord_6957549).sum := by decide
  have hdescent : baseEnd_6957549 < baseStart_6957549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957561 : List Nat := [1, 2, 1, 3, 1, 2, 3, 10]
def baseStart_6957561 : Nat := 118140960795 + 6957561 * 2 ^ 59
def prefixEnd_6957561 : Nat := 4983230072969 + 3 ^ 40 * 6957561 * 2
def baseEnd_6957561 : Nat := 132317517628761416455195

theorem tailTrace_6957561 : CollatzResearch.WordTrace tailWord_6957561 prefixEnd_6957561 132317517628761416455195 := by
  unfold tailWord_6957561
  simp only [CollatzResearch.WordTrace]
  refine ⟨253763097146952228661952537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169175398097968152441301691 253763097146952228661952537)
  ·
    refine ⟨190322322860214171496464403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253763097146952228661952537 190322322860214171496464403)
    ·
      refine ⟨285483484290321257244696605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190322322860214171496464403 285483484290321257244696605)
      ·
        refine ⟨107056306608870471466761227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285483484290321257244696605 107056306608870471466761227)
        ·
          refine ⟨160584459913305707200141841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107056306608870471466761227 160584459913305707200141841)
          ·
            refine ⟨120438344934979280400106381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160584459913305707200141841 120438344934979280400106381)
            ·
              refine ⟨45164379350617230150039893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120438344934979280400106381 45164379350617230150039893)
              ·
                refine ⟨132317517628761416455195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45164379350617230150039893 132317517628761416455195)
                ·
                  rfl

theorem cell23_6957561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 10].length) (baseStart_6957561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957561 prefixEnd_6957561 := by exact prefixLift 6957561
  have htrace : WordTrace (prefixWord ++ tailWord_6957561) baseStart_6957561 baseEnd_6957561 := by
    simpa [prefixWord, tailWord_6957561, baseEnd_6957561] using wordTrace_append hprefix tailTrace_6957561
  have hstable : (prefixWord ++ tailWord_6957561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957561).length < 2 ^ (prefixWord ++ tailWord_6957561).sum := by decide
  have hdescent : baseEnd_6957561 < baseStart_6957561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957565 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_6957565 : Nat := 118140960795 + 6957565 * 2 ^ 59
def prefixEnd_6957565 : Nat := 4983230072969 + 3 ^ 40 * 6957565 * 2
def baseEnd_6957565 : Nat := 1190858343299725409546749

theorem tailTrace_6957565 : CollatzResearch.WordTrace tailWord_6957565 prefixEnd_6957565 1190858343299725409546749 := by
  unfold tailWord_6957565
  simp only [CollatzResearch.WordTrace]
  refine ⟨253763243038937737345098149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169175495359291824896732099 253763243038937737345098149)
  ·
    refine ⟨47580608069800825752205903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253763243038937737345098149 47580608069800825752205903)
    ·
      refine ⟨71370912104701238628308855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47580608069800825752205903 71370912104701238628308855)
      ·
        refine ⟨107056368157051857942463283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71370912104701238628308855 107056368157051857942463283)
        ·
          refine ⟨160584552235577786913694925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107056368157051857942463283 160584552235577786913694925)
          ·
            refine ⟨60219207088341670092635597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160584552235577786913694925 60219207088341670092635597)
            ·
              refine ⟨22582202658128126284738349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60219207088341670092635597 22582202658128126284738349)
              ·
                refine ⟨8468325996798047356776881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22582202658128126284738349 8468325996798047356776881)
                ·
                  refine ⟨6351244497598535517582661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8468325996798047356776881 6351244497598535517582661)
                  ·
                    refine ⟨1190858343299725409546749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351244497598535517582661 1190858343299725409546749)
                    ·
                      rfl

theorem cell23_6957565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_6957565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957565 prefixEnd_6957565 := by exact prefixLift 6957565
  have htrace : WordTrace (prefixWord ++ tailWord_6957565) baseStart_6957565 baseEnd_6957565 := by
    simpa [prefixWord, tailWord_6957565, baseEnd_6957565] using wordTrace_append hprefix tailTrace_6957565
  have hstable : (prefixWord ++ tailWord_6957565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957565).length < 2 ^ (prefixWord ++ tailWord_6957565).sum := by decide
  have hdescent : baseEnd_6957565 < baseStart_6957565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957572 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6957572 : Nat := 118140960795 + 6957572 * 2 ^ 59
def prefixEnd_6957572 : Nat := 4983230072969 + 3 ^ 40 * 6957572 * 2
def baseEnd_6957572 : Nat := 3572578624263757701252715

theorem tailTrace_6957572 : CollatzResearch.WordTrace tailWord_6957572 prefixEnd_6957572 3572578624263757701252715 := by
  unfold tailWord_6957572
  simp only [CollatzResearch.WordTrace]
  refine ⟨126881749174956188770301485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169175665566608251693735313 126881749174956188770301485)
  ·
    refine ⟨47580655940608570788863057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126881749174956188770301485 47580655940608570788863057)
    ·
      refine ⟨35685491955456428091647293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47580655940608570788863057 35685491955456428091647293)
      ·
        refine ⟨13382059483296160534367735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35685491955456428091647293 13382059483296160534367735)
        ·
          refine ⟨20073089224944240801551603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13382059483296160534367735 20073089224944240801551603)
          ·
            refine ⟨30109633837416361202327405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20073089224944240801551603 30109633837416361202327405)
            ·
              refine ⟨11291112689031135450872777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30109633837416361202327405 11291112689031135450872777)
              ·
                refine ⟨8468334516773351588154583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11291112689031135450872777 8468334516773351588154583)
                ·
                  refine ⟨12702501775160027382231875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8468334516773351588154583 12702501775160027382231875)
                  ·
                    refine ⟨19053752662740041073347813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12702501775160027382231875 19053752662740041073347813)
                    ·
                      refine ⟨3572578624263757701252715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19053752662740041073347813 3572578624263757701252715)
                      ·
                        rfl

theorem cell23_6957572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6957572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957572 prefixEnd_6957572 := by exact prefixLift 6957572
  have htrace : WordTrace (prefixWord ++ tailWord_6957572) baseStart_6957572 baseEnd_6957572 := by
    simpa [prefixWord, tailWord_6957572, baseEnd_6957572] using wordTrace_append hprefix tailTrace_6957572
  have hstable : (prefixWord ++ tailWord_6957572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957572).length < 2 ^ (prefixWord ++ tailWord_6957572).sum := by decide
  have hdescent : baseEnd_6957572 < baseStart_6957572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957589 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_6957589 : Nat := 118140960795 + 6957589 * 2 ^ 59
def prefixEnd_6957589 : Nat := 4983230072969 + 3 ^ 40 * 6957589 * 2
def baseEnd_6957589 : Nat := 3572587353434884134740137

theorem tailTrace_6957589 : CollatzResearch.WordTrace tailWord_6957589 prefixEnd_6957589 3572587353434884134740137 := by
  unfold tailWord_6957589
  simp only [CollatzResearch.WordTrace]
  refine ⟨253764118390850789443971821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169176078927233859629314547 253764118390850789443971821)
  ·
    refine ⟨95161544396569046041489433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253764118390850789443971821 95161544396569046041489433)
    ·
      refine ⟨71371158297426784531117075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95161544396569046041489433 71371158297426784531117075)
      ·
        refine ⟨107056737446140176796675613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71371158297426784531117075 107056737446140176796675613)
        ·
          refine ⟨40146276542302566298753355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107056737446140176796675613 40146276542302566298753355)
          ·
            refine ⟨60219414813453849448130033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40146276542302566298753355 60219414813453849448130033)
            ·
              refine ⟨45164561110090387086097525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60219414813453849448130033 45164561110090387086097525)
              ·
                refine ⟨4234177604070973789321643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45164561110090387086097525 4234177604070973789321643)
                ·
                  refine ⟨6351266406106460683982465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234177604070973789321643 6351266406106460683982465)
                  ·
                    refine ⟨4763449804579845512986849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351266406106460683982465 4763449804579845512986849)
                    ·
                      refine ⟨3572587353434884134740137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763449804579845512986849 3572587353434884134740137)
                      ·
                        rfl

theorem cell23_6957589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_6957589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957589 prefixEnd_6957589 := by exact prefixLift 6957589
  have htrace : WordTrace (prefixWord ++ tailWord_6957589) baseStart_6957589 baseEnd_6957589 := by
    simpa [prefixWord, tailWord_6957589, baseEnd_6957589] using wordTrace_append hprefix tailTrace_6957589
  have hstable : (prefixWord ++ tailWord_6957589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957589).length < 2 ^ (prefixWord ++ tailWord_6957589).sum := by decide
  have hdescent : baseEnd_6957589 < baseStart_6957589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957605 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_6957605 : Nat := 118140960795 + 6957605 * 2 ^ 59
def prefixEnd_6957605 : Nat := 4983230072969 + 3 ^ 40 * 6957605 * 2
def baseEnd_6957605 : Nat := 3572595569125356072140063

theorem tailTrace_6957605 : CollatzResearch.WordTrace tailWord_6957605 prefixEnd_6957605 3572595569125356072140063 := by
  unfold tailWord_6957605
  simp only [CollatzResearch.WordTrace]
  refine ⟨253764701958792824176554269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169176467972528549451036179 253764701958792824176554269)
  ·
    refine ⟨95161763234547309066207851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253764701958792824176554269 95161763234547309066207851)
    ·
      refine ⟨142742644851820963599311777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95161763234547309066207851 142742644851820963599311777)
      ·
        refine ⟨107056983638865722699483833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142742644851820963599311777 107056983638865722699483833)
        ·
          refine ⟨80292737729149292024612875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107056983638865722699483833 80292737729149292024612875)
          ·
            refine ⟨120439106593723938036919313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80292737729149292024612875 120439106593723938036919313)
            ·
              refine ⟨90329329945292953527689485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120439106593723938036919313 90329329945292953527689485)
              ·
                refine ⟨33873498729484857572883557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90329329945292953527689485 33873498729484857572883557)
                ·
                  refine ⟨6351281011778410794915667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33873498729484857572883557 6351281011778410794915667)
                  ·
                    refine ⟨9526921517667616192373501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351281011778410794915667 9526921517667616192373501)
                    ·
                      refine ⟨3572595569125356072140063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526921517667616192373501 3572595569125356072140063)
                      ·
                        rfl

theorem cell23_6957605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_6957605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957605 prefixEnd_6957605 := by exact prefixLift 6957605
  have htrace : WordTrace (prefixWord ++ tailWord_6957605) baseStart_6957605 baseEnd_6957605 := by
    simpa [prefixWord, tailWord_6957605, baseEnd_6957605] using wordTrace_append hprefix tailTrace_6957605
  have hstable : (prefixWord ++ tailWord_6957605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957605).length < 2 ^ (prefixWord ++ tailWord_6957605).sum := by decide
  have hdescent : baseEnd_6957605 < baseStart_6957605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957622 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_6957622 : Nat := 118140960795 + 6957622 * 2 ^ 59
def prefixEnd_6957622 : Nat := 4983230072969 + 3 ^ 40 * 6957622 * 2
def baseEnd_6957622 : Nat := 3572604298296482505627485

theorem tailTrace_6957622 : CollatzResearch.WordTrace tailWord_6957622 prefixEnd_6957622 3572604298296482505627485 := by
  unfold tailWord_6957622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860332624983202254995195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169176881333154157386615413 15860332624983202254995195)
  ·
    refine ⟨23790498937474803382492793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15860332624983202254995195 23790498937474803382492793)
    ·
      refine ⟨17842874203106102536869595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23790498937474803382492793 17842874203106102536869595)
      ·
        refine ⟨26764311304659153805304393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17842874203106102536869595 26764311304659153805304393)
        ·
          refine ⟨20073233478494365353978295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26764311304659153805304393 20073233478494365353978295)
          ·
            refine ⟨30109850217741548030967443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20073233478494365353978295 30109850217741548030967443)
            ·
              refine ⟨45164775326612322046451165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30109850217741548030967443 45164775326612322046451165)
              ·
                refine ⟨16936790747479620767419187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45164775326612322046451165 16936790747479620767419187)
                ·
                  refine ⟨25405186121219431151128781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16936790747479620767419187 25405186121219431151128781)
                  ·
                    refine ⟨9526944795457286681673293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25405186121219431151128781 9526944795457286681673293)
                    ·
                      refine ⟨3572604298296482505627485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526944795457286681673293 3572604298296482505627485)
                      ·
                        rfl

theorem cell23_6957622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_6957622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957622 prefixEnd_6957622 := by exact prefixLift 6957622
  have htrace : WordTrace (prefixWord ++ tailWord_6957622) baseStart_6957622 baseEnd_6957622 := by
    simpa [prefixWord, tailWord_6957622, baseEnd_6957622] using wordTrace_append hprefix tailTrace_6957622
  have hstable : (prefixWord ++ tailWord_6957622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957622).length < 2 ^ (prefixWord ++ tailWord_6957622).sum := by decide
  have hdescent : baseEnd_6957622 < baseStart_6957622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957648 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3]
def baseStart_6957648 : Nat := 118140960795 + 6957648 * 2 ^ 59
def prefixEnd_6957648 : Nat := 4983230072969 + 3 ^ 40 * 6957648 * 2
def baseEnd_6957648 : Nat := 3572617648793499403902365

theorem tailTrace_6957648 : CollatzResearch.WordTrace tailWord_6957648 prefixEnd_6957648 3572617648793499403902365 := by
  unfold tailWord_6957648
  simp only [CollatzResearch.WordTrace]
  refine ⟨126883135148818521260184799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169177513531758028346913065 126883135148818521260184799)
  ·
    refine ⟨190324702723227781890277199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126883135148818521260184799 190324702723227781890277199)
    ·
      refine ⟨285487054084841672835415799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190324702723227781890277199 285487054084841672835415799)
      ·
        refine ⟨428230581127262509253123699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285487054084841672835415799 428230581127262509253123699)
        ·
          refine ⟨642345871690893763879685549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428230581127262509253123699 642345871690893763879685549)
          ·
            refine ⟨240879701884085161454882081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642345871690893763879685549 240879701884085161454882081)
            ·
              refine ⟨180659776413063871091161561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240879701884085161454882081 180659776413063871091161561)
              ·
                refine ⟨135494832309797903318371171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180659776413063871091161561 135494832309797903318371171)
                ·
                  refine ⟨203242248464696854977556757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135494832309797903318371171 203242248464696854977556757)
                  ·
                    refine ⟨9526980396782665077072973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 203242248464696854977556757 9526980396782665077072973)
                    ·
                      refine ⟨3572617648793499403902365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9526980396782665077072973 3572617648793499403902365)
                      ·
                        rfl

theorem cell23_6957648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_6957648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957648 prefixEnd_6957648 := by exact prefixLift 6957648
  have htrace : WordTrace (prefixWord ++ tailWord_6957648) baseStart_6957648 baseEnd_6957648 := by
    simpa [prefixWord, tailWord_6957648, baseEnd_6957648] using wordTrace_append hprefix tailTrace_6957648
  have hstable : (prefixWord ++ tailWord_6957648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957648).length < 2 ^ (prefixWord ++ tailWord_6957648).sum := by decide
  have hdescent : baseEnd_6957648 < baseStart_6957648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957649 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 1, 3, 2]
def baseStart_6957649 : Nat := 118140960795 + 6957649 * 2 ^ 59
def prefixEnd_6957649 : Nat := 4983230072969 + 3 ^ 40 * 6957649 * 2
def baseEnd_6957649 : Nat := 3572618162274153899989861

theorem tailTrace_6957649 : CollatzResearch.WordTrace tailWord_6957649 prefixEnd_6957649 3572618162274153899989861 := by
  unfold tailWord_6957649
  simp only [CollatzResearch.WordTrace]
  refine ⟨253766306770633419691156001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169177537847088946460770667 253766306770633419691156001)
  ·
    refine ⟨190324730077975064768367001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253766306770633419691156001 190324730077975064768367001)
    ·
      refine ⟨142743547558481298576275251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190324730077975064768367001 142743547558481298576275251)
      ·
        refine ⟨214115321337721947864412877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142743547558481298576275251 214115321337721947864412877)
        ·
          refine ⟨80293245501645730449154829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214115321337721947864412877 80293245501645730449154829)
          ·
            refine ⟨30109967063117148918433061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80293245501645730449154829 30109967063117148918433061)
            ·
              refine ⟨5645618824334465422206199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30109967063117148918433061 5645618824334465422206199)
              ·
                refine ⟨8468428236501698133309299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645618824334465422206199 8468428236501698133309299)
                ·
                  refine ⟨12702642354752547199963949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8468428236501698133309299 12702642354752547199963949)
                  ·
                    refine ⟨4763490883032205199986481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12702642354752547199963949 4763490883032205199986481)
                    ·
                      refine ⟨3572618162274153899989861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763490883032205199986481 3572618162274153899989861)
                      ·
                        rfl

theorem cell23_6957649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_6957649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957649 prefixEnd_6957649 := by exact prefixLift 6957649
  have htrace : WordTrace (prefixWord ++ tailWord_6957649) baseStart_6957649 baseEnd_6957649 := by
    simpa [prefixWord, tailWord_6957649, baseEnd_6957649] using wordTrace_append hprefix tailTrace_6957649
  have hstable : (prefixWord ++ tailWord_6957649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957649).length < 2 ^ (prefixWord ++ tailWord_6957649).sum := by decide
  have hdescent : baseEnd_6957649 < baseStart_6957649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957705 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 7, 2]
def baseStart_6957705 : Nat := 118140960795 + 6957705 * 2 ^ 59
def prefixEnd_6957705 : Nat := 4983230072969 + 3 ^ 40 * 6957705 * 2
def baseEnd_6957705 : Nat := 3572646917190805680889603

theorem tailTrace_6957705 : CollatzResearch.WordTrace tailWord_6957705 prefixEnd_6957705 3572646917190805680889603 := by
  unfold tailWord_6957705
  simp only [CollatzResearch.WordTrace]
  refine ⟨253768349258430541255194569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169178899505620360836796379 253768349258430541255194569)
  ·
    refine ⟨190326261943822905941395927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253768349258430541255194569 190326261943822905941395927)
    ·
      refine ⟨285489392915734358912093891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190326261943822905941395927 285489392915734358912093891)
      ·
        refine ⟨428234089373601538368140837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285489392915734358912093891 428234089373601538368140837)
        ·
          refine ⟨80293891757550288444026407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428234089373601538368140837 80293891757550288444026407)
          ·
            refine ⟨120440837636325432666039611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80293891757550288444026407 120440837636325432666039611)
            ·
              refine ⟨180661256454488148999059417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120440837636325432666039611 180661256454488148999059417)
              ·
                refine ⟨135495942340866111749294563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180661256454488148999059417 135495942340866111749294563)
                ·
                  refine ⟨203243913511299167623941845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135495942340866111749294563 203243913511299167623941845)
                  ·
                    refine ⟨4763529222921074241186137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 203243913511299167623941845 4763529222921074241186137)
                    ·
                      refine ⟨3572646917190805680889603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763529222921074241186137 3572646917190805680889603)
                      ·
                        rfl

theorem cell23_6957705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 7, 2].length) (baseStart_6957705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957705 prefixEnd_6957705 := by exact prefixLift 6957705
  have htrace : WordTrace (prefixWord ++ tailWord_6957705) baseStart_6957705 baseEnd_6957705 := by
    simpa [prefixWord, tailWord_6957705, baseEnd_6957705] using wordTrace_append hprefix tailTrace_6957705
  have hstable : (prefixWord ++ tailWord_6957705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957705).length < 2 ^ (prefixWord ++ tailWord_6957705).sum := by decide
  have hdescent : baseEnd_6957705 < baseStart_6957705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957852 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6957852 : Nat := 118140960795 + 6957852 * 2 ^ 59
def prefixEnd_6957852 : Nat := 4983230072969 + 3 ^ 40 * 6957852 * 2
def baseEnd_6957852 : Nat := 1190907466282338868583809

theorem tailTrace_6957852 : CollatzResearch.WordTrace tailWord_6957852 prefixEnd_6957852 1190907466282338868583809 := by
  unfold tailWord_6957852
  simp only [CollatzResearch.WordTrace]
  refine ⟨126886855394448992680397905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169182473859265323573863873 126886855394448992680397905)
  ·
    refine ⟨95165141545836744510298429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126886855394448992680397905 95165141545836744510298429)
    ·
      refine ⟨35686928079688779191361911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95165141545836744510298429 35686928079688779191361911)
      ·
        refine ⟨53530392119533168787042867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35686928079688779191361911 53530392119533168787042867)
        ·
          refine ⟨80295588179299753180564301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53530392119533168787042867 80295588179299753180564301)
          ·
            refine ⟨30110845567237407442711613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80295588179299753180564301 30110845567237407442711613)
            ·
              refine ⟨11291567087714027791016855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30110845567237407442711613 11291567087714027791016855)
              ·
                refine ⟨16937350631571041686525283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11291567087714027791016855 16937350631571041686525283)
                ·
                  refine ⟨25406025947356562529787925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16937350631571041686525283 25406025947356562529787925)
                  ·
                    refine ⟨1190907466282338868583809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25406025947356562529787925 1190907466282338868583809)
                    ·
                      rfl

theorem cell23_6957852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6957852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957852 prefixEnd_6957852 := by exact prefixLift 6957852
  have htrace : WordTrace (prefixWord ++ tailWord_6957852) baseStart_6957852 baseEnd_6957852 := by
    simpa [prefixWord, tailWord_6957852, baseEnd_6957852] using wordTrace_append hprefix tailTrace_6957852
  have hstable : (prefixWord ++ tailWord_6957852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957852).length < 2 ^ (prefixWord ++ tailWord_6957852).sum := by decide
  have hdescent : baseEnd_6957852 < baseStart_6957852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957870 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6957870 : Nat := 118140960795 + 6957870 * 2 ^ 59
def prefixEnd_6957870 : Nat := 4983230072969 + 3 ^ 40 * 6957870 * 2
def baseEnd_6957870 : Nat := 3572731641498797535326345

theorem tailTrace_6957870 : CollatzResearch.WordTrace tailWord_6957870 prefixEnd_6957870 3572731641498797535326345 := by
  unfold tailWord_6957870
  simp only [CollatzResearch.WordTrace]
  refine ⟨31721795912854096804368883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169182911535221849623300709 31721795912854096804368883)
  ·
    refine ⟨47582693869281145206553325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31721795912854096804368883 47582693869281145206553325)
    ·
      refine ⟨17843510200980429452457497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47582693869281145206553325 17843510200980429452457497)
      ·
        refine ⟨13382632650735322089343123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17843510200980429452457497 13382632650735322089343123)
        ·
          refine ⟨20073948976102983134014685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13382632650735322089343123 20073948976102983134014685)
          ·
            refine ⟨7527730866038618675255507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20073948976102983134014685 7527730866038618675255507)
            ·
              refine ⟨11291596299057928012883261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7527730866038618675255507 11291596299057928012883261)
              ·
                refine ⟨4234348612146723004831223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11291596299057928012883261 4234348612146723004831223)
                ·
                  refine ⟨6351522918220084507246835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234348612146723004831223 6351522918220084507246835)
                  ·
                    refine ⟨9527284377330126760870253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351522918220084507246835 9527284377330126760870253)
                    ·
                      refine ⟨3572731641498797535326345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9527284377330126760870253 3572731641498797535326345)
                      ·
                        rfl

theorem cell23_6957870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6957870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957870 prefixEnd_6957870 := by exact prefixLift 6957870
  have htrace : WordTrace (prefixWord ++ tailWord_6957870) baseStart_6957870 baseEnd_6957870 := by
    simpa [prefixWord, tailWord_6957870, baseEnd_6957870] using wordTrace_append hprefix tailTrace_6957870
  have hstable : (prefixWord ++ tailWord_6957870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957870).length < 2 ^ (prefixWord ++ tailWord_6957870).sum := by decide
  have hdescent : baseEnd_6957870 < baseStart_6957870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957882 : List Nat := [3, 1, 1, 1, 6, 2, 9]
def baseStart_6957882 : Nat := 118140960795 + 6957882 * 2 ^ 59
def prefixEnd_6957882 : Nat := 4983230072969 + 3 ^ 40 * 6957882 * 2
def baseEnd_6957882 : Nat := 44107874114403104794769

theorem tailTrace_6957882 : CollatzResearch.WordTrace tailWord_6957882 prefixEnd_6957882 44107874114403104794769 := by
  unfold tailWord_6957882
  simp only [CollatzResearch.WordTrace]
  refine ⟨63443701244697325121096975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169183203319192866989591933 63443701244697325121096975)
  ·
    refine ⟨95165551867045987681645463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63443701244697325121096975 95165551867045987681645463)
    ·
      refine ⟨142748327800568981522468195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95165551867045987681645463 142748327800568981522468195)
      ·
        refine ⟨214122491700853472283702293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142748327800568981522468195 214122491700853472283702293)
        ·
          refine ⟨10036991798477506513298545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214122491700853472283702293 10036991798477506513298545)
          ·
            refine ⟨7527743848858129884973909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10036991798477506513298545 7527743848858129884973909)
            ·
              refine ⟨44107874114403104794769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7527743848858129884973909 44107874114403104794769)
              ·
                rfl

theorem cell23_6957882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 9].length) (baseStart_6957882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957882 prefixEnd_6957882 := by exact prefixLift 6957882
  have htrace : WordTrace (prefixWord ++ tailWord_6957882) baseStart_6957882 baseEnd_6957882 := by
    simpa [prefixWord, tailWord_6957882, baseEnd_6957882] using wordTrace_append hprefix tailTrace_6957882
  have hstable : (prefixWord ++ tailWord_6957882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957882).length < 2 ^ (prefixWord ++ tailWord_6957882).sum := by decide
  have hdescent : baseEnd_6957882 < baseStart_6957882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957895 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 2, 7]
def baseStart_6957895 : Nat := 118140960795 + 6957895 * 2 ^ 59
def prefixEnd_6957895 : Nat := 4983230072969 + 3 ^ 40 * 6957895 * 2
def baseEnd_6957895 : Nat := 1190914826171719979171243

theorem tailTrace_6957895 : CollatzResearch.WordTrace tailWord_6957895 prefixEnd_6957895 1190914826171719979171243 := by
  unfold tailWord_6957895
  simp only [CollatzResearch.WordTrace]
  refine ⟨253775279127742203704611139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169183519418494802469740759 253775279127742203704611139)
  ·
    refine ⟨380662918691613305556916709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253775279127742203704611139 380662918691613305556916709)
    ·
      refine ⟨71374297254677494791921883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380662918691613305556916709 71374297254677494791921883)
      ·
        refine ⟨107061445882016242187882825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71374297254677494791921883 107061445882016242187882825)
        ·
          refine ⟨80296084411512181640912119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107061445882016242187882825 80296084411512181640912119)
          ·
            refine ⟨120444126617268272461368179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80296084411512181640912119 120444126617268272461368179)
            ·
              refine ⟨180666189925902408692052269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120444126617268272461368179 180666189925902408692052269)
              ·
                refine ⟨67749821222213403259519601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180666189925902408692052269 67749821222213403259519601)
                ·
                  refine ⟨50812365916660052444639701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67749821222213403259519601 50812365916660052444639701)
                  ·
                    refine ⟨1190914826171719979171243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50812365916660052444639701 1190914826171719979171243)
                    ·
                      rfl

theorem cell23_6957895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_6957895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957895 prefixEnd_6957895 := by exact prefixLift 6957895
  have htrace : WordTrace (prefixWord ++ tailWord_6957895) baseStart_6957895 baseEnd_6957895 := by
    simpa [prefixWord, tailWord_6957895, baseEnd_6957895] using wordTrace_append hprefix tailTrace_6957895
  have hstable : (prefixWord ++ tailWord_6957895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957895).length < 2 ^ (prefixWord ++ tailWord_6957895).sum := by decide
  have hdescent : baseEnd_6957895 < baseStart_6957895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6957919 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 3, 3, 2]
def baseStart_6957919 : Nat := 118140960795 + 6957919 * 2 ^ 59
def prefixEnd_6957919 : Nat := 4983230072969 + 3 ^ 40 * 6957919 * 2
def baseEnd_6957919 : Nat := 3572756802050867843613619

theorem tailTrace_6957919 : CollatzResearch.WordTrace tailWord_6957919 prefixEnd_6957919 3572756802050867843613619 := by
  unfold tailWord_6957919
  simp only [CollatzResearch.WordTrace]
  refine ⟨253776154479655255803484811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169184102986436837202323207 253776154479655255803484811)
  ·
    refine ⟨380664231719482883705227217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253776154479655255803484811 380664231719482883705227217)
    ·
      refine ⟨285498173789612162778920413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380664231719482883705227217 285498173789612162778920413)
      ·
        refine ⟨107061815171104561042095155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285498173789612162778920413 107061815171104561042095155)
        ·
          refine ⟨160592722756656841563142733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107061815171104561042095155 160592722756656841563142733)
          ·
            refine ⟨60222271033746315586178525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160592722756656841563142733 60222271033746315586178525)
            ·
              refine ⟨22583351637654868344816947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60222271033746315586178525 22583351637654868344816947)
              ·
                refine ⟨33875027456482302517225421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22583351637654868344816947 33875027456482302517225421)
                ·
                  refine ⟨12703135296180863443959533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33875027456482302517225421 12703135296180863443959533)
                  ·
                    refine ⟨4763675736067823791484825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12703135296180863443959533 4763675736067823791484825)
                    ·
                      refine ⟨3572756802050867843613619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763675736067823791484825 3572756802050867843613619)
                      ·
                        rfl

theorem cell23_6957919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_6957919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6957919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6957919 prefixEnd_6957919 := by exact prefixLift 6957919
  have htrace : WordTrace (prefixWord ++ tailWord_6957919) baseStart_6957919 baseEnd_6957919 := by
    simpa [prefixWord, tailWord_6957919, baseEnd_6957919] using wordTrace_append hprefix tailTrace_6957919
  have hstable : (prefixWord ++ tailWord_6957919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6957919).length < 2 ^ (prefixWord ++ tailWord_6957919).sum := by decide
  have hdescent : baseEnd_6957919 < baseStart_6957919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6957919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958039 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 4, 4, 2]
def baseStart_6958039 : Nat := 118140960795 + 6958039 * 2 ^ 59
def prefixEnd_6958039 : Nat := 4983230072969 + 3 ^ 40 * 6958039 * 2
def baseEnd_6958039 : Nat := 3572818419729407374113067

theorem tailTrace_6958039 : CollatzResearch.WordTrace tailWord_6958039 prefixEnd_6958039 3572818419729407374113067 := by
  unfold tailWord_6958039
  simp only [CollatzResearch.WordTrace]
  refine ⟨253780531239220516297853171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169187020826147010865235447 253780531239220516297853171)
  ·
    refine ⟨380670796858830774446779757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253780531239220516297853171 380670796858830774446779757)
    ·
      refine ⟨142751548822061540417542409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380670796858830774446779757 142751548822061540417542409)
      ·
        refine ⟨107063661616546155313156807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142751548822061540417542409 107063661616546155313156807)
        ·
          refine ⟨160595492424819232969735211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107063661616546155313156807 160595492424819232969735211)
          ·
            refine ⟨240893238637228849454602817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160595492424819232969735211 240893238637228849454602817)
            ·
              refine ⟨180669928977921637090952113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240893238637228849454602817 180669928977921637090952113)
              ·
                refine ⟨135502446733441227818214085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180669928977921637090952113 135502446733441227818214085)
                ·
                  refine ⟨25406708762520230215915141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135502446733441227818214085 25406708762520230215915141)
                  ·
                    refine ⟨4763757892972543165484089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25406708762520230215915141 4763757892972543165484089)
                    ·
                      refine ⟨3572818419729407374113067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763757892972543165484089 3572818419729407374113067)
                      ·
                        rfl

theorem cell23_6958039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_6958039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958039 prefixEnd_6958039 := by exact prefixLift 6958039
  have htrace : WordTrace (prefixWord ++ tailWord_6958039) baseStart_6958039 baseEnd_6958039 := by
    simpa [prefixWord, tailWord_6958039, baseEnd_6958039] using wordTrace_append hprefix tailTrace_6958039
  have hstable : (prefixWord ++ tailWord_6958039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958039).length < 2 ^ (prefixWord ++ tailWord_6958039).sum := by decide
  have hdescent : baseEnd_6958039 < baseStart_6958039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958052 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_6958052 : Nat := 118140960795 + 6958052 * 2 ^ 59
def prefixEnd_6958052 : Nat := 4983230072969 + 3 ^ 40 * 6958052 * 2
def baseEnd_6958052 : Nat := 3572825094977915823250507

theorem tailTrace_6958052 : CollatzResearch.WordTrace tailWord_6958052 prefixEnd_6958052 3572825094977915823250507 := by
  unfold tailWord_6958052
  simp only [CollatzResearch.WordTrace]
  refine ⟨126890502694086709759038205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169187336925448946345384273 126890502694086709759038205)
  ·
    refine ⟨47583938510282516159639327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126890502694086709759038205 47583938510282516159639327)
    ·
      refine ⟨71375907765423774239458991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47583938510282516159639327 71375907765423774239458991)
      ·
        refine ⟨107063861648135661359188487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71375907765423774239458991 107063861648135661359188487)
        ·
          refine ⟨160595792472203492038782731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107063861648135661359188487 160595792472203492038782731)
          ·
            refine ⟨240893688708305238058174097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160595792472203492038782731 240893688708305238058174097)
            ·
              refine ⟨180670266531228928543630573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240893688708305238058174097 180670266531228928543630573)
              ·
                refine ⟨67751349949210848203861465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180670266531228928543630573 67751349949210848203861465)
                ·
                  refine ⟨50813512461908136152896099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67751349949210848203861465 50813512461908136152896099)
                  ·
                    refine ⟨76220268692862204229344149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50813512461908136152896099 76220268692862204229344149)
                    ·
                      refine ⟨3572825094977915823250507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76220268692862204229344149 3572825094977915823250507)
                      ·
                        rfl

theorem cell23_6958052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_6958052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958052 prefixEnd_6958052 := by exact prefixLift 6958052
  have htrace : WordTrace (prefixWord ++ tailWord_6958052) baseStart_6958052 baseEnd_6958052 := by
    simpa [prefixWord, tailWord_6958052, baseEnd_6958052] using wordTrace_append hprefix tailTrace_6958052
  have hstable : (prefixWord ++ tailWord_6958052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958052).length < 2 ^ (prefixWord ++ tailWord_6958052).sum := by decide
  have hdescent : baseEnd_6958052 < baseStart_6958052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958068 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6958068 : Nat := 118140960795 + 6958068 * 2 ^ 59
def prefixEnd_6958068 : Nat := 4983230072969 + 3 ^ 40 * 6958068 * 2
def baseEnd_6958068 : Nat := 3572833310668387760650435

theorem tailTrace_6958068 : CollatzResearch.WordTrace tailWord_6958068 prefixEnd_6958068 3572833310668387760650435 := by
  unfold tailWord_6958068
  simp only [CollatzResearch.WordTrace]
  refine ⟨126890794478057727125329429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169187725970743636167105905 126890794478057727125329429)
  ·
    refine ⟨5948005991158955958999817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126890794478057727125329429 5948005991158955958999817)
    ·
      refine ⟨4461004493369216969249863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5948005991158955958999817 4461004493369216969249863)
      ·
        refine ⟨6691506740053825453874795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461004493369216969249863 6691506740053825453874795)
        ·
          refine ⟨10037260110080738180812193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6691506740053825453874795 10037260110080738180812193)
          ·
            refine ⟨7527945082560553635609145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10037260110080738180812193 7527945082560553635609145)
            ·
              refine ⟨5645958811920415226706859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7527945082560553635609145 5645958811920415226706859)
              ·
                refine ⟨8468938217880622840060289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645958811920415226706859 8468938217880622840060289)
                ·
                  refine ⟨6351703663410467130045217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8468938217880622840060289 6351703663410467130045217)
                  ·
                    refine ⟨4763777747557850347533913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6351703663410467130045217 4763777747557850347533913)
                    ·
                      refine ⟨3572833310668387760650435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763777747557850347533913 3572833310668387760650435)
                      ·
                        rfl

theorem cell23_6958068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6958068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958068 prefixEnd_6958068 := by exact prefixLift 6958068
  have htrace : WordTrace (prefixWord ++ tailWord_6958068) baseStart_6958068 baseEnd_6958068 := by
    simpa [prefixWord, tailWord_6958068, baseEnd_6958068] using wordTrace_append hprefix tailTrace_6958068
  have hstable : (prefixWord ++ tailWord_6958068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958068).length < 2 ^ (prefixWord ++ tailWord_6958068).sum := by decide
  have hdescent : baseEnd_6958068 < baseStart_6958068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958123 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 1, 1, 3]
def baseStart_6958123 : Nat := 118140960795 + 6958123 * 2 ^ 59
def prefixEnd_6958123 : Nat := 4983230072969 + 3 ^ 40 * 6958123 * 2
def baseEnd_6958123 : Nat := 3572861552104385045462681

theorem tailTrace_6958123 : CollatzResearch.WordTrace tailWord_6958123 prefixEnd_6958123 3572861552104385045462681 := by
  unfold tailWord_6958123
  simp only [CollatzResearch.WordTrace]
  refine ⟨253783594970916198643911023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169189063313944132429274015 253783594970916198643911023)
  ·
    refine ⟨380675392456374297965866535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253783594970916198643911023 380675392456374297965866535)
    ·
      refine ⟨571013088684561446948799803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380675392456374297965866535 571013088684561446948799803)
      ·
        refine ⟨856519633026842170423199705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571013088684561446948799803 856519633026842170423199705)
        ·
          refine ⟨642389724770131627817399779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856519633026842170423199705 642389724770131627817399779)
          ·
            refine ⟨963584587155197441726099669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642389724770131627817399779 963584587155197441726099669)
            ·
              refine ⟨22584013761449940040455461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 963584587155197441726099669 22584013761449940040455461)
              ·
                refine ⟨4234502580271863757585399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22584013761449940040455461 4234502580271863757585399)
                ·
                  refine ⟨6351753870407795636378099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234502580271863757585399 6351753870407795636378099)
                  ·
                    refine ⟨9527630805611693454567149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351753870407795636378099 9527630805611693454567149)
                    ·
                      refine ⟨3572861552104385045462681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9527630805611693454567149 3572861552104385045462681)
                      ·
                        rfl

theorem cell23_6958123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 1, 1, 3].length) (baseStart_6958123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958123 prefixEnd_6958123 := by exact prefixLift 6958123
  have htrace : WordTrace (prefixWord ++ tailWord_6958123) baseStart_6958123 baseEnd_6958123 := by
    simpa [prefixWord, tailWord_6958123, baseEnd_6958123] using wordTrace_append hprefix tailTrace_6958123
  have hstable : (prefixWord ++ tailWord_6958123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958123).length < 2 ^ (prefixWord ++ tailWord_6958123).sum := by decide
  have hdescent : baseEnd_6958123 < baseStart_6958123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958129 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_6958129 : Nat := 118140960795 + 6958129 * 2 ^ 59
def prefixEnd_6958129 : Nat := 4983230072969 + 3 ^ 40 * 6958129 * 2
def baseEnd_6958129 : Nat := 3572864632988312021987653

theorem tailTrace_6958129 : CollatzResearch.WordTrace tailWord_6958129 prefixEnd_6958129 3572864632988312021987653 := by
  unfold tailWord_6958129
  simp only [CollatzResearch.WordTrace]
  refine ⟨253783813808894461668629441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169189209205929641112419627 253783813808894461668629441)
  ·
    refine ⟨190337860356670846251472081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253783813808894461668629441 190337860356670846251472081)
    ·
      refine ⟨142753395267503134688604061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190337860356670846251472081 142753395267503134688604061)
      ·
        refine ⟨53532523225313675508226523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142753395267503134688604061 53532523225313675508226523)
        ·
          refine ⟨80298784837970513262339785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53532523225313675508226523 80298784837970513262339785)
          ·
            refine ⟨60224088628477884946754839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80298784837970513262339785 60224088628477884946754839)
            ·
              refine ⟨90336132942716827420132259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60224088628477884946754839 90336132942716827420132259)
              ·
                refine ⟨135504199414075241130198389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90336132942716827420132259 135504199414075241130198389)
                ·
                  refine ⟨12703518695069553855956099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135504199414075241130198389 12703518695069553855956099)
                  ·
                    refine ⟨19055278042604330783934149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12703518695069553855956099 19055278042604330783934149)
                    ·
                      refine ⟨3572864632988312021987653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19055278042604330783934149 3572864632988312021987653)
                      ·
                        rfl

theorem cell23_6958129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_6958129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958129 prefixEnd_6958129 := by exact prefixLift 6958129
  have htrace : WordTrace (prefixWord ++ tailWord_6958129) baseStart_6958129 baseEnd_6958129 := by
    simpa [prefixWord, tailWord_6958129, baseEnd_6958129] using wordTrace_append hprefix tailTrace_6958129
  have hstable : (prefixWord ++ tailWord_6958129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958129).length < 2 ^ (prefixWord ++ tailWord_6958129).sum := by decide
  have hdescent : baseEnd_6958129 < baseStart_6958129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958150 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_6958150 : Nat := 118140960795 + 6958150 * 2 ^ 59
def prefixEnd_6958150 : Nat := 4983230072969 + 3 ^ 40 * 6958150 * 2
def baseEnd_6958150 : Nat := 3572875416082056439825057

theorem tailTrace_6958150 : CollatzResearch.WordTrace tailWord_6958150 prefixEnd_6958150 3572875416082056439825057 := by
  unfold tailWord_6958150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7930768116931824445473247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169189719827878921503429269 7930768116931824445473247)
  ·
    refine ⟨11896152175397736668209871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7930768116931824445473247 11896152175397736668209871)
    ·
      refine ⟨17844228263096605002314807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896152175397736668209871 17844228263096605002314807)
      ·
        refine ⟨26766342394644907503472211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17844228263096605002314807 26766342394644907503472211)
        ·
          refine ⟨40149513591967361255208317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26766342394644907503472211 40149513591967361255208317)
          ·
            refine ⟨15056067596987760470703119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40149513591967361255208317 15056067596987760470703119)
            ·
              refine ⟨22584101395481640706054679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056067596987760470703119 22584101395481640706054679)
              ·
                refine ⟨33876152093222461059082019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22584101395481640706054679 33876152093222461059082019)
                ·
                  refine ⟨50814228139833691588623029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33876152093222461059082019 50814228139833691588623029)
                  ·
                    refine ⟨4763833888109408586433409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50814228139833691588623029 4763833888109408586433409)
                    ·
                      refine ⟨3572875416082056439825057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763833888109408586433409 3572875416082056439825057)
                      ·
                        rfl

theorem cell23_6958150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_6958150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958150 prefixEnd_6958150 := by exact prefixLift 6958150
  have htrace : WordTrace (prefixWord ++ tailWord_6958150) baseStart_6958150 baseEnd_6958150 := by
    simpa [prefixWord, tailWord_6958150, baseEnd_6958150] using wordTrace_append hprefix tailTrace_6958150
  have hstable : (prefixWord ++ tailWord_6958150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958150).length < 2 ^ (prefixWord ++ tailWord_6958150).sum := by decide
  have hdescent : baseEnd_6958150 < baseStart_6958150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958157 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_6958157 : Nat := 118140960795 + 6958157 * 2 ^ 59
def prefixEnd_6958157 : Nat := 4983230072969 + 3 ^ 40 * 6958157 * 2
def baseEnd_6958157 : Nat := 3572879010446637912437525

theorem tailTrace_6958157 : CollatzResearch.WordTrace tailWord_6958157 prefixEnd_6958157 3572879010446637912437525 := by
  unfold tailWord_6958157
  simp only [CollatzResearch.WordTrace]
  refine ⟨253784835052793022450648725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169189890035195348300432483 253784835052793022450648725)
  ·
    refine ⟨11896164143099672927374159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253784835052793022450648725 11896164143099672927374159)
    ·
      refine ⟨17844246214649509391061239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896164143099672927374159 17844246214649509391061239)
      ·
        refine ⟨26766369321974264086591859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17844246214649509391061239 26766369321974264086591859)
        ·
          refine ⟨40149553982961396129887789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26766369321974264086591859 40149553982961396129887789)
          ·
            refine ⟨15056082743610523548707921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40149553982961396129887789 15056082743610523548707921)
            ·
              refine ⟨11292062057707892661530941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15056082743610523548707921 11292062057707892661530941)
              ·
                refine ⟨4234523271640459748074103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11292062057707892661530941 4234523271640459748074103)
                ·
                  refine ⟨6351784907460689622111155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234523271640459748074103 6351784907460689622111155)
                  ·
                    refine ⟨9527677361191034433166733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351784907460689622111155 9527677361191034433166733)
                    ·
                      refine ⟨3572879010446637912437525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9527677361191034433166733 3572879010446637912437525)
                      ·
                        rfl

theorem cell23_6958157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_6958157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958157 prefixEnd_6958157 := by exact prefixLift 6958157
  have htrace : WordTrace (prefixWord ++ tailWord_6958157) baseStart_6958157 baseEnd_6958157 := by
    simpa [prefixWord, tailWord_6958157, baseEnd_6958157] using wordTrace_append hprefix tailTrace_6958157
  have hstable : (prefixWord ++ tailWord_6958157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958157).length < 2 ^ (prefixWord ++ tailWord_6958157).sum := by decide
  have hdescent : baseEnd_6958157 < baseStart_6958157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958174 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6958174 : Nat := 118140960795 + 6958174 * 2 ^ 59
def prefixEnd_6958174 : Nat := 4983230072969 + 3 ^ 40 * 6958174 * 2
def baseEnd_6958174 : Nat := 3572887739617764345924947

theorem tailTrace_6958174 : CollatzResearch.WordTrace tailWord_6958174 prefixEnd_6958174 3572887739617764345924947 := by
  unfold tailWord_6958174
  simp only [CollatzResearch.WordTrace]
  refine ⟨31723181886716429294252197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169190303395820956236011717 31723181886716429294252197)
  ·
    refine ⟨5948096603759330492672287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31723181886716429294252197 5948096603759330492672287)
    ·
      refine ⟨8922144905638995739008431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948096603759330492672287 8922144905638995739008431)
      ·
        refine ⟨13383217358458493608512647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922144905638995739008431 13383217358458493608512647)
        ·
          refine ⟨20074826037687740412768971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383217358458493608512647 20074826037687740412768971)
          ·
            refine ⟨30112239056531610619153457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20074826037687740412768971 30112239056531610619153457)
            ·
              refine ⟨22584179292398707964365093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30112239056531610619153457 22584179292398707964365093)
              ·
                refine ⟨4234533617324757743318455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22584179292398707964365093 4234533617324757743318455)
                ·
                  refine ⟨6351800425987136614977683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234533617324757743318455 6351800425987136614977683)
                  ·
                    refine ⟨9527700638980704922466525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351800425987136614977683 9527700638980704922466525)
                    ·
                      refine ⟨3572887739617764345924947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9527700638980704922466525 3572887739617764345924947)
                      ·
                        rfl

theorem cell23_6958174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6958174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958174 prefixEnd_6958174 := by exact prefixLift 6958174
  have htrace : WordTrace (prefixWord ++ tailWord_6958174) baseStart_6958174 baseEnd_6958174 := by
    simpa [prefixWord, tailWord_6958174, baseEnd_6958174] using wordTrace_append hprefix tailTrace_6958174
  have hstable : (prefixWord ++ tailWord_6958174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958174).length < 2 ^ (prefixWord ++ tailWord_6958174).sum := by decide
  have hdescent : baseEnd_6958174 < baseStart_6958174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958190 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_6958190 : Nat := 118140960795 + 6958190 * 2 ^ 59
def prefixEnd_6958190 : Nat := 4983230072969 + 3 ^ 40 * 6958190 * 2
def baseEnd_6958190 : Nat := 1190965318436078761108291

theorem tailTrace_6958190 : CollatzResearch.WordTrace tailWord_6958190 prefixEnd_6958190 1190965318436078761108291 := by
  unfold tailWord_6958190
  simp only [CollatzResearch.WordTrace]
  refine ⟨31723254832709183635825003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169190692441115646057733349 31723254832709183635825003)
  ·
    refine ⟨47584882249063775453737505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31723254832709183635825003 47584882249063775453737505)
    ·
      refine ⟨35688661686797831590303129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47584882249063775453737505 35688661686797831590303129)
      ·
        refine ⟨26766496265098373692727347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35688661686797831590303129 26766496265098373692727347)
        ·
          refine ⟨40149744397647560539091021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26766496265098373692727347 40149744397647560539091021)
          ·
            refine ⟨15056154149117835202159133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40149744397647560539091021 15056154149117835202159133)
            ·
              refine ⟨5646057805919188200809675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15056154149117835202159133 5646057805919188200809675)
              ·
                refine ⟨8469086708878782301214513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646057805919188200809675 8469086708878782301214513)
                ·
                  refine ⟨6351815031659086725910885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469086708878782301214513 6351815031659086725910885)
                  ·
                    refine ⟨1190965318436078761108291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351815031659086725910885 1190965318436078761108291)
                    ·
                      rfl

theorem cell23_6958190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_6958190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958190 prefixEnd_6958190 := by exact prefixLift 6958190
  have htrace : WordTrace (prefixWord ++ tailWord_6958190) baseStart_6958190 baseEnd_6958190 := by
    simpa [prefixWord, tailWord_6958190, baseEnd_6958190] using wordTrace_append hprefix tailTrace_6958190
  have hstable : (prefixWord ++ tailWord_6958190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958190).length < 2 ^ (prefixWord ++ tailWord_6958190).sum := by decide
  have hdescent : baseEnd_6958190 < baseStart_6958190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958229 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_6958229 : Nat := 118140960795 + 6958229 * 2 ^ 59
def prefixEnd_6958229 : Nat := 4983230072969 + 3 ^ 40 * 6958229 * 2
def baseEnd_6958229 : Nat := 1190971993684587210245731

theorem tailTrace_6958229 : CollatzResearch.WordTrace tailWord_6958229 prefixEnd_6958229 1190971993684587210245731 := by
  unfold tailWord_6958229
  simp only [CollatzResearch.WordTrace]
  refine ⟨253787461108532178747269741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169191640739021452498179827 253787461108532178747269741)
  ·
    refine ⟨95170297915699567030226153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253787461108532178747269741 95170297915699567030226153)
    ·
      refine ⟨71377723436774675272669615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95170297915699567030226153 71377723436774675272669615)
      ·
        refine ⟨107066585155162012909004423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71377723436774675272669615 107066585155162012909004423)
        ·
          refine ⟨160599877732743019363506635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107066585155162012909004423 160599877732743019363506635)
          ·
            refine ⟨240899816599114529045259953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160599877732743019363506635 240899816599114529045259953)
            ·
              refine ⟨180674862449335896783944965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240899816599114529045259953 180674862449335896783944965)
              ·
                refine ⟨33876536709250480646989681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180674862449335896783944965 33876536709250480646989681)
                ·
                  refine ⟨25407402531937860485242261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33876536709250480646989681 25407402531937860485242261)
                  ·
                    refine ⟨1190971993684587210245731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25407402531937860485242261 1190971993684587210245731)
                    ·
                      rfl

theorem cell23_6958229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_6958229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958229 prefixEnd_6958229 := by exact prefixLift 6958229
  have htrace : WordTrace (prefixWord ++ tailWord_6958229) baseStart_6958229 baseEnd_6958229 := by
    simpa [prefixWord, tailWord_6958229, baseEnd_6958229] using wordTrace_append hprefix tailTrace_6958229
  have hstable : (prefixWord ++ tailWord_6958229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958229).length < 2 ^ (prefixWord ++ tailWord_6958229).sum := by decide
  have hdescent : baseEnd_6958229 < baseStart_6958229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958247 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6958247 : Nat := 118140960795 + 6958247 * 2 ^ 59
def prefixEnd_6958247 : Nat := 4983230072969 + 3 ^ 40 * 6958247 * 2
def baseEnd_6958247 : Nat := 3572925223705542560312111

theorem tailTrace_6958247 : CollatzResearch.WordTrace tailWord_6958247 prefixEnd_6958247 3572925223705542560312111 := by
  unfold tailWord_6958247
  simp only [CollatzResearch.WordTrace]
  refine ⟨253788117622466967821424995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169192078414977978547616663 253788117622466967821424995)
  ·
    refine ⟨380682176433700451732137493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253788117622466967821424995 380682176433700451732137493)
    ·
      refine ⟨17844477020329708674943945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 380682176433700451732137493 17844477020329708674943945)
      ·
        refine ⟨13383357765247281506207959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17844477020329708674943945 13383357765247281506207959)
        ·
          refine ⟨20075036647870922259311939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383357765247281506207959 20075036647870922259311939)
          ·
            refine ⟨30112554971806383388967909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075036647870922259311939 30112554971806383388967909)
            ·
              refine ⟨5646104057213696885431483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30112554971806383388967909 5646104057213696885431483)
              ·
                refine ⟨8469156085820545328147225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646104057213696885431483 8469156085820545328147225)
                ·
                  refine ⟨6351867064365408996110419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469156085820545328147225 6351867064365408996110419)
                  ·
                    refine ⟨9527800596548113494165629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6351867064365408996110419 9527800596548113494165629)
                    ·
                      refine ⟨3572925223705542560312111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9527800596548113494165629 3572925223705542560312111)
                      ·
                        rfl

theorem cell23_6958247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6958247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958247 prefixEnd_6958247 := by exact prefixLift 6958247
  have htrace : WordTrace (prefixWord ++ tailWord_6958247) baseStart_6958247 baseEnd_6958247 := by
    simpa [prefixWord, tailWord_6958247, baseEnd_6958247] using wordTrace_append hprefix tailTrace_6958247
  have hstable : (prefixWord ++ tailWord_6958247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958247).length < 2 ^ (prefixWord ++ tailWord_6958247).sum := by decide
  have hdescent : baseEnd_6958247 < baseStart_6958247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958257 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6958257 : Nat := 118140960795 + 6958257 * 2 ^ 59
def prefixEnd_6958257 : Nat := 4983230072969 + 3 ^ 40 * 6958257 * 2
def baseEnd_6958257 : Nat := 3572930358512087521187065

theorem tailTrace_6958257 : CollatzResearch.WordTrace tailWord_6958257 prefixEnd_6958257 3572930358512087521187065 := by
  unfold tailWord_6958257
  simp only [CollatzResearch.WordTrace]
  refine ⟨253788482352430739529289025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169192321568287159686192683 253788482352430739529289025)
  ·
    refine ⟨190341361764323054646966769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253788482352430739529289025 190341361764323054646966769)
    ·
      refine ⟨142756021323242290985225077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190341361764323054646966769 142756021323242290985225077)
      ·
        refine ⟨13383376999053964779864851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142756021323242290985225077 13383376999053964779864851)
        ·
          refine ⟨20075065498580947169797277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383376999053964779864851 20075065498580947169797277)
          ·
            refine ⟨7528149561967855188673979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20075065498580947169797277 7528149561967855188673979)
            ·
              refine ⟨11292224342951782783010969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528149561967855188673979 11292224342951782783010969)
              ·
                refine ⟨8469168257213837087258227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11292224342951782783010969 8469168257213837087258227)
                ·
                  refine ⟨12703752385820755630887341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8469168257213837087258227 12703752385820755630887341)
                  ·
                    refine ⟨4763907144682783361582753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12703752385820755630887341 4763907144682783361582753)
                    ·
                      refine ⟨3572930358512087521187065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763907144682783361582753 3572930358512087521187065)
                      ·
                        rfl

theorem cell23_6958257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6958257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958257 prefixEnd_6958257 := by exact prefixLift 6958257
  have htrace : WordTrace (prefixWord ++ tailWord_6958257) baseStart_6958257 baseEnd_6958257 := by
    simpa [prefixWord, tailWord_6958257, baseEnd_6958257] using wordTrace_append hprefix tailTrace_6958257
  have hstable : (prefixWord ++ tailWord_6958257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958257).length < 2 ^ (prefixWord ++ tailWord_6958257).sum := by decide
  have hdescent : baseEnd_6958257 < baseStart_6958257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958259 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 7]
def baseStart_6958259 : Nat := 118140960795 + 6958259 * 2 ^ 59
def prefixEnd_6958259 : Nat := 4983230072969 + 3 ^ 40 * 6958259 * 2
def baseEnd_6958259 : Nat := 396992376163710723706895

theorem tailTrace_6958259 : CollatzResearch.WordTrace tailWord_6958259 prefixEnd_6958259 396992376163710723706895 := by
  unfold tailWord_6958259
  simp only [CollatzResearch.WordTrace]
  refine ⟨253788555298423493870861831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169192370198948995913907887 253788555298423493870861831)
  ·
    refine ⟨380682832947635240806292747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253788555298423493870861831 380682832947635240806292747)
    ·
      refine ⟨571024249421452861209439121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380682832947635240806292747 571024249421452861209439121)
      ·
        refine ⟨428268187066089645907079341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571024249421452861209439121 428268187066089645907079341)
        ·
          refine ⟨160600570149783617215154753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428268187066089645907079341 160600570149783617215154753)
          ·
            refine ⟨120450427612337712911366065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160600570149783617215154753 120450427612337712911366065)
            ·
              refine ⟨90337820709253284683524549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120450427612337712911366065 90337820709253284683524549)
              ·
                refine ⟨16938341382984990878160853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90337820709253284683524549 16938341382984990878160853)
                ·
                  refine ⟨396992376163710723706895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16938341382984990878160853 396992376163710723706895)
                  ·
                    rfl

theorem cell23_6958259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 7].length) (baseStart_6958259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958259 prefixEnd_6958259 := by exact prefixLift 6958259
  have htrace : WordTrace (prefixWord ++ tailWord_6958259) baseStart_6958259 baseEnd_6958259 := by
    simpa [prefixWord, tailWord_6958259, baseEnd_6958259] using wordTrace_append hprefix tailTrace_6958259
  have hstable : (prefixWord ++ tailWord_6958259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958259).length < 2 ^ (prefixWord ++ tailWord_6958259).sum := by decide
  have hdescent : baseEnd_6958259 < baseStart_6958259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958270 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_6958270 : Nat := 118140960795 + 6958270 * 2 ^ 59
def prefixEnd_6958270 : Nat := 4983230072969 + 3 ^ 40 * 6958270 * 2
def baseEnd_6958270 : Nat := 3572937033760595970324505

theorem tailTrace_6958270 : CollatzResearch.WordTrace tailWord_6958270 prefixEnd_6958270 3572937033760595970324505 := by
  unfold tailWord_6958270
  simp only [CollatzResearch.WordTrace]
  refine ⟨31723619562672955343689033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169192637667589095166341509 31723619562672955343689033)
  ·
    refine ⟨23792714672004716507766775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31723619562672955343689033 23792714672004716507766775)
    ·
      refine ⟨35689072008007074761650163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23792714672004716507766775 35689072008007074761650163)
      ·
        refine ⟨53533608012010612142475245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35689072008007074761650163 53533608012010612142475245)
        ·
          refine ⟨20075103004503979553428217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53533608012010612142475245 20075103004503979553428217)
          ·
            refine ⟨15056327253377984665071163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20075103004503979553428217 15056327253377984665071163)
            ·
              refine ⟨22584490880066976997606745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056327253377984665071163 22584490880066976997606745)
              ·
                refine ⟨16938368160050232748205059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22584490880066976997606745 16938368160050232748205059)
                ·
                  refine ⟨25407552240075349122307589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16938368160050232748205059 25407552240075349122307589)
                  ·
                    refine ⟨4763916045014127960432673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25407552240075349122307589 4763916045014127960432673)
                    ·
                      refine ⟨3572937033760595970324505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4763916045014127960432673 3572937033760595970324505)
                      ·
                        rfl

theorem cell23_6958270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_6958270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958270 prefixEnd_6958270 := by exact prefixLift 6958270
  have htrace : WordTrace (prefixWord ++ tailWord_6958270) baseStart_6958270 baseEnd_6958270 := by
    simpa [prefixWord, tailWord_6958270, baseEnd_6958270] using wordTrace_append hprefix tailTrace_6958270
  have hstable : (prefixWord ++ tailWord_6958270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958270).length < 2 ^ (prefixWord ++ tailWord_6958270).sum := by decide
  have hdescent : baseEnd_6958270 < baseStart_6958270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958273 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6958273 : Nat := 118140960795 + 6958273 * 2 ^ 59
def prefixEnd_6958273 : Nat := 4983230072969 + 3 ^ 40 * 6958273 * 2
def baseEnd_6958273 : Nat := 3572938574202559458586991

theorem tailTrace_6958273 : CollatzResearch.WordTrace tailWord_6958273 prefixEnd_6958273 3572938574202559458586991 := by
  unfold tailWord_6958273
  simp only [CollatzResearch.WordTrace]
  refine ⟨253789065920372774261871473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169192710613581849507914315 253789065920372774261871473)
  ·
    refine ⟨190341799440279580696403605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253789065920372774261871473 190341799440279580696403605)
    ·
      refine ⟨8922271848763105345143919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190341799440279580696403605 8922271848763105345143919)
      ·
        refine ⟨13383407773144658017715879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922271848763105345143919 13383407773144658017715879)
        ·
          refine ⟨20075111659716987026573819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383407773144658017715879 20075111659716987026573819)
          ·
            refine ⟨30112667489575480539860729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075111659716987026573819 30112667489575480539860729)
            ·
              refine ⟨22584500617181610404895547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30112667489575480539860729 22584500617181610404895547)
              ·
                refine ⟨33876750925772415607343321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22584500617181610404895547 33876750925772415607343321)
                ·
                  refine ⟨25407563194329311705507491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33876750925772415607343321 25407563194329311705507491)
                  ·
                    refine ⟨38111344791493967558261237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25407563194329311705507491 38111344791493967558261237)
                    ·
                      refine ⟨3572938574202559458586991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38111344791493967558261237 3572938574202559458586991)
                      ·
                        rfl

theorem cell23_6958273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6958273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958273 prefixEnd_6958273 := by exact prefixLift 6958273
  have htrace : WordTrace (prefixWord ++ tailWord_6958273) baseStart_6958273 baseEnd_6958273 := by
    simpa [prefixWord, tailWord_6958273, baseEnd_6958273] using wordTrace_append hprefix tailTrace_6958273
  have hstable : (prefixWord ++ tailWord_6958273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958273).length < 2 ^ (prefixWord ++ tailWord_6958273).sum := by decide
  have hdescent : baseEnd_6958273 < baseStart_6958273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958289 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 3, 7]
def baseStart_6958289 : Nat := 118140960795 + 6958289 * 2 ^ 59
def prefixEnd_6958289 : Nat := 4983230072969 + 3 ^ 40 * 6958289 * 2
def baseEnd_6958289 : Nat := 1190982263297677131995639

theorem tailTrace_6958289 : CollatzResearch.WordTrace tailWord_6958289 prefixEnd_6958289 1190982263297677131995639 := by
  unfold tailWord_6958289
  simp only [CollatzResearch.WordTrace]
  refine ⟨253789649488314808994453921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169193099658876539329635947 253789649488314808994453921)
  ·
    refine ⟨190342237116236106745840441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253789649488314808994453921 190342237116236106745840441)
    ·
      refine ⟨142756677837177080059380331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190342237116236106745840441 142756677837177080059380331)
      ·
        refine ⟨214135016755765620089070497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142756677837177080059380331 214135016755765620089070497)
        ·
          refine ⟨160601262566824215066802873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214135016755765620089070497 160601262566824215066802873)
          ·
            refine ⟨120450946925118161300102155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160601262566824215066802873 120450946925118161300102155)
            ·
              refine ⟨180676420387677241950153233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120450946925118161300102155 180676420387677241950153233)
              ·
                refine ⟨135507315290757931462614925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180676420387677241950153233 135507315290757931462614925)
                ·
                  refine ⟨50815243234034224298480597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135507315290757931462614925 50815243234034224298480597)
                  ·
                    refine ⟨1190982263297677131995639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50815243234034224298480597 1190982263297677131995639)
                    ·
                      rfl

theorem cell23_6958289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_6958289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958289 prefixEnd_6958289 := by exact prefixLift 6958289
  have htrace : WordTrace (prefixWord ++ tailWord_6958289) baseStart_6958289 baseEnd_6958289 := by
    simpa [prefixWord, tailWord_6958289, baseEnd_6958289] using wordTrace_append hprefix tailTrace_6958289
  have hstable : (prefixWord ++ tailWord_6958289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958289).length < 2 ^ (prefixWord ++ tailWord_6958289).sum := by decide
  have hdescent : baseEnd_6958289 < baseStart_6958289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958299 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5]
def baseStart_6958299 : Nat := 118140960795 + 6958299 * 2 ^ 59
def prefixEnd_6958299 : Nat := 4983230072969 + 3 ^ 40 * 6958299 * 2
def baseEnd_6958299 : Nat := 3572951924699576356861871

theorem tailTrace_6958299 : CollatzResearch.WordTrace tailWord_6958299 prefixEnd_6958299 3572951924699576356861871 := by
  unfold tailWord_6958299
  simp only [CollatzResearch.WordTrace]
  refine ⟨253790014218278580702317951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169193342812185720468211967 253790014218278580702317951)
  ·
    refine ⟨380685021327417871053476927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253790014218278580702317951 380685021327417871053476927)
    ·
      refine ⟨571027531991126806580215391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380685021327417871053476927 571027531991126806580215391)
      ·
        refine ⟨856541297986690209870323087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571027531991126806580215391 856541297986690209870323087)
        ·
          refine ⟨1284811946980035314805484631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856541297986690209870323087 1284811946980035314805484631)
          ·
            refine ⟨1927217920470052972208226947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284811946980035314805484631 1927217920470052972208226947)
            ·
              refine ⟨2890826880705079458312340421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927217920470052972208226947 2890826880705079458312340421)
              ·
                refine ⟨542030040132202398433563829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2890826880705079458312340421 542030040132202398433563829)
                ·
                  refine ⟨50815316262393974853146609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 542030040132202398433563829 50815316262393974853146609)
                  ·
                    refine ⟨38111487196795481139859957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50815316262393974853146609 38111487196795481139859957)
                    ·
                      refine ⟨3572951924699576356861871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38111487196795481139859957 3572951924699576356861871)
                      ·
                        rfl

theorem cell23_6958299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 5].length) (baseStart_6958299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958299 prefixEnd_6958299 := by exact prefixLift 6958299
  have htrace : WordTrace (prefixWord ++ tailWord_6958299) baseStart_6958299 baseEnd_6958299 := by
    simpa [prefixWord, tailWord_6958299, baseEnd_6958299] using wordTrace_append hprefix tailTrace_6958299
  have hstable : (prefixWord ++ tailWord_6958299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958299).length < 2 ^ (prefixWord ++ tailWord_6958299).sum := by decide
  have hdescent : baseEnd_6958299 < baseStart_6958299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958323 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 2, 5]
def baseStart_6958323 : Nat := 118140960795 + 6958323 * 2 ^ 59
def prefixEnd_6958323 : Nat := 4983230072969 + 3 ^ 40 * 6958323 * 2
def baseEnd_6958323 : Nat := 1190988082745094754320587

theorem tailTrace_6958323 : CollatzResearch.WordTrace tailWord_6958323 prefixEnd_6958323 1190988082745094754320587 := by
  unfold tailWord_6958323
  simp only [CollatzResearch.WordTrace]
  refine ⟨253790889570191632801191623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169193926380127755200794415 253790889570191632801191623)
  ·
    refine ⟨380686334355287449201787435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253790889570191632801191623 380686334355287449201787435)
    ·
      refine ⟨571029501532931173802681153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380686334355287449201787435 571029501532931173802681153)
      ·
        refine ⟨428272126149698380352010865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571029501532931173802681153 428272126149698380352010865)
        ·
          refine ⟨321204094612273785264008149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428272126149698380352010865 321204094612273785264008149)
          ·
            refine ⟨7528220967475166842125191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 321204094612273785264008149 7528220967475166842125191)
            ·
              refine ⟨11292331451212750263187787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528220967475166842125191 11292331451212750263187787)
              ·
                refine ⟨16938497176819125394781681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11292331451212750263187787 16938497176819125394781681)
                ·
                  refine ⟨12703872882614344046086261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16938497176819125394781681 12703872882614344046086261)
                  ·
                    refine ⟨1190988082745094754320587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12703872882614344046086261 1190988082745094754320587)
                    ·
                      rfl

theorem cell23_6958323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 5].length) (baseStart_6958323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958323 prefixEnd_6958323 := by exact prefixLift 6958323
  have htrace : WordTrace (prefixWord ++ tailWord_6958323) baseStart_6958323 baseEnd_6958323 := by
    simpa [prefixWord, tailWord_6958323, baseEnd_6958323] using wordTrace_append hprefix tailTrace_6958323
  have hstable : (prefixWord ++ tailWord_6958323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958323).length < 2 ^ (prefixWord ++ tailWord_6958323).sum := by decide
  have hdescent : baseEnd_6958323 < baseStart_6958323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958336 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 7, 4]
def baseStart_6958336 : Nat := 118140960795 + 6958336 * 2 ^ 59
def prefixEnd_6958336 : Nat := 4983230072969 + 3 ^ 40 * 6958336 * 2
def baseEnd_6958336 : Nat := 1190990307827930904033067

theorem tailTrace_6958336 : CollatzResearch.WordTrace tailWord_6958336 prefixEnd_6958336 1190990307827930904033067 := by
  unfold tailWord_6958336
  simp only [CollatzResearch.WordTrace]
  refine ⟨126895681859572268010707431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169194242479429690680943241 126895681859572268010707431)
  ·
    refine ⟨190343522789358402016061147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126895681859572268010707431 190343522789358402016061147)
    ·
      refine ⟨285515284184037603024091721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190343522789358402016061147 285515284184037603024091721)
      ·
        refine ⟨214136463138028202268068791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285515284184037603024091721 214136463138028202268068791)
        ·
          refine ⟨321204694707042303402103187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214136463138028202268068791 321204694707042303402103187)
          ·
            refine ⟨481807042060563455103154781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321204694707042303402103187 481807042060563455103154781)
            ·
              refine ⟨180677640772711295663683043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481807042060563455103154781 180677640772711295663683043)
              ·
                refine ⟨271016461159066943495524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180677640772711295663683043 271016461159066943495524565)
                ·
                  refine ⟨6351948308415631488176357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 271016461159066943495524565 6351948308415631488176357)
                  ·
                    refine ⟨1190990307827930904033067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351948308415631488176357 1190990307827930904033067)
                    ·
                      rfl

theorem cell23_6958336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_6958336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958336 prefixEnd_6958336 := by exact prefixLift 6958336
  have htrace : WordTrace (prefixWord ++ tailWord_6958336) baseStart_6958336 baseEnd_6958336 := by
    simpa [prefixWord, tailWord_6958336, baseEnd_6958336] using wordTrace_append hprefix tailTrace_6958336
  have hstable : (prefixWord ++ tailWord_6958336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958336).length < 2 ^ (prefixWord ++ tailWord_6958336).sum := by decide
  have hdescent : baseEnd_6958336 < baseStart_6958336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958353 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 3, 4]
def baseStart_6958353 : Nat := 118140960795 + 6958353 * 2 ^ 59
def prefixEnd_6958353 : Nat := 4983230072969 + 3 ^ 40 * 6958353 * 2
def baseEnd_6958353 : Nat := 1190993217551639715195541

theorem tailTrace_6958353 : CollatzResearch.WordTrace tailWord_6958353 prefixEnd_6958353 1190993217551639715195541 := by
  unfold tailWord_6958353
  simp only [CollatzResearch.WordTrace]
  refine ⟨253791983760082947924783713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169194655840055298616522475 253791983760082947924783713)
  ·
    refine ⟨190343987820062210943587785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253791983760082947924783713 190343987820062210943587785)
    ·
      refine ⟨142757990865046658207690839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190343987820062210943587785 142757990865046658207690839)
      ·
        refine ⟨214136986297569987311536259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142757990865046658207690839 214136986297569987311536259)
        ·
          refine ⟨321205479446354980967304389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214136986297569987311536259 321205479446354980967304389)
          ·
            refine ⟨60226027396191558931369573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321205479446354980967304389 60226027396191558931369573)
            ·
              refine ⟨11292380136785917299631795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60226027396191558931369573 11292380136785917299631795)
              ·
                refine ⟨16938570205178875949447693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11292380136785917299631795 16938570205178875949447693)
                ·
                  refine ⟨6351963826942078481042885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16938570205178875949447693 6351963826942078481042885)
                  ·
                    refine ⟨1190993217551639715195541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351963826942078481042885 1190993217551639715195541)
                    ·
                      rfl

theorem cell23_6958353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_6958353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958353 prefixEnd_6958353 := by exact prefixLift 6958353
  have htrace : WordTrace (prefixWord ++ tailWord_6958353) baseStart_6958353 baseEnd_6958353 := by
    simpa [prefixWord, tailWord_6958353, baseEnd_6958353] using wordTrace_append hprefix tailTrace_6958353
  have hstable : (prefixWord ++ tailWord_6958353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958353).length < 2 ^ (prefixWord ++ tailWord_6958353).sum := by decide
  have hdescent : baseEnd_6958353 < baseStart_6958353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958387 : List Nat := [1, 1, 1, 2, 5, 4, 1, 3, 1, 4]
def baseStart_6958387 : Nat := 118140960795 + 6958387 * 2 ^ 59
def prefixEnd_6958387 : Nat := 4983230072969 + 3 ^ 40 * 6958387 * 2
def baseEnd_6958387 : Nat := 1190999036999057337520489

theorem tailTrace_6958387 : CollatzResearch.WordTrace tailWord_6958387 prefixEnd_6958387 1190999036999057337520489 := by
  unfold tailWord_6958387
  simp only [CollatzResearch.WordTrace]
  refine ⟨253793223841959771731521415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169195482561306514487680943 253793223841959771731521415)
  ·
    refine ⟨380689835762939657597282123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253793223841959771731521415 380689835762939657597282123)
    ·
      refine ⟨571034753644409486395923185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380689835762939657597282123 571034753644409486395923185)
      ·
        refine ⟨428276065233307114796942389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571034753644409486395923185 428276065233307114796942389)
        ·
          refine ⟨40150881115622542012213349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 428276065233307114796942389 40150881115622542012213349)
          ·
            refine ⟨7528290209179226627290003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40150881115622542012213349 7528290209179226627290003)
            ·
              refine ⟨11292435313768839940935005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528290209179226627290003 11292435313768839940935005)
              ·
                refine ⟨4234663242663314977850627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11292435313768839940935005 4234663242663314977850627)
                ·
                  refine ⟨6351994863994972466775941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234663242663314977850627 6351994863994972466775941)
                  ·
                    refine ⟨1190999036999057337520489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6351994863994972466775941 1190999036999057337520489)
                    ·
                      rfl

theorem cell23_6958387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 3, 1, 4].length) (baseStart_6958387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958387 prefixEnd_6958387 := by exact prefixLift 6958387
  have htrace : WordTrace (prefixWord ++ tailWord_6958387) baseStart_6958387 baseEnd_6958387 := by
    simpa [prefixWord, tailWord_6958387, baseEnd_6958387] using wordTrace_append hprefix tailTrace_6958387
  have hstable : (prefixWord ++ tailWord_6958387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958387).length < 2 ^ (prefixWord ++ tailWord_6958387).sum := by decide
  have hdescent : baseEnd_6958387 < baseStart_6958387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958397 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6958397 : Nat := 118140960795 + 6958397 * 2 ^ 59
def prefixEnd_6958397 : Nat := 4983230072969 + 3 ^ 40 * 6958397 * 2
def baseEnd_6958397 : Nat := 3573002245803716973436421

theorem tailTrace_6958397 : CollatzResearch.WordTrace tailWord_6958397 prefixEnd_6958397 3573002245803716973436421 := by
  unfold tailWord_6958397
  simp only [CollatzResearch.WordTrace]
  refine ⟨253793588571923543439385445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169195725714615695626256963 253793588571923543439385445)
  ·
    refine ⟨47586297857235664394884771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253793588571923543439385445 47586297857235664394884771)
    ·
      refine ⟨71379446785853496592327157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47586297857235664394884771 71379446785853496592327157)
      ·
        refine ⟨6691823136173765305530671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71379446785853496592327157 6691823136173765305530671)
        ·
          refine ⟨10037734704260647958296007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6691823136173765305530671 10037734704260647958296007)
          ·
            refine ⟨15056602056390971937444011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10037734704260647958296007 15056602056390971937444011)
            ·
              refine ⟨22584903084586457906166017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056602056390971937444011 22584903084586457906166017)
              ·
                refine ⟨16938677313439843429624513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22584903084586457906166017 16938677313439843429624513)
                ·
                  refine ⟨12704007985079882572218385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16938677313439843429624513 12704007985079882572218385)
                  ·
                    refine ⟨9528005988809911929163789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12704007985079882572218385 9528005988809911929163789)
                    ·
                      refine ⟨3573002245803716973436421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528005988809911929163789 3573002245803716973436421)
                      ·
                        rfl

theorem cell23_6958397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6958397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958397 prefixEnd_6958397 := by exact prefixLift 6958397
  have htrace : WordTrace (prefixWord ++ tailWord_6958397) baseStart_6958397 baseEnd_6958397 := by
    simpa [prefixWord, tailWord_6958397, baseEnd_6958397] using wordTrace_append hprefix tailTrace_6958397
  have hstable : (prefixWord ++ tailWord_6958397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958397).length < 2 ^ (prefixWord ++ tailWord_6958397).sum := by decide
  have hdescent : baseEnd_6958397 < baseStart_6958397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958420 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_6958420 : Nat := 118140960795 + 6958420 * 2 ^ 59
def prefixEnd_6958420 : Nat := 4983230072969 + 3 ^ 40 * 6958420 * 2
def baseEnd_6958420 : Nat := 3573014055858770383448815

theorem tailTrace_6958420 : CollatzResearch.WordTrace tailWord_6958420 prefixEnd_6958420 3573014055858770383448815 := by
  unfold tailWord_6958420
  simp only [CollatzResearch.WordTrace]
  refine ⟨126897213725420109183736357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169196284967226812244981809 126897213725420109183736357)
  ·
    refine ⟨23793227573516270471950567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126897213725420109183736357 23793227573516270471950567)
    ·
      refine ⟨35689841360274405707925851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23793227573516270471950567 35689841360274405707925851)
      ·
        refine ⟨53534762040411608561888777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35689841360274405707925851 53534762040411608561888777)
        ·
          refine ⟨40151071530308706421416583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53534762040411608561888777 40151071530308706421416583)
          ·
            refine ⟨60226607295463059632124875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40151071530308706421416583 60226607295463059632124875)
            ·
              refine ⟨90339910943194589448187313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60226607295463059632124875 90339910943194589448187313)
              ·
                refine ⟨67754933207395942086140485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90339910943194589448187313 67754933207395942086140485)
                ·
                  refine ⟨12704049976386739141151341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67754933207395942086140485 12704049976386739141151341)
                  ·
                    refine ⟨4764018741145027177931753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12704049976386739141151341 4764018741145027177931753)
                    ·
                      refine ⟨3573014055858770383448815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764018741145027177931753 3573014055858770383448815)
                      ·
                        rfl

theorem cell23_6958420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_6958420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958420 prefixEnd_6958420 := by exact prefixLift 6958420
  have htrace : WordTrace (prefixWord ++ tailWord_6958420) baseStart_6958420 baseEnd_6958420 := by
    simpa [prefixWord, tailWord_6958420, baseEnd_6958420] using wordTrace_append hprefix tailTrace_6958420
  have hstable : (prefixWord ++ tailWord_6958420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958420).length < 2 ^ (prefixWord ++ tailWord_6958420).sum := by decide
  have hdescent : baseEnd_6958420 < baseStart_6958420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958433 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_6958433 : Nat := 118140960795 + 6958433 * 2 ^ 59
def prefixEnd_6958433 : Nat := 4983230072969 + 3 ^ 40 * 6958433 * 2
def baseEnd_6958433 : Nat := 3573020731107278832586255

theorem tailTrace_6958433 : CollatzResearch.WordTrace tailWord_6958433 prefixEnd_6958433 3573020731107278832586255 := by
  unfold tailWord_6958433
  simp only [CollatzResearch.WordTrace]
  refine ⟨253794901599793121587695953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169196601066528747725130635 253794901599793121587695953)
  ·
    refine ⟨190346176199844841190771965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253794901599793121587695953 190346176199844841190771965)
    ·
      refine ⟨71379816074941815446539487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190346176199844841190771965 71379816074941815446539487)
      ·
        refine ⟨107069724112412723169809231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71379816074941815446539487 107069724112412723169809231)
        ·
          refine ⟨160604586168619084754713847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107069724112412723169809231 160604586168619084754713847)
          ·
            refine ⟨240906879252928627132070771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160604586168619084754713847 240906879252928627132070771)
            ·
              refine ⟨361360318879392940698106157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240906879252928627132070771 361360318879392940698106157)
              ·
                refine ⟨135510119579772352761789809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361360318879392940698106157 135510119579772352761789809)
                ·
                  refine ⟨101632589684829264571342357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135510119579772352761789809 101632589684829264571342357)
                  ·
                    refine ⟨4764027641476371776781673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101632589684829264571342357 4764027641476371776781673)
                    ·
                      refine ⟨3573020731107278832586255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764027641476371776781673 3573020731107278832586255)
                      ·
                        rfl

theorem cell23_6958433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_6958433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958433 prefixEnd_6958433 := by exact prefixLift 6958433
  have htrace : WordTrace (prefixWord ++ tailWord_6958433) baseStart_6958433 baseEnd_6958433 := by
    simpa [prefixWord, tailWord_6958433, baseEnd_6958433] using wordTrace_append hprefix tailTrace_6958433
  have hstable : (prefixWord ++ tailWord_6958433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958433).length < 2 ^ (prefixWord ++ tailWord_6958433).sum := by decide
  have hdescent : baseEnd_6958433 < baseStart_6958433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958460 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_6958460 : Nat := 118140960795 + 6958460 * 2 ^ 59
def prefixEnd_6958460 : Nat := 4983230072969 + 3 ^ 40 * 6958460 * 2
def baseEnd_6958460 : Nat := 1191011531694983408982877

theorem tailTrace_6958460 : CollatzResearch.WordTrace tailWord_6958460 prefixEnd_6958460 1191011531694983408982877 := by
  unfold tailWord_6958460
  simp only [CollatzResearch.WordTrace]
  refine ⟨126897943185347652599464417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169197257580463536799285889 126897943185347652599464417)
  ·
    refine ⟨95173457389010739449598313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126897943185347652599464417 95173457389010739449598313)
    ·
      refine ⟨71380093041758054587198735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95173457389010739449598313 71380093041758054587198735)
      ·
        refine ⟨107070139562637081880798103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71380093041758054587198735 107070139562637081880798103)
        ·
          refine ⟨160605209343955622821197155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107070139562637081880798103 160605209343955622821197155)
          ·
            refine ⟨240907814015933434231795733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160605209343955622821197155 240907814015933434231795733)
            ·
              refine ⟨11292553781996879729615425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240907814015933434231795733 11292553781996879729615425)
              ·
                refine ⟨8469415336497659797211569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11292553781996879729615425 8469415336497659797211569)
                ·
                  refine ⟨6352061502373244847908677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469415336497659797211569 6352061502373244847908677)
                  ·
                    refine ⟨1191011531694983408982877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352061502373244847908677 1191011531694983408982877)
                    ·
                      rfl

theorem cell23_6958460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_6958460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958460 prefixEnd_6958460 := by exact prefixLift 6958460
  have htrace : WordTrace (prefixWord ++ tailWord_6958460) baseStart_6958460 baseEnd_6958460 := by
    simpa [prefixWord, tailWord_6958460, baseEnd_6958460] using wordTrace_append hprefix tailTrace_6958460
  have hstable : (prefixWord ++ tailWord_6958460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958460).length < 2 ^ (prefixWord ++ tailWord_6958460).sum := by decide
  have hdescent : baseEnd_6958460 < baseStart_6958460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958484 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6958484 : Nat := 118140960795 + 6958484 * 2 ^ 59
def prefixEnd_6958484 : Nat := 4983230072969 + 3 ^ 40 * 6958484 * 2
def baseEnd_6958484 : Nat := 3573046918620658133048521

theorem tailTrace_6958484 : CollatzResearch.WordTrace tailWord_6958484 prefixEnd_6958484 3573046918620658133048521 := by
  unfold tailWord_6958484
  simp only [CollatzResearch.WordTrace]
  refine ⟨126898380861304178648901253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169197841148405571531868337 126898380861304178648901253)
  ·
    refine ⟨23793446411494533496668985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126898380861304178648901253 23793446411494533496668985)
    ·
      refine ⟨17845084808620900122501739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23793446411494533496668985 17845084808620900122501739)
      ·
        refine ⟨26767627212931350183752609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845084808620900122501739 26767627212931350183752609)
        ·
          refine ⟨20075720409698512637814457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26767627212931350183752609 20075720409698512637814457)
          ·
            refine ⟨15056790307273884478360843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20075720409698512637814457 15056790307273884478360843)
            ·
              refine ⟨22585185460910826717541265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056790307273884478360843 22585185460910826717541265)
              ·
                refine ⟨16938889095683120038155949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22585185460910826717541265 16938889095683120038155949)
                ·
                  refine ⟨6352083410881170014308481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16938889095683120038155949 6352083410881170014308481)
                  ·
                    refine ⟨4764062558160877510731361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352083410881170014308481 4764062558160877510731361)
                    ·
                      refine ⟨3573046918620658133048521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764062558160877510731361 3573046918620658133048521)
                      ·
                        rfl

theorem cell23_6958484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6958484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958484 prefixEnd_6958484 := by exact prefixLift 6958484
  have htrace : WordTrace (prefixWord ++ tailWord_6958484) baseStart_6958484 baseEnd_6958484 := by
    simpa [prefixWord, tailWord_6958484, baseEnd_6958484] using wordTrace_append hprefix tailTrace_6958484
  have hstable : (prefixWord ++ tailWord_6958484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958484).length < 2 ^ (prefixWord ++ tailWord_6958484).sum := by decide
  have hdescent : baseEnd_6958484 < baseStart_6958484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958500 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_6958500 : Nat := 118140960795 + 6958500 * 2 ^ 59
def prefixEnd_6958500 : Nat := 4983230072969 + 3 ^ 40 * 6958500 * 2
def baseEnd_6958500 : Nat := 3573055134311130070448447

theorem tailTrace_6958500 : CollatzResearch.WordTrace tailWord_6958500 prefixEnd_6958500 3573055134311130070448447 := by
  unfold tailWord_6958500
  simp only [CollatzResearch.WordTrace]
  refine ⟨126898672645275196015192477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169198230193700261353589969 126898672645275196015192477)
  ·
    refine ⟨47587002241978198505697179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126898672645275196015192477 47587002241978198505697179)
    ·
      refine ⟨71380503362967297758545769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47587002241978198505697179 71380503362967297758545769)
      ·
        refine ⟨53535377522225473318909327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71380503362967297758545769 53535377522225473318909327)
        ·
          refine ⟨80303066283338209978363991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53535377522225473318909327 80303066283338209978363991)
          ·
            refine ⟨120454599425007314967545987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80303066283338209978363991 120454599425007314967545987)
            ·
              refine ⟨180681899137510972451318981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120454599425007314967545987 180681899137510972451318981)
              ·
                refine ⟨33877856088283307334622309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180681899137510972451318981 33877856088283307334622309)
                ·
                  refine ⟨6352098016553120125241683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33877856088283307334622309 6352098016553120125241683)
                  ·
                    refine ⟨9528147024829680187862525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352098016553120125241683 9528147024829680187862525)
                    ·
                      refine ⟨3573055134311130070448447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528147024829680187862525 3573055134311130070448447)
                      ·
                        rfl

theorem cell23_6958500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_6958500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958500 prefixEnd_6958500 := by exact prefixLift 6958500
  have htrace : WordTrace (prefixWord ++ tailWord_6958500) baseStart_6958500 baseEnd_6958500 := by
    simpa [prefixWord, tailWord_6958500, baseEnd_6958500] using wordTrace_append hprefix tailTrace_6958500
  have hstable : (prefixWord ++ tailWord_6958500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958500).length < 2 ^ (prefixWord ++ tailWord_6958500).sum := by decide
  have hdescent : baseEnd_6958500 < baseStart_6958500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958504 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6958504 : Nat := 118140960795 + 6958504 * 2 ^ 59
def prefixEnd_6958504 : Nat := 4983230072969 + 3 ^ 40 * 6958504 * 2
def baseEnd_6958504 : Nat := 3573057188233748054798429

theorem tailTrace_6958504 : CollatzResearch.WordTrace tailWord_6958504 prefixEnd_6958504 3573057188233748054798429 := by
  unfold tailWord_6958504
  simp only [CollatzResearch.WordTrace]
  refine ⟨126898745591267950356765283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169198327455023933809020377 126898745591267950356765283)
  ·
    refine ⟨190348118386901925535147925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126898745591267950356765283 190348118386901925535147925)
    ·
      refine ⟨8922568049386027759460059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190348118386901925535147925 8922568049386027759460059)
      ·
        refine ⟨13383852074079041639190089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922568049386027759460059 13383852074079041639190089)
        ·
          refine ⟨10037889055559281229392567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13383852074079041639190089 10037889055559281229392567)
          ·
            refine ⟨15056833583338921844088851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10037889055559281229392567 15056833583338921844088851)
            ·
              refine ⟨22585250375008382766133277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056833583338921844088851 22585250375008382766133277)
              ·
                refine ⟨8469468890628143537299979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22585250375008382766133277 8469468890628143537299979)
                ·
                  refine ⟨12704203335942215305949969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8469468890628143537299979 12704203335942215305949969)
                  ·
                    refine ⟨9528152501956661479462477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12704203335942215305949969 9528152501956661479462477)
                    ·
                      refine ⟨3573057188233748054798429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528152501956661479462477 3573057188233748054798429)
                      ·
                        rfl

theorem cell23_6958504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6958504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958504 prefixEnd_6958504 := by exact prefixLift 6958504
  have htrace : WordTrace (prefixWord ++ tailWord_6958504) baseStart_6958504 baseEnd_6958504 := by
    simpa [prefixWord, tailWord_6958504, baseEnd_6958504] using wordTrace_append hprefix tailTrace_6958504
  have hstable : (prefixWord ++ tailWord_6958504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958504).length < 2 ^ (prefixWord ++ tailWord_6958504).sum := by decide
  have hdescent : baseEnd_6958504 < baseStart_6958504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958517 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_6958517 : Nat := 118140960795 + 6958517 * 2 ^ 59
def prefixEnd_6958517 : Nat := 4983230072969 + 3 ^ 40 * 6958517 * 2
def baseEnd_6958517 : Nat := 3573063863482256503935869

theorem tailTrace_6958517 : CollatzResearch.WordTrace tailWord_6958517 prefixEnd_6958517 3573063863482256503935869 := by
  unfold tailWord_6958517
  simp only [CollatzResearch.WordTrace]
  refine ⟨253797965331488803933753805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169198643554325869289169203 253797965331488803933753805)
  ·
    refine ⟨95174236999308301475157677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253797965331488803933753805 95174236999308301475157677)
    ·
      refine ⟨35690338874740613053184129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95174236999308301475157677 35690338874740613053184129)
      ·
        refine ⟨26767754156055459789888097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35690338874740613053184129 26767754156055459789888097)
        ·
          refine ⟨20075815617041594842416073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26767754156055459789888097 20075815617041594842416073)
          ·
            refine ⟨15056861712781196131812055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20075815617041594842416073 15056861712781196131812055)
            ·
              refine ⟨22585292569171794197718083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15056861712781196131812055 22585292569171794197718083)
              ·
                refine ⟨33877938853757691296577125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22585292569171794197718083 33877938853757691296577125)
                ·
                  refine ⟨6352113535079567118108211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33877938853757691296577125 6352113535079567118108211)
                  ·
                    refine ⟨9528170302619350677162317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352113535079567118108211 9528170302619350677162317)
                    ·
                      refine ⟨3573063863482256503935869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528170302619350677162317 3573063863482256503935869)
                      ·
                        rfl

theorem cell23_6958517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_6958517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958517 prefixEnd_6958517 := by exact prefixLift 6958517
  have htrace : WordTrace (prefixWord ++ tailWord_6958517) baseStart_6958517 baseEnd_6958517 := by
    simpa [prefixWord, tailWord_6958517, baseEnd_6958517] using wordTrace_append hprefix tailTrace_6958517
  have hstable : (prefixWord ++ tailWord_6958517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958517).length < 2 ^ (prefixWord ++ tailWord_6958517).sum := by decide
  have hdescent : baseEnd_6958517 < baseStart_6958517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958543 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_6958543 : Nat := 118140960795 + 6958543 * 2 ^ 59
def prefixEnd_6958543 : Nat := 4983230072969 + 3 ^ 40 * 6958543 * 2
def baseEnd_6958543 : Nat := 3573077213979273402210749

theorem tailTrace_6958543 : CollatzResearch.WordTrace tailWord_6958543 prefixEnd_6958543 3573077213979273402210749 := by
  unfold tailWord_6958543
  simp only [CollatzResearch.WordTrace]
  refine ⟨253798913629394610374200283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169199275752929740249466855 253798913629394610374200283)
  ·
    refine ⟨380698370444091915561300425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253798913629394610374200283 380698370444091915561300425)
    ·
      refine ⟨285523777833068936670975319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380698370444091915561300425 285523777833068936670975319)
      ·
        refine ⟨428285666749603405006462979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285523777833068936670975319 428285666749603405006462979)
        ·
          refine ⟨642428500124405107509694469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428285666749603405006462979 642428500124405107509694469)
          ·
            refine ⟨120455343773325957658067713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 642428500124405107509694469 120455343773325957658067713)
            ·
              refine ⟨90341507829994468243550785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120455343773325957658067713 90341507829994468243550785)
              ·
                refine ⟨67756130872495851182663089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90341507829994468243550785 67756130872495851182663089)
                ·
                  refine ⟨50817098154371888386997317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67756130872495851182663089 50817098154371888386997317)
                  ·
                    refine ⟨9528205903944729072561997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50817098154371888386997317 9528205903944729072561997)
                    ·
                      refine ⟨3573077213979273402210749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528205903944729072561997 3573077213979273402210749)
                      ·
                        rfl

theorem cell23_6958543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_6958543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958543 prefixEnd_6958543 := by exact prefixLift 6958543
  have htrace : WordTrace (prefixWord ++ tailWord_6958543) baseStart_6958543 baseEnd_6958543 := by
    simpa [prefixWord, tailWord_6958543, baseEnd_6958543] using wordTrace_append hprefix tailTrace_6958543
  have hstable : (prefixWord ++ tailWord_6958543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958543).length < 2 ^ (prefixWord ++ tailWord_6958543).sum := by decide
  have hdescent : baseEnd_6958543 < baseStart_6958543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958574 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_6958574 : Nat := 118140960795 + 6958574 * 2 ^ 59
def prefixEnd_6958574 : Nat := 4983230072969 + 3 ^ 40 * 6958574 * 2
def baseEnd_6958574 : Nat := 3573093131879562780923107

theorem tailTrace_6958574 : CollatzResearch.WordTrace tailWord_6958574 prefixEnd_6958574 3573093131879562780923107 := by
  unfold tailWord_6958574
  simp only [CollatzResearch.WordTrace]
  refine ⟨31725005536535287833572347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169200029528188201779052517 31725005536535287833572347)
  ·
    refine ⟨47587508304802931750358521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31725005536535287833572347 47587508304802931750358521)
    ·
      refine ⟨35690631228602198812768891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47587508304802931750358521 35690631228602198812768891)
      ·
        refine ⟨53535946842903298219153337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35690631228602198812768891 53535946842903298219153337)
        ·
          refine ⟨40151960132177473664365003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53535946842903298219153337 40151960132177473664365003)
          ·
            refine ⟨60227940198266210496547505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40151960132177473664365003 60227940198266210496547505)
            ·
              refine ⟨45170955148699657872410629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60227940198266210496547505 45170955148699657872410629)
              ·
                refine ⟨8469554090381185851076993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45170955148699657872410629 8469554090381185851076993)
                ·
                  refine ⟨6352165567785889388307745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469554090381185851076993 6352165567785889388307745)
                  ·
                    refine ⟨4764124175839417041230809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352165567785889388307745 4764124175839417041230809)
                    ·
                      refine ⟨3573093131879562780923107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764124175839417041230809 3573093131879562780923107)
                      ·
                        rfl

theorem cell23_6958574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_6958574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958574 prefixEnd_6958574 := by exact prefixLift 6958574
  have htrace : WordTrace (prefixWord ++ tailWord_6958574) baseStart_6958574 baseEnd_6958574 := by
    simpa [prefixWord, tailWord_6958574, baseEnd_6958574] using wordTrace_append hprefix tailTrace_6958574
  have hstable : (prefixWord ++ tailWord_6958574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958574).length < 2 ^ (prefixWord ++ tailWord_6958574).sum := by decide
  have hdescent : baseEnd_6958574 < baseStart_6958574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958640 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 3, 4]
def baseStart_6958640 : Nat := 118140960795 + 6958640 * 2 ^ 59
def prefixEnd_6958640 : Nat := 4983230072969 + 3 ^ 40 * 6958640 * 2
def baseEnd_6958640 : Nat := 1191042340534253174232601

theorem tailTrace_6958640 : CollatzResearch.WordTrace tailWord_6958640 prefixEnd_6958640 1191042340534253174232601 := by
  unfold tailWord_6958640
  simp only [CollatzResearch.WordTrace]
  refine ⟨126901225755021597970240687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169201634340028797293654249 126901225755021597970240687)
  ·
    refine ⟨190351838632532396955361031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126901225755021597970240687 190351838632532396955361031)
    ·
      refine ⟨285527757948798595433041547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190351838632532396955361031 285527757948798595433041547)
      ·
        refine ⟨428291636923197893149562321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285527757948798595433041547 428291636923197893149562321)
        ·
          refine ⟨321218727692398419862171741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428291636923197893149562321 321218727692398419862171741)
          ·
            refine ⟨120457022884649407448314403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321218727692398419862171741 120457022884649407448314403)
            ·
              refine ⟨180685534326974111172471605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120457022884649407448314403 180685534326974111172471605)
              ·
                refine ⟨16939268843153822922419213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180685534326974111172471605 16939268843153822922419213)
                ·
                  refine ⟨6352225816182683595907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16939268843153822922419213 6352225816182683595907205)
                  ·
                    refine ⟨1191042340534253174232601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352225816182683595907205 1191042340534253174232601)
                    ·
                      rfl

theorem cell23_6958640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_6958640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958640 prefixEnd_6958640 := by exact prefixLift 6958640
  have htrace : WordTrace (prefixWord ++ tailWord_6958640) baseStart_6958640 baseEnd_6958640 := by
    simpa [prefixWord, tailWord_6958640, baseEnd_6958640] using wordTrace_append hprefix tailTrace_6958640
  have hstable : (prefixWord ++ tailWord_6958640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958640).length < 2 ^ (prefixWord ++ tailWord_6958640).sum := by decide
  have hdescent : baseEnd_6958640 < baseStart_6958640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958647 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 2, 4, 2]
def baseStart_6958647 : Nat := 118140960795 + 6958647 * 2 ^ 59
def prefixEnd_6958647 : Nat := 4983230072969 + 3 ^ 40 * 6958647 * 2
def baseEnd_6958647 : Nat := 3573130615967340995310271

theorem tailTrace_6958647 : CollatzResearch.WordTrace tailWord_6958647 prefixEnd_6958647 3573130615967340995310271 := by
  unfold tailWord_6958647
  simp only [CollatzResearch.WordTrace]
  refine ⟨253802706821017836135986195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169201804547345224090657463 253802706821017836135986195)
  ·
    refine ⟨380704060231526754203979293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253802706821017836135986195 380704060231526754203979293)
    ·
      refine ⟨142764022586822532826492235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380704060231526754203979293 142764022586822532826492235)
      ·
        refine ⟨214146033880233799239738353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142764022586822532826492235 214146033880233799239738353)
        ·
          refine ⟨160609525410175349429803765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214146033880233799239738353 160609525410175349429803765)
          ·
            refine ⟨15057143007203939009044103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160609525410175349429803765 15057143007203939009044103)
            ·
              refine ⟨22585714510805908513566155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15057143007203939009044103 22585714510805908513566155)
              ·
                refine ⟨33878571766208862770349233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22585714510805908513566155 33878571766208862770349233)
                ·
                  refine ⟨25408928824656647077761925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33878571766208862770349233 25408928824656647077761925)
                  ·
                    refine ⟨4764174154623121327080361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25408928824656647077761925 4764174154623121327080361)
                    ·
                      refine ⟨3573130615967340995310271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764174154623121327080361 3573130615967340995310271)
                      ·
                        rfl

theorem cell23_6958647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_6958647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958647 prefixEnd_6958647 := by exact prefixLift 6958647
  have htrace : WordTrace (prefixWord ++ tailWord_6958647) baseStart_6958647 baseEnd_6958647 := by
    simpa [prefixWord, tailWord_6958647, baseEnd_6958647] using wordTrace_append hprefix tailTrace_6958647
  have hstable : (prefixWord ++ tailWord_6958647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958647).length < 2 ^ (prefixWord ++ tailWord_6958647).sum := by decide
  have hdescent : baseEnd_6958647 < baseStart_6958647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958650 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_6958650 : Nat := 118140960795 + 6958650 * 2 ^ 59
def prefixEnd_6958650 : Nat := 4983230072969 + 3 ^ 40 * 6958650 * 2
def baseEnd_6958650 : Nat := 3573132156409304483572757

theorem tailTrace_6958650 : CollatzResearch.WordTrace tailWord_6958650 prefixEnd_6958650 3573132156409304483572757 := by
  unfold tailWord_6958650
  simp only [CollatzResearch.WordTrace]
  refine ⟨63450704060001741912086351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169201877493337978432230269 63450704060001741912086351)
  ·
    refine ⟨95176056090002612868129527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63450704060001741912086351 95176056090002612868129527)
    ·
      refine ⟨142764084135003919302194291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95176056090002612868129527 142764084135003919302194291)
      ·
        refine ⟨214146126202505878953291437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142764084135003919302194291 214146126202505878953291437)
        ·
          refine ⟨80304797325939704607484289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214146126202505878953291437 80304797325939704607484289)
          ·
            refine ⟨60228597994454778455613217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80304797325939704607484289 60228597994454778455613217)
            ·
              refine ⟨45171448495841083841709913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60228597994454778455613217 45171448495841083841709913)
              ·
                refine ⟨33878586371880812881282435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45171448495841083841709913 33878586371880812881282435)
                ·
                  refine ⟨50817879557821219321923653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33878586371880812881282435 50817879557821219321923653)
                  ·
                    refine ⟨9528352417091478622860685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50817879557821219321923653 9528352417091478622860685)
                    ·
                      refine ⟨3573132156409304483572757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528352417091478622860685 3573132156409304483572757)
                      ·
                        rfl

theorem cell23_6958650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_6958650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958650 prefixEnd_6958650 := by exact prefixLift 6958650
  have htrace : WordTrace (prefixWord ++ tailWord_6958650) baseStart_6958650 baseEnd_6958650 := by
    simpa [prefixWord, tailWord_6958650, baseEnd_6958650] using wordTrace_append hprefix tailTrace_6958650
  have hstable : (prefixWord ++ tailWord_6958650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958650).length < 2 ^ (prefixWord ++ tailWord_6958650).sum := by decide
  have hdescent : baseEnd_6958650 < baseStart_6958650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958657 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 3, 4]
def baseStart_6958657 : Nat := 118140960795 + 6958657 * 2 ^ 59
def prefixEnd_6958657 : Nat := 4983230072969 + 3 ^ 40 * 6958657 * 2
def baseEnd_6958657 : Nat := 1191045250257961985395075

theorem tailTrace_6958657 : CollatzResearch.WordTrace tailWord_6958657 prefixEnd_6958657 1191045250257961985395075 := by
  unfold tailWord_6958657
  simp only [CollatzResearch.WordTrace]
  refine ⟨253803071550981607843850225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169202047700654405229233483 253803071550981607843850225)
  ·
    refine ⟨190352303663236205882887669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253803071550981607843850225 190352303663236205882887669)
    ·
      refine ⟨17845528468428394301520719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190352303663236205882887669 17845528468428394301520719)
      ·
        refine ⟨26768292702642591452281079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845528468428394301520719 26768292702642591452281079)
        ·
          refine ⟨40152439053963887178421619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26768292702642591452281079 40152439053963887178421619)
          ·
            refine ⟨60228658580945830767632429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40152439053963887178421619 60228658580945830767632429)
            ·
              refine ⟨22585746967854686537862161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60228658580945830767632429 22585746967854686537862161)
              ·
                refine ⟨16939310225891014903396621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22585746967854686537862161 16939310225891014903396621)
                ·
                  refine ⟨6352241334709130588773733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16939310225891014903396621 6352241334709130588773733)
                  ·
                    refine ⟨1191045250257961985395075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352241334709130588773733 1191045250257961985395075)
                    ·
                      rfl

theorem cell23_6958657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_6958657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958657 prefixEnd_6958657 := by exact prefixLift 6958657
  have htrace : WordTrace (prefixWord ++ tailWord_6958657) baseStart_6958657 baseEnd_6958657 := by
    simpa [prefixWord, tailWord_6958657, baseEnd_6958657] using wordTrace_append hprefix tailTrace_6958657
  have hstable : (prefixWord ++ tailWord_6958657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958657).length < 2 ^ (prefixWord ++ tailWord_6958657).sum := by decide
  have hdescent : baseEnd_6958657 < baseStart_6958657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958674 : List Nat := [3, 2, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_6958674 : Nat := 118140960795 + 6958674 * 2 ^ 59
def prefixEnd_6958674 : Nat := 4983230072969 + 3 ^ 40 * 6958674 * 2
def baseEnd_6958674 : Nat := 1191048159981670796557549

theorem tailTrace_6958674 : CollatzResearch.WordTrace tailWord_6958674 prefixEnd_6958674 1191048159981670796557549 := by
  unfold tailWord_6958674
  simp only [CollatzResearch.WordTrace]
  refine ⟨63450922897980004936804769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169202461061280013164812717 63450922897980004936804769)
  ·
    refine ⟨47588192173485003702603577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63450922897980004936804769 47588192173485003702603577)
    ·
      refine ⟨35691144130113752776952683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47588192173485003702603577 35691144130113752776952683)
      ·
        refine ⟨53536716195170629165429025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35691144130113752776952683 53536716195170629165429025)
        ·
          refine ⟨40152537146377971874071769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53536716195170629165429025 40152537146377971874071769)
          ·
            refine ⟨30114402859783478905553827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40152537146377971874071769 30114402859783478905553827)
            ·
              refine ⟨45171604289675218358330741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30114402859783478905553827 45171604289675218358330741)
              ·
                refine ⟨4234837902157051721093507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45171604289675218358330741 4234837902157051721093507)
                ·
                  refine ⟨6352256853235577581640261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234837902157051721093507 6352256853235577581640261)
                  ·
                    refine ⟨1191048159981670796557549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352256853235577581640261 1191048159981670796557549)
                    ·
                      rfl

theorem cell23_6958674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_6958674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958674 prefixEnd_6958674 := by exact prefixLift 6958674
  have htrace : WordTrace (prefixWord ++ tailWord_6958674) baseStart_6958674 baseEnd_6958674 := by
    simpa [prefixWord, tailWord_6958674, baseEnd_6958674] using wordTrace_append hprefix tailTrace_6958674
  have hstable : (prefixWord ++ tailWord_6958674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958674).length < 2 ^ (prefixWord ++ tailWord_6958674).sum := by decide
  have hdescent : baseEnd_6958674 < baseStart_6958674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958697 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 3]
def baseStart_6958697 : Nat := 118140960795 + 6958697 * 2 ^ 59
def prefixEnd_6958697 : Nat := 4983230072969 + 3 ^ 40 * 6958697 * 2
def baseEnd_6958697 : Nat := 3573156290000065799685041

theorem tailTrace_6958697 : CollatzResearch.WordTrace tailWord_6958697 prefixEnd_6958697 3573156290000065799685041 := by
  unfold tailWord_6958697
  simp only [CollatzResearch.WordTrace]
  refine ⟨253804530470836694675306345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169203020313891129783537563 253804530470836694675306345)
  ·
    refine ⟨190353397853127521006479759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253804530470836694675306345 190353397853127521006479759)
    ·
      refine ⟨285530096779691281509719639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190353397853127521006479759 285530096779691281509719639)
      ·
        refine ⟨428295145169536922264579459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285530096779691281509719639 428295145169536922264579459)
        ·
          refine ⟨642442717754305383396869189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428295145169536922264579459 642442717754305383396869189)
          ·
            refine ⟨120458009578932259386912973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 642442717754305383396869189 120458009578932259386912973)
            ·
              refine ⟨45171753592099597270092365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120458009578932259386912973 45171753592099597270092365)
              ·
                refine ⟨16939407597037348976284637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45171753592099597270092365 16939407597037348976284637)
                ·
                  refine ⟨6352277848889005866106739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16939407597037348976284637 6352277848889005866106739)
                  ·
                    refine ⟨9528416773333508799160109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352277848889005866106739 9528416773333508799160109)
                    ·
                      refine ⟨3573156290000065799685041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528416773333508799160109 3573156290000065799685041)
                      ·
                        rfl

theorem cell23_6958697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 3].length) (baseStart_6958697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958697 prefixEnd_6958697 := by exact prefixLift 6958697
  have htrace : WordTrace (prefixWord ++ tailWord_6958697) baseStart_6958697 baseEnd_6958697 := by
    simpa [prefixWord, tailWord_6958697, baseEnd_6958697] using wordTrace_append hprefix tailTrace_6958697
  have hstable : (prefixWord ++ tailWord_6958697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958697).length < 2 ^ (prefixWord ++ tailWord_6958697).sum := by decide
  have hdescent : baseEnd_6958697 < baseStart_6958697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958717 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_6958717 : Nat := 118140960795 + 6958717 * 2 ^ 59
def prefixEnd_6958717 : Nat := 4983230072969 + 3 ^ 40 * 6958717 * 2
def baseEnd_6958717 : Nat := 1191055519871051907144983

theorem tailTrace_6958717 : CollatzResearch.WordTrace tailWord_6958717 prefixEnd_6958717 1191055519871051907144983 := by
  unfold tailWord_6958717
  simp only [CollatzResearch.WordTrace]
  refine ⟨253805259930764238091034405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169203506620509492060689603 253805259930764238091034405)
  ·
    refine ⟨47588486237018294642068951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253805259930764238091034405 47588486237018294642068951)
    ·
      refine ⟨71382729355527441963103427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47588486237018294642068951 71382729355527441963103427)
      ·
        refine ⟨107074094033291162944655141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71382729355527441963103427 107074094033291162944655141)
        ·
          refine ⟨20076392631242093052122839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107074094033291162944655141 20076392631242093052122839)
          ·
            refine ⟨30114588946863139578184259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20076392631242093052122839 30114588946863139578184259)
            ·
              refine ⟨45171883420294709367276389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30114588946863139578184259 45171883420294709367276389)
              ·
                refine ⟨8469728141305258006364323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45171883420294709367276389 8469728141305258006364323)
                ·
                  refine ⟨12704592211957887009546485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8469728141305258006364323 12704592211957887009546485)
                  ·
                    refine ⟨1191055519871051907144983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12704592211957887009546485 1191055519871051907144983)
                    ·
                      rfl

theorem cell23_6958717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_6958717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958717 prefixEnd_6958717 := by exact prefixLift 6958717
  have htrace : WordTrace (prefixWord ++ tailWord_6958717) baseStart_6958717 baseEnd_6958717 := by
    simpa [prefixWord, tailWord_6958717, baseEnd_6958717] using wordTrace_append hprefix tailTrace_6958717
  have hstable : (prefixWord ++ tailWord_6958717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958717).length < 2 ^ (prefixWord ++ tailWord_6958717).sum := by decide
  have hdescent : baseEnd_6958717 < baseStart_6958717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958748 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6958748 : Nat := 118140960795 + 6958748 * 2 ^ 59
def prefixEnd_6958748 : Nat := 4983230072969 + 3 ^ 40 * 6958748 * 2
def baseEnd_6958748 : Nat := 3573182477513445100147307

theorem tailTrace_6958748 : CollatzResearch.WordTrace tailWord_6958748 prefixEnd_6958748 3573182477513445100147307 := by
  unfold tailWord_6958748
  simp only [CollatzResearch.WordTrace]
  refine ⟨126903195296825965192706449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169204260395767953590275265 126903195296825965192706449)
  ·
    refine ⟨95177396472619473894529837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126903195296825965192706449 95177396472619473894529837)
    ·
      refine ⟨35691523677232302710448689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95177396472619473894529837 35691523677232302710448689)
      ·
        refine ⟨26768642757924227032836517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35691523677232302710448689 26768642757924227032836517)
        ·
          refine ⟨5019120517110792568656847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26768642757924227032836517 5019120517110792568656847)
          ·
            refine ⟨7528680775666188852985271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019120517110792568656847 7528680775666188852985271)
            ·
              refine ⟨11293021163499283279477907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528680775666188852985271 11293021163499283279477907)
              ·
                refine ⟨16939531745248924919216861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293021163499283279477907 16939531745248924919216861)
                ·
                  refine ⟨6352324404468346844706323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16939531745248924919216861 6352324404468346844706323)
                  ·
                    refine ⟨9528486606702520267059485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352324404468346844706323 9528486606702520267059485)
                    ·
                      refine ⟨3573182477513445100147307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528486606702520267059485 3573182477513445100147307)
                      ·
                        rfl

theorem cell23_6958748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6958748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958748 prefixEnd_6958748 := by exact prefixLift 6958748
  have htrace : WordTrace (prefixWord ++ tailWord_6958748) baseStart_6958748 baseEnd_6958748 := by
    simpa [prefixWord, tailWord_6958748, baseEnd_6958748] using wordTrace_append hprefix tailTrace_6958748
  have hstable : (prefixWord ++ tailWord_6958748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958748).length < 2 ^ (prefixWord ++ tailWord_6958748).sum := by decide
  have hdescent : baseEnd_6958748 < baseStart_6958748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958788 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_6958788 : Nat := 118140960795 + 6958788 * 2 ^ 59
def prefixEnd_6958788 : Nat := 4983230072969 + 3 ^ 40 * 6958788 * 2
def baseEnd_6958788 : Nat := 3573203016739624943647123

theorem tailTrace_6958788 : CollatzResearch.WordTrace tailWord_6958788 prefixEnd_6958788 3573203016739624943647123 := by
  unfold tailWord_6958788
  simp only [CollatzResearch.WordTrace]
  refine ⟨126903924756753508608434509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169205233009004678144579345 126903924756753508608434509)
  ·
    refine ⟨47588971783782565728162941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126903924756753508608434509 47588971783782565728162941)
    ·
      refine ⟨17845864418918462148061103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47588971783782565728162941 17845864418918462148061103)
      ·
        refine ⟨26768796628377693222091655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845864418918462148061103 26768796628377693222091655)
        ·
          refine ⟨40153194942566539833137483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26768796628377693222091655 40153194942566539833137483)
          ·
            refine ⟨60229792413849809749706225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40153194942566539833137483 60229792413849809749706225)
            ·
              refine ⟨45172344310387357312279669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60229792413849809749706225 45172344310387357312279669)
              ·
                refine ⟨4234907279098814748026219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45172344310387357312279669 4234907279098814748026219)
                ·
                  refine ⟨6352360918648222122039329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4234907279098814748026219 6352360918648222122039329)
                  ·
                    refine ⟨4764270688986166591529497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352360918648222122039329 4764270688986166591529497)
                    ·
                      refine ⟨3573203016739624943647123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764270688986166591529497 3573203016739624943647123)
                      ·
                        rfl

theorem cell23_6958788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_6958788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958788 prefixEnd_6958788 := by exact prefixLift 6958788
  have htrace : WordTrace (prefixWord ++ tailWord_6958788) baseStart_6958788 baseEnd_6958788 := by
    simpa [prefixWord, tailWord_6958788, baseEnd_6958788] using wordTrace_append hprefix tailTrace_6958788
  have hstable : (prefixWord ++ tailWord_6958788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958788).length < 2 ^ (prefixWord ++ tailWord_6958788).sum := by decide
  have hdescent : baseEnd_6958788 < baseStart_6958788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958844 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_6958844 : Nat := 118140960795 + 6958844 * 2 ^ 59
def prefixEnd_6958844 : Nat := 4983230072969 + 3 ^ 40 * 6958844 * 2
def baseEnd_6958844 : Nat := 3573231771656276724546865

theorem tailTrace_6958844 : CollatzResearch.WordTrace tailWord_6958844 prefixEnd_6958844 3573231771656276724546865 := by
  unfold tailWord_6958844
  simp only [CollatzResearch.WordTrace]
  refine ⟨126904946000652069390453793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169206594667536092520605057 126904946000652069390453793)
  ·
    refine ⟨95178709500489052042840345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126904946000652069390453793 95178709500489052042840345)
    ·
      refine ⟨71384032125366789032130259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95178709500489052042840345 71384032125366789032130259)
      ·
        refine ⟨107076048188050183548195389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71384032125366789032130259 107076048188050183548195389)
        ·
          refine ⟨40153518070518818830573271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107076048188050183548195389 40153518070518818830573271)
          ·
            refine ⟨60230277105778228245859907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40153518070518818830573271 60230277105778228245859907)
            ·
              refine ⟨90345415658667342368789861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60230277105778228245859907 90345415658667342368789861)
              ·
                refine ⟨16939765436000126694148099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90345415658667342368789861 16939765436000126694148099)
                ·
                  refine ⟨25409648154000190041222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16939765436000126694148099 25409648154000190041222149)
                  ·
                    refine ⟨4764309028875035632729153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25409648154000190041222149 4764309028875035632729153)
                    ·
                      refine ⟨3573231771656276724546865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764309028875035632729153 3573231771656276724546865)
                      ·
                        rfl

theorem cell23_6958844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_6958844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958844 prefixEnd_6958844 := by exact prefixLift 6958844
  have htrace : WordTrace (prefixWord ++ tailWord_6958844) baseStart_6958844 baseEnd_6958844 := by
    simpa [prefixWord, tailWord_6958844, baseEnd_6958844] using wordTrace_append hprefix tailTrace_6958844
  have hstable : (prefixWord ++ tailWord_6958844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958844).length < 2 ^ (prefixWord ++ tailWord_6958844).sum := by decide
  have hdescent : baseEnd_6958844 < baseStart_6958844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958855 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6958855 : Nat := 118140960795 + 6958855 * 2 ^ 59
def prefixEnd_6958855 : Nat := 4983230072969 + 3 ^ 40 * 6958855 * 2
def baseEnd_6958855 : Nat := 3573237419943476181509315

theorem tailTrace_6958855 : CollatzResearch.WordTrace tailWord_6958855 prefixEnd_6958855 3573237419943476181509315 := by
  unfold tailWord_6958855
  simp only [CollatzResearch.WordTrace]
  refine ⟨253810293204264287659558019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169206862136176191773038679 253810293204264287659558019)
  ·
    refine ⟨380715439806396431489337029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253810293204264287659558019 380715439806396431489337029)
    ·
      refine ⟨71384144963699330904250693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380715439806396431489337029 71384144963699330904250693)
      ·
        refine ⟨13384527180693624544547005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71384144963699330904250693 13384527180693624544547005)
        ·
          refine ⟨5019197692760109204205127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13384527180693624544547005 5019197692760109204205127)
          ·
            refine ⟨7528796539140163806307691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019197692760109204205127 7528796539140163806307691)
            ·
              refine ⟨11293194808710245709461537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528796539140163806307691 11293194808710245709461537)
              ·
                refine ⟨8469896106532684282096153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11293194808710245709461537 8469896106532684282096153)
                ·
                  refine ⟨6352422079899513211572115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8469896106532684282096153 6352422079899513211572115)
                  ·
                    refine ⟨9528633119849269817358173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352422079899513211572115 9528633119849269817358173)
                    ·
                      refine ⟨3573237419943476181509315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528633119849269817358173 3573237419943476181509315)
                      ·
                        rfl

theorem cell23_6958855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6958855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958855 prefixEnd_6958855 := by exact prefixLift 6958855
  have htrace : WordTrace (prefixWord ++ tailWord_6958855) baseStart_6958855 baseEnd_6958855 := by
    simpa [prefixWord, tailWord_6958855, baseEnd_6958855] using wordTrace_append hprefix tailTrace_6958855
  have hstable : (prefixWord ++ tailWord_6958855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958855).length < 2 ^ (prefixWord ++ tailWord_6958855).sum := by decide
  have hdescent : baseEnd_6958855 < baseStart_6958855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958897 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 1, 7]
def baseStart_6958897 : Nat := 118140960795 + 6958897 * 2 ^ 59
def prefixEnd_6958897 : Nat := 4983230072969 + 3 ^ 40 * 6958897 * 2
def baseEnd_6958897 : Nat := 1191086328710321672394707

theorem tailTrace_6958897 : CollatzResearch.WordTrace tailWord_6958897 prefixEnd_6958897 1191086328710321672394707 := by
  unfold tailWord_6958897
  simp only [CollatzResearch.WordTrace]
  refine ⟨253811825070112128832586945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169207883380074752555057963 253811825070112128832586945)
  ·
    refine ⟨190358868802584096624440209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253811825070112128832586945 190358868802584096624440209)
    ·
      refine ⟨142769151601938072468330157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190358868802584096624440209 142769151601938072468330157)
      ·
        refine ⟨53538431850726777175623809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142769151601938072468330157 53538431850726777175623809)
        ·
          refine ⟨40153823888045082881717857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53538431850726777175623809 40153823888045082881717857)
          ·
            refine ⟨30115367916033812161288393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40153823888045082881717857 30115367916033812161288393)
            ·
              refine ⟨22586525937025359120966295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30115367916033812161288393 22586525937025359120966295)
              ·
                refine ⟨33879788905538038681449443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22586525937025359120966295 33879788905538038681449443)
                ·
                  refine ⟨50819683358307058022174165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33879788905538038681449443 50819683358307058022174165)
                  ·
                    refine ⟨1191086328710321672394707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50819683358307058022174165 1191086328710321672394707)
                    ·
                      rfl

theorem cell23_6958897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_6958897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958897 prefixEnd_6958897 := by exact prefixLift 6958897
  have htrace : WordTrace (prefixWord ++ tailWord_6958897) baseStart_6958897 baseEnd_6958897 := by
    simpa [prefixWord, tailWord_6958897, baseEnd_6958897] using wordTrace_append hprefix tailTrace_6958897
  have hstable : (prefixWord ++ tailWord_6958897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958897).length < 2 ^ (prefixWord ++ tailWord_6958897).sum := by decide
  have hdescent : baseEnd_6958897 < baseStart_6958897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958918 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_6958918 : Nat := 118140960795 + 6958918 * 2 ^ 59
def prefixEnd_6958918 : Nat := 4983230072969 + 3 ^ 40 * 6958918 * 2
def baseEnd_6958918 : Nat := 397029974358301048335725

theorem tailTrace_6958918 : CollatzResearch.WordTrace tailWord_6958918 prefixEnd_6958918 397029974358301048335725 := by
  unfold tailWord_6958918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931643468844876544346919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169208394002024032946067605 7931643468844876544346919)
  ·
    refine ⟨11897465203267314816520379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7931643468844876544346919 11897465203267314816520379)
    ·
      refine ⟨17846197804900972224780569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11897465203267314816520379 17846197804900972224780569)
      ·
        refine ⟨13384648353675729168585427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17846197804900972224780569 13384648353675729168585427)
        ·
          refine ⟨20076972530513593752878141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13384648353675729168585427 20076972530513593752878141)
          ·
            refine ⟨7528864698942597657329303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20076972530513593752878141 7528864698942597657329303)
            ·
              refine ⟨11293297048413896485993955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528864698942597657329303 11293297048413896485993955)
              ·
                refine ⟨16939945572620844728990933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293297048413896485993955 16939945572620844728990933)
                ·
                  refine ⟨397029974358301048335725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16939945572620844728990933 397029974358301048335725)
                  ·
                    rfl

theorem cell23_6958918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_6958918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958918 prefixEnd_6958918 := by exact prefixLift 6958918
  have htrace : WordTrace (prefixWord ++ tailWord_6958918) baseStart_6958918 baseEnd_6958918 := by
    simpa [prefixWord, tailWord_6958918, baseEnd_6958918] using wordTrace_append hprefix tailTrace_6958918
  have hstable : (prefixWord ++ tailWord_6958918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958918).length < 2 ^ (prefixWord ++ tailWord_6958918).sum := by decide
  have hdescent : baseEnd_6958918 < baseStart_6958918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958924 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_6958924 : Nat := 118140960795 + 6958924 * 2 ^ 59
def prefixEnd_6958924 : Nat := 4983230072969 + 3 ^ 40 * 6958924 * 2
def baseEnd_6958924 : Nat := 3573272850108636411546497

theorem tailTrace_6958924 : CollatzResearch.WordTrace tailWord_6958924 prefixEnd_6958924 3573272850108636411546497 := by
  unfold tailWord_6958924
  simp only [CollatzResearch.WordTrace]
  refine ⟨126906404920507156221909913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169208539894009541629213217 126906404920507156221909913)
  ·
    refine ⟨95179803690380367166432435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126906404920507156221909913 95179803690380367166432435)
    ·
      refine ⟨142769705535570550749648653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95179803690380367166432435 142769705535570550749648653)
      ·
        refine ⟨53538639575838956531118245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142769705535570550749648653 53538639575838956531118245)
        ·
          refine ⟨10038494920469804349584671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53538639575838956531118245 10038494920469804349584671)
          ·
            refine ⟨15057742380704706524377007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10038494920469804349584671 15057742380704706524377007)
            ·
              refine ⟨22586613571057059786565511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15057742380704706524377007 22586613571057059786565511)
              ·
                refine ⟨33879920356585589679848267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22586613571057059786565511 33879920356585589679848267)
                ·
                  refine ⟨50819880534878384519772401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33879920356585589679848267 50819880534878384519772401)
                  ·
                    refine ⟨38114910401158788389829301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50819880534878384519772401 38114910401158788389829301)
                    ·
                      refine ⟨3573272850108636411546497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38114910401158788389829301 3573272850108636411546497)
                      ·
                        rfl

theorem cell23_6958924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_6958924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958924 prefixEnd_6958924 := by exact prefixLift 6958924
  have htrace : WordTrace (prefixWord ++ tailWord_6958924) baseStart_6958924 baseEnd_6958924 := by
    simpa [prefixWord, tailWord_6958924, baseEnd_6958924] using wordTrace_append hprefix tailTrace_6958924
  have hstable : (prefixWord ++ tailWord_6958924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958924).length < 2 ^ (prefixWord ++ tailWord_6958924).sum := by decide
  have hdescent : baseEnd_6958924 < baseStart_6958924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958957 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 10]
def baseStart_6958957 : Nat := 118140960795 + 6958957 * 2 ^ 59
def prefixEnd_6958957 : Nat := 4983230072969 + 3 ^ 40 * 6958957 * 2
def baseEnd_6958957 : Nat := 397032199441137198048205

theorem tailTrace_6958957 : CollatzResearch.WordTrace tailWord_6958957 prefixEnd_6958957 397032199441137198048205 := by
  unfold tailWord_6958957
  simp only [CollatzResearch.WordTrace]
  refine ⟨253814013449894759079771125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169209342299929839386514083 253814013449894759079771125)
  ·
    refine ⟨23795063760927633663728543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253814013449894759079771125 23795063760927633663728543)
    ·
      refine ⟨35692595641391450495592815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23795063760927633663728543 35692595641391450495592815)
      ·
        refine ⟨53538893462087175743389223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35692595641391450495592815 53538893462087175743389223)
        ·
          refine ⟨80308340193130763615083835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53538893462087175743389223 80308340193130763615083835)
          ·
            refine ⟨120462510289696145422625753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80308340193130763615083835 120462510289696145422625753)
            ·
              refine ⟨90346882717272109066969315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120462510289696145422625753 90346882717272109066969315)
              ·
                refine ⟨135520324075908163600453973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90346882717272109066969315 135520324075908163600453973)
                ·
                  refine ⟨397032199441137198048205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 135520324075908163600453973 397032199441137198048205)
                  ·
                    rfl

theorem cell23_6958957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_6958957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958957 prefixEnd_6958957 := by exact prefixLift 6958957
  have htrace : WordTrace (prefixWord ++ tailWord_6958957) baseStart_6958957 baseEnd_6958957 := by
    simpa [prefixWord, tailWord_6958957, baseEnd_6958957] using wordTrace_append hprefix tailTrace_6958957
  have hstable : (prefixWord ++ tailWord_6958957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958957).length < 2 ^ (prefixWord ++ tailWord_6958957).sum := by decide
  have hdescent : baseEnd_6958957 < baseStart_6958957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958961 : List Nat := [1, 2, 2, 2, 1, 3, 2, 5, 1, 4]
def baseStart_6958961 : Nat := 118140960795 + 6958961 * 2 ^ 59
def prefixEnd_6958961 : Nat := 4983230072969 + 3 ^ 40 * 6958961 * 2
def baseEnd_6958961 : Nat := 1191097282964284255594609

theorem tailTrace_6958961 : CollatzResearch.WordTrace tailWord_6958961 prefixEnd_6958961 1191097282964284255594609 := by
  unfold tailWord_6958961
  simp only [CollatzResearch.WordTrace]
  refine ⟨253814159341880267762916737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169209439561253511841944491 253814159341880267762916737)
  ·
    refine ⟨190360619506410200822187553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253814159341880267762916737 190360619506410200822187553)
    ·
      refine ⟨142770464629807650616640665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190360619506410200822187553 142770464629807650616640665)
      ·
        refine ⟨107077848472355737962480499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142770464629807650616640665 107077848472355737962480499)
        ·
          refine ⟨160616772708533606943720749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107077848472355737962480499 160616772708533606943720749)
          ·
            refine ⟨60231289765700102603895281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160616772708533606943720749 60231289765700102603895281)
            ·
              refine ⟨45173467324275076952921461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60231289765700102603895281 45173467324275076952921461)
              ·
                refine ⟨4235012561650788464336387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45173467324275076952921461 4235012561650788464336387)
                ·
                  refine ⟨6352518842476182696504581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235012561650788464336387 6352518842476182696504581)
                  ·
                    refine ⟨1191097282964284255594609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352518842476182696504581 1191097282964284255594609)
                    ·
                      rfl

theorem cell23_6958961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_6958961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958961 prefixEnd_6958961 := by exact prefixLift 6958961
  have htrace : WordTrace (prefixWord ++ tailWord_6958961) baseStart_6958961 baseEnd_6958961 := by
    simpa [prefixWord, tailWord_6958961, baseEnd_6958961] using wordTrace_append hprefix tailTrace_6958961
  have hstable : (prefixWord ++ tailWord_6958961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958961).length < 2 ^ (prefixWord ++ tailWord_6958961).sum := by decide
  have hdescent : baseEnd_6958961 < baseStart_6958961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958997 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_6958997 : Nat := 118140960795 + 6958997 * 2 ^ 59
def prefixEnd_6958997 : Nat := 4983230072969 + 3 ^ 40 * 6958997 * 2
def baseEnd_6958997 : Nat := 3573310334196414625933661

theorem tailTrace_6958997 : CollatzResearch.WordTrace tailWord_6958997 prefixEnd_6958997 3573310334196414625933661 := by
  unfold tailWord_6958997
  simp only [CollatzResearch.WordTrace]
  refine ⟨253815472369749845911227245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169210314913166563940818163 253815472369749845911227245)
  ·
    refine ⟨95180802138656192216710217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253815472369749845911227245 95180802138656192216710217)
    ·
      refine ⟨71385601603992144162532663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95180802138656192216710217 71385601603992144162532663)
      ·
        refine ⟨107078402405988216243798995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71385601603992144162532663 107078402405988216243798995)
        ·
          refine ⟨160617603608982324365698493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107078402405988216243798995 160617603608982324365698493)
          ·
            refine ⟨60231601353368371637136935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160617603608982324365698493 60231601353368371637136935)
            ·
              refine ⟨90347402030052557455705403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60231601353368371637136935 90347402030052557455705403)
              ·
                refine ⟨135521103045078836183558105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90347402030052557455705403 135521103045078836183558105)
                ·
                  refine ⟨101640827283809127137668579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135521103045078836183558105 101640827283809127137668579)
                  ·
                    refine ⟨152461240925713690706502869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101640827283809127137668579 152461240925713690706502869)
                    ·
                      refine ⟨3573310334196414625933661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152461240925713690706502869 3573310334196414625933661)
                      ·
                        rfl

theorem cell23_6958997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_6958997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6958997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6958997 prefixEnd_6958997 := by exact prefixLift 6958997
  have htrace : WordTrace (prefixWord ++ tailWord_6958997) baseStart_6958997 baseEnd_6958997 := by
    simpa [prefixWord, tailWord_6958997, baseEnd_6958997] using wordTrace_append hprefix tailTrace_6958997
  have hstable : (prefixWord ++ tailWord_6958997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958997).length < 2 ^ (prefixWord ++ tailWord_6958997).sum := by decide
  have hdescent : baseEnd_6958997 < baseStart_6958997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959017 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 3, 6]
def baseStart_6959017 : Nat := 118140960795 + 6959017 * 2 ^ 59
def prefixEnd_6959017 : Nat := 4983230072969 + 3 ^ 40 * 6959017 * 2
def baseEnd_6959017 : Nat := 1191106867936501515894523

theorem tailTrace_6959017 : CollatzResearch.WordTrace tailWord_6959017 prefixEnd_6959017 1191106867936501515894523 := by
  unfold tailWord_6959017
  simp only [CollatzResearch.WordTrace]
  refine ⟨253816201829677389326955305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169210801219784926217970203 253816201829677389326955305)
  ·
    refine ⟨190362151372258041995216479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253816201829677389326955305 190362151372258041995216479)
    ·
      refine ⟨285543227058387062992824719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190362151372258041995216479 285543227058387062992824719)
      ·
        refine ⟨428314840587580594489237079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285543227058387062992824719 428314840587580594489237079)
        ·
          refine ⟨642472260881370891733855619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428314840587580594489237079 642472260881370891733855619)
          ·
            refine ⟨963708391322056337600783429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642472260881370891733855619 963708391322056337600783429)
            ·
              refine ⟨180695323372885563300146893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 963708391322056337600783429 180695323372885563300146893)
              ·
                refine ⟨67760746264832086237555085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180695323372885563300146893 67760746264832086237555085)
                ·
                  refine ⟨25410279849312032339083157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67760746264832086237555085 25410279849312032339083157)
                  ·
                    refine ⟨1191106867936501515894523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25410279849312032339083157 1191106867936501515894523)
                    ·
                      rfl

theorem cell23_6959017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_6959017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959017 prefixEnd_6959017 := by exact prefixLift 6959017
  have htrace : WordTrace (prefixWord ++ tailWord_6959017) baseStart_6959017 baseEnd_6959017 := by
    simpa [prefixWord, tailWord_6959017, baseEnd_6959017] using wordTrace_append hprefix tailTrace_6959017
  have hstable : (prefixWord ++ tailWord_6959017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959017).length < 2 ^ (prefixWord ++ tailWord_6959017).sum := by decide
  have hdescent : baseEnd_6959017 < baseStart_6959017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959024 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 8, 2]
def baseStart_6959024 : Nat := 118140960795 + 6959024 * 2 ^ 59
def prefixEnd_6959024 : Nat := 4983230072969 + 3 ^ 40 * 6959024 * 2
def baseEnd_6959024 : Nat := 3573324198174086020296037

theorem tailTrace_6959024 : CollatzResearch.WordTrace tailWord_6959024 prefixEnd_6959024 3573324198174086020296037 := by
  unfold tailWord_6959024
  simp only [CollatzResearch.WordTrace]
  refine ⟨126908228570326014761230063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169210971427101353014973417 126908228570326014761230063)
  ·
    refine ⟨190362342855489022141845095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126908228570326014761230063 190362342855489022141845095)
    ·
      refine ⟨285543514283233533212767643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190362342855489022141845095 285543514283233533212767643)
      ·
        refine ⟨428315271424850299819151465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285543514283233533212767643 428315271424850299819151465)
        ·
          refine ⟨321236453568637724864363599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428315271424850299819151465 321236453568637724864363599)
          ·
            refine ⟨481854680352956587296545399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321236453568637724864363599 481854680352956587296545399)
            ·
              refine ⟨722782020529434880944818099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481854680352956587296545399 722782020529434880944818099)
              ·
                refine ⟨1084173030794152321417227149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722782020529434880944818099 1084173030794152321417227149)
                ·
                  refine ⟨406564886547807120531460181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1084173030794152321417227149 406564886547807120531460181)
                  ·
                    refine ⟨4764432264232114693728049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 406564886547807120531460181 4764432264232114693728049)
                    ·
                      refine ⟨3573324198174086020296037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764432264232114693728049 3573324198174086020296037)
                      ·
                        rfl

theorem cell23_6959024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8, 2].length) (baseStart_6959024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959024 prefixEnd_6959024 := by exact prefixLift 6959024
  have htrace : WordTrace (prefixWord ++ tailWord_6959024) baseStart_6959024 baseEnd_6959024 := by
    simpa [prefixWord, tailWord_6959024, baseEnd_6959024] using wordTrace_append hprefix tailTrace_6959024
  have hstable : (prefixWord ++ tailWord_6959024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959024).length < 2 ^ (prefixWord ++ tailWord_6959024).sum := by decide
  have hdescent : baseEnd_6959024 < baseStart_6959024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959047 : List Nat := [1, 1, 4, 1, 1, 2, 1, 12]
def baseStart_6959047 : Nat := 118140960795 + 6959047 * 2 ^ 59
def prefixEnd_6959047 : Nat := 4983230072969 + 3 ^ 40 * 6959047 * 2
def baseEnd_6959047 : Nat := 132345778082560719641053

theorem tailTrace_6959047 : CollatzResearch.WordTrace tailWord_6959047 prefixEnd_6959047 132345778082560719641053 := by
  unfold tailWord_6959047
  simp only [CollatzResearch.WordTrace]
  refine ⟨253817296019568704450547395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169211530679712469633698263 253817296019568704450547395)
  ·
    refine ⟨380725944029353056675821093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253817296019568704450547395 380725944029353056675821093)
    ·
      refine ⟨71386114505503698126716455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380725944029353056675821093 71386114505503698126716455)
      ·
        refine ⟨107079171758255547190074683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71386114505503698126716455 107079171758255547190074683)
        ·
          refine ⟨160618757637383320785112025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107079171758255547190074683 160618757637383320785112025)
          ·
            refine ⟨120464068228037490588834019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160618757637383320785112025 120464068228037490588834019)
            ·
              refine ⟨180696102342056235883251029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120464068228037490588834019 180696102342056235883251029)
              ·
                refine ⟨132345778082560719641053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 180696102342056235883251029 132345778082560719641053)
                ·
                  rfl

theorem cell23_6959047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 12].length) (baseStart_6959047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959047 prefixEnd_6959047 := by exact prefixLift 6959047
  have htrace : WordTrace (prefixWord ++ tailWord_6959047) baseStart_6959047 baseEnd_6959047 := by
    simpa [prefixWord, tailWord_6959047, baseEnd_6959047] using wordTrace_append hprefix tailTrace_6959047
  have hstable : (prefixWord ++ tailWord_6959047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959047).length < 2 ^ (prefixWord ++ tailWord_6959047).sum := by decide
  have hdescent : baseEnd_6959047 < baseStart_6959047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959054 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6959054 : Nat := 118140960795 + 6959054 * 2 ^ 59
def prefixEnd_6959054 : Nat := 4983230072969 + 3 ^ 40 * 6959054 * 2
def baseEnd_6959054 : Nat := 3573339602593720902920899

theorem tailTrace_6959054 : CollatzResearch.WordTrace tailWord_6959054 prefixEnd_6959054 3573339602593720902920899 := by
  unfold tailWord_6959054
  simp only [CollatzResearch.WordTrace]
  refine ⟨31727193916317918080756527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169211700887028896430701477 31727193916317918080756527)
  ·
    refine ⟨47590790874476877121134791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31727193916317918080756527 47590790874476877121134791)
    ·
      refine ⟨71386186311715315681702187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47590790874476877121134791 71386186311715315681702187)
      ·
        refine ⟨107079279467572973522553281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71386186311715315681702187 107079279467572973522553281)
        ·
          refine ⟨80309459600679730141914961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107079279467572973522553281 80309459600679730141914961)
          ·
            refine ⟨60232094700509797606436221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80309459600679730141914961 60232094700509797606436221)
            ·
              refine ⟨22587035512691174102413583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60232094700509797606436221 22587035512691174102413583)
              ·
                refine ⟨33880553269036761153620375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22587035512691174102413583 33880553269036761153620375)
                ·
                  refine ⟨50820829903555141730430563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33880553269036761153620375 50820829903555141730430563)
                  ·
                    refine ⟨76231244855332712595645845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50820829903555141730430563 76231244855332712595645845)
                    ·
                      refine ⟨3573339602593720902920899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76231244855332712595645845 3573339602593720902920899)
                      ·
                        rfl

theorem cell23_6959054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6959054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959054 prefixEnd_6959054 := by exact prefixLift 6959054
  have htrace : WordTrace (prefixWord ++ tailWord_6959054) baseStart_6959054 baseEnd_6959054 := by
    simpa [prefixWord, tailWord_6959054, baseEnd_6959054] using wordTrace_append hprefix tailTrace_6959054
  have hstable : (prefixWord ++ tailWord_6959054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959054).length < 2 ^ (prefixWord ++ tailWord_6959054).sum := by decide
  have hdescent : baseEnd_6959054 < baseStart_6959054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959069 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_6959069 : Nat := 118140960795 + 6959069 * 2 ^ 59
def prefixEnd_6959069 : Nat := 4983230072969 + 3 ^ 40 * 6959069 * 2
def baseEnd_6959069 : Nat := 3573347304803538344233331

theorem tailTrace_6959069 : CollatzResearch.WordTrace tailWord_6959069 prefixEnd_6959069 3573347304803538344233331 := by
  unfold tailWord_6959069
  simp only [CollatzResearch.WordTrace]
  refine ⟨253818098425489002207848261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169212065616992668138565507 253818098425489002207848261)
  ·
    refine ⟨47590893454779187913971549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253818098425489002207848261 47590893454779187913971549)
    ·
      refine ⟨17846585045542195467739331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47590893454779187913971549 17846585045542195467739331)
      ·
        refine ⟨26769877568313293201608997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17846585045542195467739331 26769877568313293201608997)
        ·
          refine ⟨5019352044058742475301687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26769877568313293201608997 5019352044058742475301687)
          ·
            refine ⟨7529028066088113712952531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019352044058742475301687 7529028066088113712952531)
            ·
              refine ⟨11293542099132170569428797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7529028066088113712952531 11293542099132170569428797)
              ·
                refine ⟨4235078287174563963535799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11293542099132170569428797 4235078287174563963535799)
                ·
                  refine ⟨6352617430761845945303699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235078287174563963535799 6352617430761845945303699)
                  ·
                    refine ⟨9528926146142768917955549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352617430761845945303699 9528926146142768917955549)
                    ·
                      refine ⟨3573347304803538344233331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9528926146142768917955549 3573347304803538344233331)
                      ·
                        rfl

theorem cell23_6959069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_6959069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959069 prefixEnd_6959069 := by exact prefixLift 6959069
  have htrace : WordTrace (prefixWord ++ tailWord_6959069) baseStart_6959069 baseEnd_6959069 := by
    simpa [prefixWord, tailWord_6959069, baseEnd_6959069] using wordTrace_append hprefix tailTrace_6959069
  have hstable : (prefixWord ++ tailWord_6959069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959069).length < 2 ^ (prefixWord ++ tailWord_6959069).sum := by decide
  have hdescent : baseEnd_6959069 < baseStart_6959069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959102 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6959102 : Nat := 118140960795 + 6959102 * 2 ^ 59
def prefixEnd_6959102 : Nat := 4983230072969 + 3 ^ 40 * 6959102 * 2
def baseEnd_6959102 : Nat := 1191121416555045571706893

theorem tailTrace_6959102 : CollatzResearch.WordTrace tailWord_6959102 prefixEnd_6959102 1191121416555045571706893 := by
  unfold tailWord_6959102
  simp only [CollatzResearch.WordTrace]
  refine ⟨31727412754296181105474945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169212868022912965895866373 31727412754296181105474945)
  ·
    refine ⟨23795559565722135829106209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31727412754296181105474945 23795559565722135829106209)
    ·
      refine ⟨17846669674291601871829657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23795559565722135829106209 17846669674291601871829657)
      ·
        refine ⟨13385002255718701403872243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17846669674291601871829657 13385002255718701403872243)
        ·
          refine ⟨20077503383578052105808365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13385002255718701403872243 20077503383578052105808365)
          ·
            refine ⟨7529063768841769539678137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20077503383578052105808365 7529063768841769539678137)
            ·
              refine ⟨5646797826631327154758603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7529063768841769539678137 5646797826631327154758603)
              ·
                refine ⟨8470196739946990732137905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646797826631327154758603 8470196739946990732137905)
                ·
                  refine ⟨6352647554960243049103429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8470196739946990732137905 6352647554960243049103429)
                  ·
                    refine ⟨1191121416555045571706893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352647554960243049103429 1191121416555045571706893)
                    ·
                      rfl

theorem cell23_6959102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6959102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959102 prefixEnd_6959102 := by exact prefixLift 6959102
  have htrace : WordTrace (prefixWord ++ tailWord_6959102) baseStart_6959102 baseEnd_6959102 := by
    simpa [prefixWord, tailWord_6959102, baseEnd_6959102] using wordTrace_append hprefix tailTrace_6959102
  have hstable : (prefixWord ++ tailWord_6959102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959102).length < 2 ^ (prefixWord ++ tailWord_6959102).sum := by decide
  have hdescent : baseEnd_6959102 < baseStart_6959102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959118 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_6959118 : Nat := 118140960795 + 6959118 * 2 ^ 59
def prefixEnd_6959118 : Nat := 4983230072969 + 3 ^ 40 * 6959118 * 2
def baseEnd_6959118 : Nat := 3573372465355608652520605

theorem tailTrace_6959118 : CollatzResearch.WordTrace tailWord_6959118 prefixEnd_6959118 3573372465355608652520605 := by
  unfold tailWord_6959118
  simp only [CollatzResearch.WordTrace]
  refine ⟨31727485700288935447047751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169213257068207655717588005 31727485700288935447047751)
  ·
    refine ⟨47591228550433403170571627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31727485700288935447047751 47591228550433403170571627)
    ·
      refine ⟨71386842825650104755857441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47591228550433403170571627 71386842825650104755857441)
      ·
        refine ⟨53540132119237578566893081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71386842825650104755857441 53540132119237578566893081)
        ·
          refine ⟨40155099089428183925169811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53540132119237578566893081 40155099089428183925169811)
          ·
            refine ⟨60232648634142275887754717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40155099089428183925169811 60232648634142275887754717)
            ·
              refine ⟨22587243237803353457908019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60232648634142275887754717 22587243237803353457908019)
              ·
                refine ⟨33880864856705030186862029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22587243237803353457908019 33880864856705030186862029)
                ·
                  refine ⟨12705324321264386320073261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33880864856705030186862029 12705324321264386320073261)
                  ·
                    refine ⟨4764496620474144870027473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12705324321264386320073261 4764496620474144870027473)
                    ·
                      refine ⟨3573372465355608652520605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764496620474144870027473 3573372465355608652520605)
                      ·
                        rfl

theorem cell23_6959118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_6959118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959118 prefixEnd_6959118 := by exact prefixLift 6959118
  have htrace : WordTrace (prefixWord ++ tailWord_6959118) baseStart_6959118 baseEnd_6959118 := by
    simpa [prefixWord, tailWord_6959118, baseEnd_6959118] using wordTrace_append hprefix tailTrace_6959118
  have hstable : (prefixWord ++ tailWord_6959118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959118).length < 2 ^ (prefixWord ++ tailWord_6959118).sum := by decide
  have hdescent : baseEnd_6959118 < baseStart_6959118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959135 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 1, 3, 2]
def baseStart_6959135 : Nat := 118140960795 + 6959135 * 2 ^ 59
def prefixEnd_6959135 : Nat := 4983230072969 + 3 ^ 40 * 6959135 * 2
def baseEnd_6959135 : Nat := 3573381194526735086008027

theorem tailTrace_6959135 : CollatzResearch.WordTrace tailWord_6959135 prefixEnd_6959135 3573381194526735086008027 := by
  unfold tailWord_6959135
  simp only [CollatzResearch.WordTrace]
  refine ⟨253820505643249895479750859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169213670428833263653167239 253820505643249895479750859)
  ·
    refine ⟨380730758464874843219626289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253820505643249895479750859 380730758464874843219626289)
    ·
      refine ⟨285548068848656132414719717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380730758464874843219626289 285548068848656132414719717)
      ·
        refine ⟨53540262909123024827759947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285548068848656132414719717 53540262909123024827759947)
        ·
          refine ⟨80310394363684537241639921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53540262909123024827759947 80310394363684537241639921)
          ·
            refine ⟨60232795772763402931229941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80310394363684537241639921 60232795772763402931229941)
            ·
              refine ⟨5646824603696569024802807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60232795772763402931229941 5646824603696569024802807)
              ·
                refine ⟨8470236905544853537204211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5646824603696569024802807 8470236905544853537204211)
                ·
                  refine ⟨12705355358317280305806317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8470236905544853537204211 12705355358317280305806317)
                  ·
                    refine ⟨4764508259368980114677369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12705355358317280305806317 4764508259368980114677369)
                    ·
                      refine ⟨3573381194526735086008027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764508259368980114677369 3573381194526735086008027)
                      ·
                        rfl

theorem cell23_6959135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_6959135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959135 prefixEnd_6959135 := by exact prefixLift 6959135
  have htrace : WordTrace (prefixWord ++ tailWord_6959135) baseStart_6959135 baseEnd_6959135 := by
    simpa [prefixWord, tailWord_6959135, baseEnd_6959135] using wordTrace_append hprefix tailTrace_6959135
  have hstable : (prefixWord ++ tailWord_6959135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959135).length < 2 ^ (prefixWord ++ tailWord_6959135).sum := by decide
  have hdescent : baseEnd_6959135 < baseStart_6959135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959143 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6959143 : Nat := 118140960795 + 6959143 * 2 ^ 59
def prefixEnd_6959143 : Nat := 4983230072969 + 3 ^ 40 * 6959143 * 2
def baseEnd_6959143 : Nat := 3573385302371971054707991

theorem tailTrace_6959143 : CollatzResearch.WordTrace tailWord_6959143 prefixEnd_6959143 3573385302371971054707991 := by
  unfold tailWord_6959143
  simp only [CollatzResearch.WordTrace]
  refine ⟨253820797427220912846042083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169213864951480608564028055 253820797427220912846042083)
  ·
    refine ⟨380731196140831369269063125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253820797427220912846042083 380731196140831369269063125)
    ·
      refine ⟨8923387409550735217243667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 380731196140831369269063125 8923387409550735217243667)
      ·
        refine ⟨13385081114326102825865501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8923387409550735217243667 13385081114326102825865501)
        ·
          refine ⟨5019405417872288559699563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13385081114326102825865501 5019405417872288559699563)
          ·
            refine ⟨7529108126808432839549345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019405417872288559699563 7529108126808432839549345)
            ·
              refine ⟨5646831095106324629662009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7529108126808432839549345 5646831095106324629662009)
              ·
                refine ⟨4235123321329743472246507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5646831095106324629662009 4235123321329743472246507)
                ·
                  refine ⟨6352684981994615208369761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235123321329743472246507 6352684981994615208369761)
                  ·
                    refine ⟨4764513736495961406277321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352684981994615208369761 4764513736495961406277321)
                    ·
                      refine ⟨3573385302371971054707991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764513736495961406277321 3573385302371971054707991)
                      ·
                        rfl

theorem cell23_6959143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6959143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959143 prefixEnd_6959143 := by exact prefixLift 6959143
  have htrace : WordTrace (prefixWord ++ tailWord_6959143) baseStart_6959143 baseEnd_6959143 := by
    simpa [prefixWord, tailWord_6959143, baseEnd_6959143] using wordTrace_append hprefix tailTrace_6959143
  have hstable : (prefixWord ++ tailWord_6959143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959143).length < 2 ^ (prefixWord ++ tailWord_6959143).sum := by decide
  have hdescent : baseEnd_6959143 < baseStart_6959143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959165 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_6959165 : Nat := 118140960795 + 6959165 * 2 ^ 59
def prefixEnd_6959165 : Nat := 4983230072969 + 3 ^ 40 * 6959165 * 2
def baseEnd_6959165 : Nat := 3573396598946369968632889

theorem tailTrace_6959165 : CollatzResearch.WordTrace tailWord_6959165 prefixEnd_6959165 3573396598946369968632889 := by
  unfold tailWord_6959165
  simp only [CollatzResearch.WordTrace]
  refine ⟨253821599833141210603342949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169214399888760807068895299 253821599833141210603342949)
  ·
    refine ⟨47591549968713976988126803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253821599833141210603342949 47591549968713976988126803)
    ·
      refine ⟨71387324953070965482190205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47591549968713976988126803 71387324953070965482190205)
      ·
        refine ⟨26770246857401612055821327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71387324953070965482190205 26770246857401612055821327)
        ·
          refine ⟨40155370286102418083731991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26770246857401612055821327 40155370286102418083731991)
          ·
            refine ⟨60233055429153627125597987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40155370286102418083731991 60233055429153627125597987)
            ·
              refine ⟨90349583143730440688396981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60233055429153627125597987 90349583143730440688396981)
              ·
                refine ⟨8470273419724728814537217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90349583143730440688396981 8470273419724728814537217)
                ·
                  refine ⟨6352705064793546610902913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8470273419724728814537217 6352705064793546610902913)
                  ·
                    refine ⟨4764528798595159958177185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352705064793546610902913 4764528798595159958177185)
                    ·
                      refine ⟨3573396598946369968632889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764528798595159958177185 3573396598946369968632889)
                      ·
                        rfl

theorem cell23_6959165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_6959165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959165 prefixEnd_6959165 := by exact prefixLift 6959165
  have htrace : WordTrace (prefixWord ++ tailWord_6959165) baseStart_6959165 baseEnd_6959165 := by
    simpa [prefixWord, tailWord_6959165, baseEnd_6959165] using wordTrace_append hprefix tailTrace_6959165
  have hstable : (prefixWord ++ tailWord_6959165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959165).length < 2 ^ (prefixWord ++ tailWord_6959165).sum := by decide
  have hdescent : baseEnd_6959165 < baseStart_6959165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959241 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_6959241 : Nat := 118140960795 + 6959241 * 2 ^ 59
def prefixEnd_6959241 : Nat := 4983230072969 + 3 ^ 40 * 6959241 * 2
def baseEnd_6959241 : Nat := 3573435623476111671282539

theorem tailTrace_6959241 : CollatzResearch.WordTrace tailWord_6959241 prefixEnd_6959241 3573435623476111671282539 := by
  unfold tailWord_6959241
  simp only [CollatzResearch.WordTrace]
  refine ⟨253824371780865875583109577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169216247853910583722073051 253824371780865875583109577)
  ·
    refine ⟨190368278835649406687332183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253824371780865875583109577 190368278835649406687332183)
    ·
      refine ⟨285552418253474110030998275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190368278835649406687332183 285552418253474110030998275)
      ·
        refine ⟨428328627380211165046497413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285552418253474110030998275 428328627380211165046497413)
        ·
          refine ⟨80311617633789593446218265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428328627380211165046497413 80311617633789593446218265)
          ·
            refine ⟨60233713225342195084663699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80311617633789593446218265 60233713225342195084663699)
            ·
              refine ⟨90350569838013292626995549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60233713225342195084663699 90350569838013292626995549)
              ·
                refine ⟨33881463689254984735123331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90350569838013292626995549 33881463689254984735123331)
                ·
                  refine ⟨50822195533882477102684997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33881463689254984735123331 50822195533882477102684997)
                  ·
                    refine ⟨9529161662602964456753437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50822195533882477102684997 9529161662602964456753437)
                    ·
                      refine ⟨3573435623476111671282539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9529161662602964456753437 3573435623476111671282539)
                      ·
                        rfl

theorem cell23_6959241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_6959241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959241 prefixEnd_6959241 := by exact prefixLift 6959241
  have htrace : WordTrace (prefixWord ++ tailWord_6959241) baseStart_6959241 baseEnd_6959241 := by
    simpa [prefixWord, tailWord_6959241, baseEnd_6959241] using wordTrace_append hprefix tailTrace_6959241
  have hstable : (prefixWord ++ tailWord_6959241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959241).length < 2 ^ (prefixWord ++ tailWord_6959241).sum := by decide
  have hdescent : baseEnd_6959241 < baseStart_6959241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959261 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 8]
def baseStart_6959261 : Nat := 118140960795 + 6959261 * 2 ^ 59
def prefixEnd_6959261 : Nat := 4983230072969 + 3 ^ 40 * 6959261 * 2
def baseEnd_6959261 : Nat := 397049543676577954781383

theorem tailTrace_6959261 : CollatzResearch.WordTrace tailWord_6959261 prefixEnd_6959261 397049543676577954781383 := by
  unfold tailWord_6959261
  simp only [CollatzResearch.WordTrace]
  refine ⟨253825101240793418998837637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169216734160528945999225091 253825101240793418998837637)
  ·
    refine ⟨47592206482648766062282057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253825101240793418998837637 47592206482648766062282057)
    ·
      refine ⟨35694154861986574546711543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47592206482648766062282057 35694154861986574546711543)
      ·
        refine ⟨53541232292979861820067315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35694154861986574546711543 53541232292979861820067315)
        ·
          refine ⟨80311848439469792730100973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53541232292979861820067315 80311848439469792730100973)
          ·
            refine ⟨30116943164801172273787865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80311848439469792730100973 30116943164801172273787865)
            ·
              refine ⟨22587707373600879205340899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30116943164801172273787865 22587707373600879205340899)
              ·
                refine ⟨33881561060401318808011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22587707373600879205340899 33881561060401318808011349)
                ·
                  refine ⟨397049543676577954781383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33881561060401318808011349 397049543676577954781383)
                  ·
                    rfl

theorem cell23_6959261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_6959261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959261 prefixEnd_6959261 := by exact prefixLift 6959261
  have htrace : WordTrace (prefixWord ++ tailWord_6959261) baseStart_6959261 baseEnd_6959261 := by
    simpa [prefixWord, tailWord_6959261, baseEnd_6959261] using wordTrace_append hprefix tailTrace_6959261
  have hstable : (prefixWord ++ tailWord_6959261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959261).length < 2 ^ (prefixWord ++ tailWord_6959261).sum := by decide
  have hdescent : baseEnd_6959261 < baseStart_6959261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959265 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 3, 4]
def baseStart_6959265 : Nat := 118140960795 + 6959265 * 2 ^ 59
def prefixEnd_6959265 : Nat := 4983230072969 + 3 ^ 40 * 6959265 * 2
def baseEnd_6959265 : Nat := 1191149315670606525794143

theorem tailTrace_6959265 : CollatzResearch.WordTrace tailWord_6959265 prefixEnd_6959265 1191149315670606525794143 := by
  unfold tailWord_6959265
  simp only [CollatzResearch.WordTrace]
  refine ⟨253825247132778927681983249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169216831421852618454655499 253825247132778927681983249)
  ·
    refine ⟨190368935349584195761487437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253825247132778927681983249 190368935349584195761487437)
    ·
      refine ⟨71388350756094073410557789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190368935349584195761487437 71388350756094073410557789)
      ·
        refine ⟨26770631533535277528959171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71388350756094073410557789 26770631533535277528959171)
        ·
          refine ⟨40155947300302916293438757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26770631533535277528959171 40155947300302916293438757)
          ·
            refine ⟨7529240118806796805019767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40155947300302916293438757 7529240118806796805019767)
            ·
              refine ⟨11293860178210195207529651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7529240118806796805019767 11293860178210195207529651)
              ·
                refine ⟨16940790267315292811294477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293860178210195207529651 16940790267315292811294477)
                ·
                  refine ⟨6352796350243234804235429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16940790267315292811294477 6352796350243234804235429)
                  ·
                    refine ⟨1191149315670606525794143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352796350243234804235429 1191149315670606525794143)
                    ·
                      rfl

theorem cell23_6959265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_6959265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959265 prefixEnd_6959265 := by exact prefixLift 6959265
  have htrace : WordTrace (prefixWord ++ tailWord_6959265) baseStart_6959265 baseEnd_6959265 := by
    simpa [prefixWord, tailWord_6959265, baseEnd_6959265] using wordTrace_append hprefix tailTrace_6959265
  have hstable : (prefixWord ++ tailWord_6959265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959265).length < 2 ^ (prefixWord ++ tailWord_6959265).sum := by decide
  have hdescent : baseEnd_6959265 < baseStart_6959265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959288 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_6959288 : Nat := 118140960795 + 6959288 * 2 ^ 59
def prefixEnd_6959288 : Nat := 4983230072969 + 3 ^ 40 * 6959288 * 2
def baseEnd_6959288 : Nat := 3573459757066872987394823

theorem tailTrace_6959288 : CollatzResearch.WordTrace tailWord_6959288 prefixEnd_6959288 3573459757066872987394823 := by
  unfold tailWord_6959288
  simp only [CollatzResearch.WordTrace]
  refine ⟨126913043005847801305035259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169217390674463735073380345 126913043005847801305035259)
  ·
    refine ⟨190369564508771701957552889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126913043005847801305035259 190369564508771701957552889)
    ·
      refine ⟨142777173381578776468164667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190369564508771701957552889 142777173381578776468164667)
      ·
        refine ⟨214165760072368164702247001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142777173381578776468164667 214165760072368164702247001)
        ·
          refine ⟨160624320054276123526685251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214165760072368164702247001 160624320054276123526685251)
          ·
            refine ⟨240936480081414185290027877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160624320054276123526685251 240936480081414185290027877)
            ·
              refine ⟨45175590015265159741880227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240936480081414185290027877 45175590015265159741880227)
              ·
                refine ⟨67763385022897739612820341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45175590015265159741880227 67763385022897739612820341)
                ·
                  refine ⟨6352817345896663088701907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67763385022897739612820341 6352817345896663088701907)
                  ·
                    refine ⟨9529226018844994633052861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352817345896663088701907 9529226018844994633052861)
                    ·
                      refine ⟨3573459757066872987394823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9529226018844994633052861 3573459757066872987394823)
                      ·
                        rfl

theorem cell23_6959288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_6959288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959288 prefixEnd_6959288 := by exact prefixLift 6959288
  have htrace : WordTrace (prefixWord ++ tailWord_6959288) baseStart_6959288 baseEnd_6959288 := by
    simpa [prefixWord, tailWord_6959288, baseEnd_6959288] using wordTrace_append hprefix tailTrace_6959288
  have hstable : (prefixWord ++ tailWord_6959288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959288).length < 2 ^ (prefixWord ++ tailWord_6959288).sum := by decide
  have hdescent : baseEnd_6959288 < baseStart_6959288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959291 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 3, 5]
def baseStart_6959291 : Nat := 118140960795 + 6959291 * 2 ^ 59
def prefixEnd_6959291 : Nat := 4983230072969 + 3 ^ 40 * 6959291 * 2
def baseEnd_6959291 : Nat := 1191153765836278825219103

theorem tailTrace_6959291 : CollatzResearch.WordTrace tailWord_6959291 prefixEnd_6959291 1191153765836278825219103 := by
  unfold tailWord_6959291
  simp only [CollatzResearch.WordTrace]
  refine ⟨253826195430684734122429727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169217463620456489414953151 253826195430684734122429727)
  ·
    refine ⟨380739293146027101183644591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253826195430684734122429727 380739293146027101183644591)
    ·
      refine ⟨571108939719040651775466887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380739293146027101183644591 571108939719040651775466887)
      ·
        refine ⟨856663409578560977663200331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571108939719040651775466887 856663409578560977663200331)
        ·
          refine ⟨1284995114367841466494800497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856663409578560977663200331 1284995114367841466494800497)
          ·
            refine ⟨963746335775881099871100373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284995114367841466494800497 963746335775881099871100373)
            ·
              refine ⟨22587804744747213278228915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 963746335775881099871100373 22587804744747213278228915)
              ·
                refine ⟨33881707117120819917343373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22587804744747213278228915 33881707117120819917343373)
                ·
                  refine ⟨12705640168920307469003765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33881707117120819917343373 12705640168920307469003765)
                  ·
                    refine ⟨1191153765836278825219103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12705640168920307469003765 1191153765836278825219103)
                    ·
                      rfl

theorem cell23_6959291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 5].length) (baseStart_6959291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959291 prefixEnd_6959291 := by exact prefixLift 6959291
  have htrace : WordTrace (prefixWord ++ tailWord_6959291) baseStart_6959291 baseEnd_6959291 := by
    simpa [prefixWord, tailWord_6959291, baseEnd_6959291] using wordTrace_append hprefix tailTrace_6959291
  have hstable : (prefixWord ++ tailWord_6959291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959291).length < 2 ^ (prefixWord ++ tailWord_6959291).sum := by decide
  have hdescent : baseEnd_6959291 < baseStart_6959291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959338 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_6959338 : Nat := 118140960795 + 6959338 * 2 ^ 59
def prefixEnd_6959338 : Nat := 4983230072969 + 3 ^ 40 * 6959338 * 2
def baseEnd_6959338 : Nat := 1191161810366532597256531

theorem tailTrace_6959338 : CollatzResearch.WordTrace tailWord_6959338 prefixEnd_6959338 1191161810366532597256531 := by
  unfold tailWord_6959338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63456977415378615287347667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169218606441009640766260445 63456977415378615287347667)
  ·
    refine ⟨95185466123067922931021501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63456977415378615287347667 95185466123067922931021501)
    ·
      refine ⟨35694549796150471099133063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95185466123067922931021501 35694549796150471099133063)
      ·
        refine ⟨53541824694225706648699595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35694549796150471099133063 53541824694225706648699595)
        ·
          refine ⟨80312737041338559973049393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53541824694225706648699595 80312737041338559973049393)
          ·
            refine ⟨60234552781003919979787045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80312737041338559973049393 60234552781003919979787045)
            ·
              refine ⟨11293978646438234996210071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60234552781003919979787045 11293978646438234996210071)
              ·
                refine ⟨16940967969657352494315107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11293978646438234996210071 16940967969657352494315107)
                ·
                  refine ⟨25411451954486028741472661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16940967969657352494315107 25411451954486028741472661)
                  ·
                    refine ⟨1191161810366532597256531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25411451954486028741472661 1191161810366532597256531)
                    ·
                      rfl

theorem cell23_6959338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_6959338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959338 prefixEnd_6959338 := by exact prefixLift 6959338
  have htrace : WordTrace (prefixWord ++ tailWord_6959338) baseStart_6959338 baseEnd_6959338 := by
    simpa [prefixWord, tailWord_6959338, baseEnd_6959338] using wordTrace_append hprefix tailTrace_6959338
  have hstable : (prefixWord ++ tailWord_6959338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959338).length < 2 ^ (prefixWord ++ tailWord_6959338).sum := by decide
  have hdescent : baseEnd_6959338 < baseStart_6959338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959345 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 5, 2, 2]
def baseStart_6959345 : Nat := 118140960795 + 6959345 * 2 ^ 59
def prefixEnd_6959345 : Nat := 4983230072969 + 3 ^ 40 * 6959345 * 2
def baseEnd_6959345 : Nat := 3573489025464179264382061

theorem tailTrace_6959345 : CollatzResearch.WordTrace tailWord_6959345 prefixEnd_6959345 3573489025464179264382061 := by
  unfold tailWord_6959345
  simp only [CollatzResearch.WordTrace]
  refine ⟨253828164972489101344895489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169218776648326067563263659 253828164972489101344895489)
  ·
    refine ⟨190371123729366826008671617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253828164972489101344895489 190371123729366826008671617)
    ·
      refine ⟨142778342797025119506503713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190371123729366826008671617 142778342797025119506503713)
      ·
        refine ⟨107083757097768839629877785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142778342797025119506503713 107083757097768839629877785)
        ·
          refine ⟨80312817823326629722408339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107083757097768839629877785 80312817823326629722408339)
          ·
            refine ⟨120469226734989944583612509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80312817823326629722408339 120469226734989944583612509)
            ·
              refine ⟨45175960025621229218854691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120469226734989944583612509 45175960025621229218854691)
              ·
                refine ⟨67763940038431843828282037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45175960025621229218854691 67763940038431843828282037)
                ·
                  refine ⟨6352869378602985358901441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67763940038431843828282037 6352869378602985358901441)
                  ·
                    refine ⟨4764652033952239019176081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6352869378602985358901441 4764652033952239019176081)
                    ·
                      refine ⟨3573489025464179264382061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764652033952239019176081 3573489025464179264382061)
                      ·
                        rfl

theorem cell23_6959345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_6959345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959345 prefixEnd_6959345 := by exact prefixLift 6959345
  have htrace : WordTrace (prefixWord ++ tailWord_6959345) baseStart_6959345 baseEnd_6959345 := by
    simpa [prefixWord, tailWord_6959345, baseEnd_6959345] using wordTrace_append hprefix tailTrace_6959345
  have hstable : (prefixWord ++ tailWord_6959345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959345).length < 2 ^ (prefixWord ++ tailWord_6959345).sum := by decide
  have hdescent : baseEnd_6959345 < baseStart_6959345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959362 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_6959362 : Nat := 118140960795 + 6959362 * 2 ^ 59
def prefixEnd_6959362 : Nat := 4983230072969 + 3 ^ 40 * 6959362 * 2
def baseEnd_6959362 : Nat := 3573497754635305697869483

theorem tailTrace_6959362 : CollatzResearch.WordTrace tailWord_6959362 prefixEnd_6959362 3573497754635305697869483 := by
  unfold tailWord_6959362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63457196253356878312066085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169219190008951675498842893 63457196253356878312066085)
  ·
    refine ⟨11898224297504414683512391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63457196253356878312066085 11898224297504414683512391)
    ·
      refine ⟨17847336446256622025268587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11898224297504414683512391 17847336446256622025268587)
      ·
        refine ⟨26771004669384933037902881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17847336446256622025268587 26771004669384933037902881)
        ·
          refine ⟨20078253502038699778427161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26771004669384933037902881 20078253502038699778427161)
          ·
            refine ⟨15058690126529024833820371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20078253502038699778427161 15058690126529024833820371)
            ·
              refine ⟨22588035189793537250730557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15058690126529024833820371 22588035189793537250730557)
              ·
                refine ⟨8470513196172576469023959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22588035189793537250730557 8470513196172576469023959)
                ·
                  refine ⟨12705769794258864703535939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8470513196172576469023959 12705769794258864703535939)
                  ·
                    refine ⟨19058654691388297055303909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12705769794258864703535939 19058654691388297055303909)
                    ·
                      refine ⟨3573497754635305697869483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19058654691388297055303909 3573497754635305697869483)
                      ·
                        rfl

theorem cell23_6959362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_6959362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959362 prefixEnd_6959362 := by exact prefixLift 6959362
  have htrace : WordTrace (prefixWord ++ tailWord_6959362) baseStart_6959362 baseEnd_6959362 := by
    simpa [prefixWord, tailWord_6959362, baseEnd_6959362] using wordTrace_append hprefix tailTrace_6959362
  have hstable : (prefixWord ++ tailWord_6959362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959362).length < 2 ^ (prefixWord ++ tailWord_6959362).sum := by decide
  have hdescent : baseEnd_6959362 < baseStart_6959362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959381 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_6959381 : Nat := 118140960795 + 6959381 * 2 ^ 59
def prefixEnd_6959381 : Nat := 4983230072969 + 3 ^ 40 * 6959381 * 2
def baseEnd_6959381 : Nat := 1191169170255913707843965

theorem tailTrace_6959381 : CollatzResearch.WordTrace tailWord_6959381 prefixEnd_6959381 1191169170255913707843965 := by
  unfold tailWord_6959381
  simp only [CollatzResearch.WordTrace]
  refine ⟨253829478000358679493205997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169219652000239119662137331 253829478000358679493205997)
  ·
    refine ⟨95186054250134504809952249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253829478000358679493205997 95186054250134504809952249)
    ·
      refine ⟨71389540687600878607464187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95186054250134504809952249 71389540687600878607464187)
      ·
        refine ⟨107084311031401317911196281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71389540687600878607464187 107084311031401317911196281)
        ·
          refine ⟨80313233273550988433397211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107084311031401317911196281 80313233273550988433397211)
          ·
            refine ⟨120469849910326482650095817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80313233273550988433397211 120469849910326482650095817)
            ·
              refine ⟨90352387432744861987571863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120469849910326482650095817 90352387432744861987571863)
              ·
                refine ⟨135528581149117292981357795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90352387432744861987571863 135528581149117292981357795)
                ·
                  refine ⟨203292871723675939472036693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135528581149117292981357795 203292871723675939472036693)
                  ·
                    refine ⟨1191169170255913707843965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 203292871723675939472036693 1191169170255913707843965)
                    ·
                      rfl

theorem cell23_6959381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_6959381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959381 prefixEnd_6959381 := by exact prefixLift 6959381
  have htrace : WordTrace (prefixWord ++ tailWord_6959381) baseStart_6959381 baseEnd_6959381 := by
    simpa [prefixWord, tailWord_6959381, baseEnd_6959381] using wordTrace_append hprefix tailTrace_6959381
  have hstable : (prefixWord ++ tailWord_6959381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959381).length < 2 ^ (prefixWord ++ tailWord_6959381).sum := by decide
  have hdescent : baseEnd_6959381 < baseStart_6959381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959389 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 2, 4]
def baseStart_6959389 : Nat := 118140960795 + 6959389 * 2 ^ 59
def prefixEnd_6959389 : Nat := 4983230072969 + 3 ^ 40 * 6959389 * 2
def baseEnd_6959389 : Nat := 1191170539537659030743953

theorem tailTrace_6959389 : CollatzResearch.WordTrace tailWord_6959389 prefixEnd_6959389 1191170539537659030743953 := by
  unfold tailWord_6959389
  simp only [CollatzResearch.WordTrace]
  refine ⟨253829769784329696859497221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169219846522886464572998147 253829769784329696859497221)
  ·
    refine ⟨47593081834561818161155729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253829769784329696859497221 47593081834561818161155729)
    ·
      refine ⟨35694811375921363620866797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47593081834561818161155729 35694811375921363620866797)
      ·
        refine ⟨13385554265970511357825049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35694811375921363620866797 13385554265970511357825049)
        ·
          refine ⟨10039165699477883518368787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13385554265970511357825049 10039165699477883518368787)
          ·
            refine ⟨15058748549216825277553181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10039165699477883518368787 15058748549216825277553181)
            ·
              refine ⟨5647030705956309479082443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15058748549216825277553181 5647030705956309479082443)
              ·
                refine ⟨8470546058934464218623665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647030705956309479082443 8470546058934464218623665)
                ·
                  refine ⟨6352909544200848163967749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8470546058934464218623665 6352909544200848163967749)
                  ·
                    refine ⟨1191170539537659030743953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6352909544200848163967749 1191170539537659030743953)
                    ·
                      rfl

theorem cell23_6959389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_6959389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959389 prefixEnd_6959389 := by exact prefixLift 6959389
  have htrace : WordTrace (prefixWord ++ tailWord_6959389) baseStart_6959389 baseEnd_6959389 := by
    simpa [prefixWord, tailWord_6959389, baseEnd_6959389] using wordTrace_append hprefix tailTrace_6959389
  have hstable : (prefixWord ++ tailWord_6959389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959389).length < 2 ^ (prefixWord ++ tailWord_6959389).sum := by decide
  have hdescent : baseEnd_6959389 < baseStart_6959389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959402 : List Nat := [3, 1, 4, 2, 2, 2, 2, 7]
def baseStart_6959402 : Nat := 118140960795 + 6959402 * 2 ^ 59
def prefixEnd_6959402 : Nat := 4983230072969 + 3 ^ 40 * 6959402 * 2
def baseEnd_6959402 : Nat := 132352529402277242272937

theorem tailTrace_6959402 : CollatzResearch.WordTrace tailWord_6959402 prefixEnd_6959402 132352529402277242272937 := by
  unfold tailWord_6959402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63457560983320650019930115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169220162622188400053146973 63457560983320650019930115)
  ·
    refine ⟨95186341474980975029895173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63457560983320650019930115 95186341474980975029895173)
    ·
      refine ⟨17847439026558932818105345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95186341474980975029895173 17847439026558932818105345)
      ·
        refine ⟨13385579269919199613579009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17847439026558932818105345 13385579269919199613579009)
        ·
          refine ⟨10039184452439399710184257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13385579269919199613579009 10039184452439399710184257)
          ·
            refine ⟨7529388339329549782638193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10039184452439399710184257 7529388339329549782638193)
            ·
              refine ⟨5647041254497162336978645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7529388339329549782638193 5647041254497162336978645)
              ·
                refine ⟨132352529402277242272937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5647041254497162336978645 132352529402277242272937)
                ·
                  rfl

theorem cell23_6959402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_6959402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959402 prefixEnd_6959402 := by exact prefixLift 6959402
  have htrace : WordTrace (prefixWord ++ tailWord_6959402) baseStart_6959402 baseEnd_6959402 := by
    simpa [prefixWord, tailWord_6959402, baseEnd_6959402] using wordTrace_append hprefix tailTrace_6959402
  have hstable : (prefixWord ++ tailWord_6959402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959402).length < 2 ^ (prefixWord ++ tailWord_6959402).sum := by decide
  have hdescent : baseEnd_6959402 < baseStart_6959402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959412 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_6959412 : Nat := 118140960795 + 6959412 * 2 ^ 59
def prefixEnd_6959412 : Nat := 4983230072969 + 3 ^ 40 * 6959412 * 2
def baseEnd_6959412 : Nat := 3573523428668030502244253

theorem tailTrace_6959412 : CollatzResearch.WordTrace tailWord_6959412 prefixEnd_6959412 3573523428668030502244253 := by
  unfold tailWord_6959412
  simp only [CollatzResearch.WordTrace]
  refine ⟨126915304331623185893792245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169220405775497581191722993 126915304331623185893792245)
  ·
    refine ⟨11898309781089673677543023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126915304331623185893792245 11898309781089673677543023)
    ·
      refine ⟨17847464671634510516314535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11898309781089673677543023 17847464671634510516314535)
      ·
        refine ⟨26771197007451765774471803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17847464671634510516314535 26771197007451765774471803)
        ·
          refine ⟨40156795511177648661707705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26771197007451765774471803 40156795511177648661707705)
          ·
            refine ⟨30117596633383236496280779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40156795511177648661707705 30117596633383236496280779)
            ·
              refine ⟨45176394950074854744421169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30117596633383236496280779 45176394950074854744421169)
              ·
                refine ⟨33882296212556141058315877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45176394950074854744421169 33882296212556141058315877)
                ·
                  refine ⟨6352930539854276448434227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33882296212556141058315877 6352930539854276448434227)
                  ·
                    refine ⟨9529395809781414672651341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6352930539854276448434227 9529395809781414672651341)
                    ·
                      refine ⟨3573523428668030502244253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9529395809781414672651341 3573523428668030502244253)
                      ·
                        rfl

theorem cell23_6959412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_6959412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959412 prefixEnd_6959412 := by exact prefixLift 6959412
  have htrace : WordTrace (prefixWord ++ tailWord_6959412) baseStart_6959412 baseEnd_6959412 := by
    simpa [prefixWord, tailWord_6959412, baseEnd_6959412] using wordTrace_append hprefix tailTrace_6959412
  have hstable : (prefixWord ++ tailWord_6959412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959412).length < 2 ^ (prefixWord ++ tailWord_6959412).sum := by decide
  have hdescent : baseEnd_6959412 < baseStart_6959412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959451 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_6959451 : Nat := 118140960795 + 6959451 * 2 ^ 59
def prefixEnd_6959451 : Nat := 4983230072969 + 3 ^ 40 * 6959451 * 2
def baseEnd_6959451 : Nat := 3573543454413555849656573

theorem tailTrace_6959451 : CollatzResearch.WordTrace tailWord_6959451 prefixEnd_6959451 3573543454413555849656573 := by
  unfold tailWord_6959451
  simp only [CollatzResearch.WordTrace]
  refine ⟨253832031110105081448254207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169221354073403387632169471 253832031110105081448254207)
  ·
    refine ⟨380748046665157622172381311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253832031110105081448254207 380748046665157622172381311)
    ·
      refine ⟨571122069997736433258571967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380748046665157622172381311 571122069997736433258571967)
      ·
        refine ⟨856683104996604649887857951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571122069997736433258571967 856683104996604649887857951)
        ·
          refine ⟨1285024657494906974831786927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856683104996604649887857951 1285024657494906974831786927)
          ·
            refine ⟨1927536986242360462247680391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285024657494906974831786927 1927536986242360462247680391)
            ·
              refine ⟨2891305479363540693371520587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927536986242360462247680391 2891305479363540693371520587)
              ·
                refine ⟨4336958219045311040057280881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891305479363540693371520587 4336958219045311040057280881)
                ·
                  refine ⟨3252718664283983280042960661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4336958219045311040057280881 3252718664283983280042960661)
                  ·
                    refine ⟨152471187388311716252013781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3252718664283983280042960661 152471187388311716252013781)
                    ·
                      refine ⟨3573543454413555849656573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152471187388311716252013781 3573543454413555849656573)
                      ·
                        rfl

theorem cell23_6959451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_6959451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959451 prefixEnd_6959451 := by exact prefixLift 6959451
  have htrace : WordTrace (prefixWord ++ tailWord_6959451) baseStart_6959451 baseEnd_6959451 := by
    simpa [prefixWord, tailWord_6959451, baseEnd_6959451] using wordTrace_append hprefix tailTrace_6959451
  have hstable : (prefixWord ++ tailWord_6959451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959451).length < 2 ^ (prefixWord ++ tailWord_6959451).sum := by decide
  have hdescent : baseEnd_6959451 < baseStart_6959451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959456 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 1, 3, 2]
def baseStart_6959456 : Nat := 118140960795 + 6959456 * 2 ^ 59
def prefixEnd_6959456 : Nat := 4983230072969 + 3 ^ 40 * 6959456 * 2
def baseEnd_6959456 : Nat := 3573546021816828330094051

theorem tailTrace_6959456 : CollatzResearch.WordTrace tailWord_6959456 prefixEnd_6959456 3573546021816828330094051 := by
  unfold tailWord_6959456
  simp only [CollatzResearch.WordTrace]
  refine ⟨126916106737543483651093111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169221475650057978201457481 126916106737543483651093111)
  ·
    refine ⟨190374160106315225476639667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126916106737543483651093111 190374160106315225476639667)
    ·
      refine ⟨285561240159472838214959501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190374160106315225476639667 285561240159472838214959501)
      ·
        refine ⟨107085465059802314330609813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285561240159472838214959501 107085465059802314330609813)
        ·
          refine ⟨5019631174678233484247335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107085465059802314330609813 5019631174678233484247335)
          ·
            refine ⟨7529446762017350226371003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019631174678233484247335 7529446762017350226371003)
            ·
              refine ⟨11294170143026025339556505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7529446762017350226371003 11294170143026025339556505)
              ·
                refine ⟨8470627607269519004667379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11294170143026025339556505 8470627607269519004667379)
                ·
                  refine ⟨12705941410904278507001069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8470627607269519004667379 12705941410904278507001069)
                  ·
                    refine ⟨4764728029089104440125401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12705941410904278507001069 4764728029089104440125401)
                    ·
                      refine ⟨3573546021816828330094051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764728029089104440125401 3573546021816828330094051)
                      ·
                        rfl

theorem cell23_6959456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_6959456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959456 prefixEnd_6959456 := by exact prefixLift 6959456
  have htrace : WordTrace (prefixWord ++ tailWord_6959456) baseStart_6959456 baseEnd_6959456 := by
    simpa [prefixWord, tailWord_6959456, baseEnd_6959456] using wordTrace_append hprefix tailTrace_6959456
  have hstable : (prefixWord ++ tailWord_6959456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959456).length < 2 ^ (prefixWord ++ tailWord_6959456).sum := by decide
  have hdescent : baseEnd_6959456 < baseStart_6959456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959495 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_6959495 : Nat := 118140960795 + 6959495 * 2 ^ 59
def prefixEnd_6959495 : Nat := 4983230072969 + 3 ^ 40 * 6959495 * 2
def baseEnd_6959495 : Nat := 3573566047562353677506371

theorem tailTrace_6959495 : CollatzResearch.WordTrace tailWord_6959495 prefixEnd_6959495 3573566047562353677506371 := by
  unfold tailWord_6959495
  simp only [CollatzResearch.WordTrace]
  refine ⟨253833635921945676962855939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169222423947963784641903959 253833635921945676962855939)
  ·
    refine ⟨380750453882918515444283909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253833635921945676962855939 380750453882918515444283909)
    ·
      refine ⟨71390710103047221645803233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 380750453882918515444283909 71390710103047221645803233)
      ·
        refine ⟨53543032577285416234352425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71390710103047221645803233 53543032577285416234352425)
        ·
          refine ⟨40157274432964062175764319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53543032577285416234352425 40157274432964062175764319)
          ·
            refine ⟨60235911649446093263646479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40157274432964062175764319 60235911649446093263646479)
            ·
              refine ⟨90353867474169139895469719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60235911649446093263646479 90353867474169139895469719)
              ·
                refine ⟨135530801211253709843204579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90353867474169139895469719 135530801211253709843204579)
                ·
                  refine ⟨203296201816880564764806869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135530801211253709843204579 203296201816880564764806869)
                  ·
                    refine ⟨4764754730083138236675161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 203296201816880564764806869 4764754730083138236675161)
                    ·
                      refine ⟨3573566047562353677506371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764754730083138236675161 3573566047562353677506371)
                      ·
                        rfl

theorem cell23_6959495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_6959495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959495 prefixEnd_6959495 := by exact prefixLift 6959495
  have htrace : WordTrace (prefixWord ++ tailWord_6959495) baseStart_6959495 baseEnd_6959495 := by
    simpa [prefixWord, tailWord_6959495, baseEnd_6959495] using wordTrace_append hprefix tailTrace_6959495
  have hstable : (prefixWord ++ tailWord_6959495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959495).length < 2 ^ (prefixWord ++ tailWord_6959495).sum := by decide
  have hdescent : baseEnd_6959495 < baseStart_6959495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959502 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6959502 : Nat := 118140960795 + 6959502 * 2 ^ 59
def prefixEnd_6959502 : Nat := 4983230072969 + 3 ^ 40 * 6959502 * 2
def baseEnd_6959502 : Nat := 3573569641926935150118839

theorem tailTrace_6959502 : CollatzResearch.WordTrace tailWord_6959502 prefixEnd_6959502 3573569641926935150118839 := by
  unfold tailWord_6959502
  simp only [CollatzResearch.WordTrace]
  refine ⟨31729236404115039644795095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169222594155280211438907173 31729236404115039644795095)
  ·
    refine ⟨47593854606172559467192643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31729236404115039644795095 47593854606172559467192643)
    ·
      refine ⟨71390781909258839200788965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47593854606172559467192643 71390781909258839200788965)
      ·
        refine ⟨13385771607986032350147931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71390781909258839200788965 13385771607986032350147931)
        ·
          refine ⟨20078657411979048525221897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13385771607986032350147931 20078657411979048525221897)
          ·
            refine ⟨15058993058984286393916423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20078657411979048525221897 15058993058984286393916423)
            ·
              refine ⟨22588489588476429590874635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15058993058984286393916423 22588489588476429590874635)
              ·
                refine ⟨33882734382714644386311953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22588489588476429590874635 33882734382714644386311953)
                ·
                  refine ⟨25412050787035983289733965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33882734382714644386311953 25412050787035983289733965)
                  ·
                    refine ⟨9529519045138493733650237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25412050787035983289733965 9529519045138493733650237)
                    ·
                      refine ⟨3573569641926935150118839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9529519045138493733650237 3573569641926935150118839)
                      ·
                        rfl

theorem cell23_6959502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6959502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959502 prefixEnd_6959502 := by exact prefixLift 6959502
  have htrace : WordTrace (prefixWord ++ tailWord_6959502) baseStart_6959502 baseEnd_6959502 := by
    simpa [prefixWord, tailWord_6959502, baseEnd_6959502] using wordTrace_append hprefix tailTrace_6959502
  have hstable : (prefixWord ++ tailWord_6959502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959502).length < 2 ^ (prefixWord ++ tailWord_6959502).sum := by decide
  have hdescent : baseEnd_6959502 < baseStart_6959502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959525 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 6, 2]
def baseStart_6959525 : Nat := 118140960795 + 6959525 * 2 ^ 59
def prefixEnd_6959525 : Nat := 4983230072969 + 3 ^ 40 * 6959525 * 2
def baseEnd_6959525 : Nat := 3573581451981988560131233

theorem tailTrace_6959525 : CollatzResearch.WordTrace tailWord_6959525 prefixEnd_6959525 3573581451981988560131233 := by
  unfold tailWord_6959525
  simp only [CollatzResearch.WordTrace]
  refine ⟨253834730111836992086448029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169223153407891328057632019 253834730111836992086448029)
  ·
    refine ⟨95188023791938872032418011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253834730111836992086448029 95188023791938872032418011)
    ·
      refine ⟨142782035687908308048627017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95188023791938872032418011 142782035687908308048627017)
      ·
        refine ⟨107086526765931231036470263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142782035687908308048627017 107086526765931231036470263)
        ·
          refine ⟨160629790148896846554705395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107086526765931231036470263 160629790148896846554705395)
          ·
            refine ⟨240944685223345269832058093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160629790148896846554705395 240944685223345269832058093)
            ·
              refine ⟨90354256958754476187021785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240944685223345269832058093 90354256958754476187021785)
              ·
                refine ⟨67765692719065857140266339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90354256958754476187021785 67765692719065857140266339)
                ·
                  refine ⟨101648539078598785710399509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67765692719065857140266339 101648539078598785710399509)
                  ·
                    refine ⟨4764775269309318080174977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101648539078598785710399509 4764775269309318080174977)
                    ·
                      refine ⟨3573581451981988560131233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764775269309318080174977 3573581451981988560131233)
                      ·
                        rfl

theorem cell23_6959525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_6959525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959525 prefixEnd_6959525 := by exact prefixLift 6959525
  have htrace : WordTrace (prefixWord ++ tailWord_6959525) baseStart_6959525 baseEnd_6959525 := by
    simpa [prefixWord, tailWord_6959525, baseEnd_6959525] using wordTrace_append hprefix tailTrace_6959525
  have hstable : (prefixWord ++ tailWord_6959525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959525).length < 2 ^ (prefixWord ++ tailWord_6959525).sum := by decide
  have hdescent : baseEnd_6959525 < baseStart_6959525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959538 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_6959538 : Nat := 118140960795 + 6959538 * 2 ^ 59
def prefixEnd_6959538 : Nat := 4983230072969 + 3 ^ 40 * 6959538 * 2
def baseEnd_6959538 : Nat := 3573588127230497009268673

theorem tailTrace_6959538 : CollatzResearch.WordTrace tailWord_6959538 prefixEnd_6959538 3573588127230497009268673 := by
  unfold tailWord_6959538
  simp only [CollatzResearch.WordTrace]
  refine ⟨63458801065197473826667817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169223469507193263537780845 63458801065197473826667817)
  ·
    refine ⟨47594100798898105370000863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63458801065197473826667817 47594100798898105370000863)
    ·
      refine ⟨71391151198347158055001295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47594100798898105370000863 71391151198347158055001295)
      ·
        refine ⟨107086726797520737082501943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71391151198347158055001295 107086726797520737082501943)
        ·
          refine ⟨160630090196281105623752915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107086726797520737082501943 160630090196281105623752915)
          ·
            refine ⟨240945135294421658435629373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160630090196281105623752915 240945135294421658435629373)
            ·
              refine ⟨90354425735408121913361015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240945135294421658435629373 90354425735408121913361015)
              ·
                refine ⟨135531638603112182870041523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90354425735408121913361015 135531638603112182870041523)
                ·
                  refine ⟨203297457904668274305062285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135531638603112182870041523 203297457904668274305062285)
                  ·
                    refine ⟨76236546714250602864398357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203297457904668274305062285 76236546714250602864398357)
                    ·
                      refine ⟨3573588127230497009268673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76236546714250602864398357 3573588127230497009268673)
                      ·
                        rfl

theorem cell23_6959538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_6959538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959538 prefixEnd_6959538 := by exact prefixLift 6959538
  have htrace : WordTrace (prefixWord ++ tailWord_6959538) baseStart_6959538 baseEnd_6959538 := by
    simpa [prefixWord, tailWord_6959538, baseEnd_6959538] using wordTrace_append hprefix tailTrace_6959538
  have hstable : (prefixWord ++ tailWord_6959538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959538).length < 2 ^ (prefixWord ++ tailWord_6959538).sum := by decide
  have hdescent : baseEnd_6959538 < baseStart_6959538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959595 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 1, 5]
def baseStart_6959595 : Nat := 118140960795 + 6959595 * 2 ^ 59
def prefixEnd_6959595 : Nat := 4983230072969 + 3 ^ 40 * 6959595 * 2
def baseEnd_6959595 : Nat := 1191205798542601095418637

theorem tailTrace_6959595 : CollatzResearch.WordTrace tailWord_6959595 prefixEnd_6959595 1191205798542601095418637 := by
  unfold tailWord_6959595
  simp only [CollatzResearch.WordTrace]
  refine ⟨253837283221583394041496239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169224855481055596027664159 253837283221583394041496239)
  ·
    refine ⟨380755924832375091062244359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253837283221583394041496239 380755924832375091062244359)
    ·
      refine ⟨571133887248562636593366539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380755924832375091062244359 571133887248562636593366539)
      ·
        refine ⟨856700830872843954890049809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571133887248562636593366539 856700830872843954890049809)
        ·
          refine ⟨642525623154632966167537357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856700830872843954890049809 642525623154632966167537357)
          ·
            refine ⟨240947108682987362312826509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642525623154632966167537357 240947108682987362312826509)
            ·
              refine ⟨90355165756120260867309941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240947108682987362312826509 90355165756120260867309941)
              ·
                refine ⟨8470796789636274456310307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90355165756120260867309941 8470796789636274456310307)
                ·
                  refine ⟨12706195184454411684465461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8470796789636274456310307 12706195184454411684465461)
                  ·
                    refine ⟨1191205798542601095418637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12706195184454411684465461 1191205798542601095418637)
                    ·
                      rfl

theorem cell23_6959595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 5].length) (baseStart_6959595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959595 prefixEnd_6959595 := by exact prefixLift 6959595
  have htrace : WordTrace (prefixWord ++ tailWord_6959595) baseStart_6959595 baseEnd_6959595 := by
    simpa [prefixWord, tailWord_6959595, baseEnd_6959595] using wordTrace_append hprefix tailTrace_6959595
  have hstable : (prefixWord ++ tailWord_6959595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959595).length < 2 ^ (prefixWord ++ tailWord_6959595).sum := by decide
  have hdescent : baseEnd_6959595 < baseStart_6959595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959609 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 1, 1, 3]
def baseStart_6959609 : Nat := 118140960795 + 6959609 * 2 ^ 59
def prefixEnd_6959609 : Nat := 4983230072969 + 3 ^ 40 * 6959609 * 2
def baseEnd_6959609 : Nat := 3573624584356966231480847

theorem tailTrace_6959609 : CollatzResearch.WordTrace tailWord_6959609 prefixEnd_6959609 3573624584356966231480847 := by
  unfold tailWord_6959609
  simp only [CollatzResearch.WordTrace]
  refine ⟨253837793843532674432505881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169225195895688449621670587 253837793843532674432505881)
  ·
    refine ⟨190378345382649505824379411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253837793843532674432505881 190378345382649505824379411)
    ·
      refine ⟨285567518073974258736569117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190378345382649505824379411 285567518073974258736569117)
      ·
        refine ⟨107087819277740347026213419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285567518073974258736569117 107087819277740347026213419)
        ·
          refine ⟨160631728916610520539320129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107087819277740347026213419 160631728916610520539320129)
          ·
            refine ⟨120473796687457890404490097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160631728916610520539320129 120473796687457890404490097)
            ·
              refine ⟨90355347515593417803367573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120473796687457890404490097 90355347515593417803367573)
              ·
                refine ⟨4235406914793441459532855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90355347515593417803367573 4235406914793441459532855)
                ·
                  refine ⟨6353110372190162189299283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235406914793441459532855 6353110372190162189299283)
                  ·
                    refine ⟨9529665558285243283948925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353110372190162189299283 9529665558285243283948925)
                    ·
                      refine ⟨3573624584356966231480847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9529665558285243283948925 3573624584356966231480847)
                      ·
                        rfl

theorem cell23_6959609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_6959609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959609 prefixEnd_6959609 := by exact prefixLift 6959609
  have htrace : WordTrace (prefixWord ++ tailWord_6959609) baseStart_6959609 baseEnd_6959609 := by
    simpa [prefixWord, tailWord_6959609, baseEnd_6959609] using wordTrace_append hprefix tailTrace_6959609
  have hstable : (prefixWord ++ tailWord_6959609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959609).length < 2 ^ (prefixWord ++ tailWord_6959609).sum := by decide
  have hdescent : baseEnd_6959609 < baseStart_6959609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959615 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_6959615 : Nat := 118140960795 + 6959615 * 2 ^ 59
def prefixEnd_6959615 : Nat := 4983230072969 + 3 ^ 40 * 6959615 * 2
def baseEnd_6959615 : Nat := 3573627665240893208005819

theorem tailTrace_6959615 : CollatzResearch.WordTrace tailWord_6959615 prefixEnd_6959615 3573627665240893208005819 := by
  unfold tailWord_6959615
  simp only [CollatzResearch.WordTrace]
  refine ⟨253838012681510937457224299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169225341787673958304816199 253838012681510937457224299)
  ·
    refine ⟨380757019022266406185836449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253838012681510937457224299 380757019022266406185836449)
    ·
      refine ⟨285567764266699804639377337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380757019022266406185836449 285567764266699804639377337)
      ·
        refine ⟨214175823200024853479533003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285567764266699804639377337 214175823200024853479533003)
        ·
          refine ⟨321263734800037280219299505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214175823200024853479533003 321263734800037280219299505)
          ·
            refine ⟨240947801100027960164474629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321263734800037280219299505 240947801100027960164474629)
            ·
              refine ⟨45177712706255242530838993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240947801100027960164474629 45177712706255242530838993)
              ·
                refine ⟨33883284529691431898129245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45177712706255242530838993 33883284529691431898129245)
                ·
                  refine ⟨12706231698634286961798467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33883284529691431898129245 12706231698634286961798467)
                  ·
                    refine ⟨19059347547951430442697701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12706231698634286961798467 19059347547951430442697701)
                    ·
                      refine ⟨3573627665240893208005819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19059347547951430442697701 3573627665240893208005819)
                      ·
                        rfl

theorem cell23_6959615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_6959615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959615 prefixEnd_6959615 := by exact prefixLift 6959615
  have htrace : WordTrace (prefixWord ++ tailWord_6959615) baseStart_6959615 baseEnd_6959615 := by
    simpa [prefixWord, tailWord_6959615, baseEnd_6959615] using wordTrace_append hprefix tailTrace_6959615
  have hstable : (prefixWord ++ tailWord_6959615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959615).length < 2 ^ (prefixWord ++ tailWord_6959615).sum := by decide
  have hdescent : baseEnd_6959615 < baseStart_6959615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959625 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 6, 4]
def baseStart_6959625 : Nat := 118140960795 + 6959625 * 2 ^ 59
def prefixEnd_6959625 : Nat := 4983230072969 + 3 ^ 40 * 6959625 * 2
def baseEnd_6959625 : Nat := 1191210933349146056293591

theorem tailTrace_6959625 : CollatzResearch.WordTrace tailWord_6959625 prefixEnd_6959625 1191210933349146056293591 := by
  unfold tailWord_6959625
  simp only [CollatzResearch.WordTrace]
  refine ⟨253838377411474709165088329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169225584940983139443392219 253838377411474709165088329)
  ·
    refine ⟨190378783058606031873816247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253838377411474709165088329 190378783058606031873816247)
    ·
      refine ⟨285568174587909047810724371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190378783058606031873816247 285568174587909047810724371)
      ·
        refine ⟨428352261881863571716086557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285568174587909047810724371 428352261881863571716086557)
        ·
          refine ⟨160632098205698839393532459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428352261881863571716086557 160632098205698839393532459)
          ·
            refine ⟨240948147308548259090298689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160632098205698839393532459 240948147308548259090298689)
            ·
              refine ⟨180711110481411194317724017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240948147308548259090298689 180711110481411194317724017)
              ·
                refine ⟨135533332861058395738293013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180711110481411194317724017 135533332861058395738293013)
                ·
                  refine ⟨6353124977862112300232485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135533332861058395738293013 6353124977862112300232485)
                  ·
                    refine ⟨1191210933349146056293591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353124977862112300232485 1191210933349146056293591)
                    ·
                      rfl

theorem cell23_6959625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 4].length) (baseStart_6959625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959625 prefixEnd_6959625 := by exact prefixLift 6959625
  have htrace : WordTrace (prefixWord ++ tailWord_6959625) baseStart_6959625 baseEnd_6959625 := by
    simpa [prefixWord, tailWord_6959625, baseEnd_6959625] using wordTrace_append hprefix tailTrace_6959625
  have hstable : (prefixWord ++ tailWord_6959625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959625).length < 2 ^ (prefixWord ++ tailWord_6959625).sum := by decide
  have hdescent : baseEnd_6959625 < baseStart_6959625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959636 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6959636 : Nat := 118140960795 + 6959636 * 2 ^ 59
def prefixEnd_6959636 : Nat := 4983230072969 + 3 ^ 40 * 6959636 * 2
def baseEnd_6959636 : Nat := 3573638448334637625843223

theorem tailTrace_6959636 : CollatzResearch.WordTrace tailWord_6959636 prefixEnd_6959636 3573638448334637625843223 := by
  unfold tailWord_6959636
  simp only [CollatzResearch.WordTrace]
  refine ⟨126919389307217429021869381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169225852409623238695825841 126919389307217429021869381)
  ·
    refine ⟨23797385495103267941600509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126919389307217429021869381 23797385495103267941600509)
    ·
      refine ⟨8924019560663725478100191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23797385495103267941600509 8924019560663725478100191)
      ·
        refine ⟨13386029340995588217150287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924019560663725478100191 13386029340995588217150287)
        ·
          refine ⟨20079044011493382325725431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13386029340995588217150287 20079044011493382325725431)
          ·
            refine ⟨30118566017240073488588147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20079044011493382325725431 30118566017240073488588147)
            ·
              refine ⟨45177849025860110232882221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30118566017240073488588147 45177849025860110232882221)
              ·
                refine ⟨16941693384697541337330833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45177849025860110232882221 16941693384697541337330833)
                ·
                  refine ⟨12706270038523156002998125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16941693384697541337330833 12706270038523156002998125)
                  ·
                    refine ⟨4764851264446183501124297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12706270038523156002998125 4764851264446183501124297)
                    ·
                      refine ⟨3573638448334637625843223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764851264446183501124297 3573638448334637625843223)
                      ·
                        rfl

theorem cell23_6959636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6959636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959636 prefixEnd_6959636 := by exact prefixLift 6959636
  have htrace : WordTrace (prefixWord ++ tailWord_6959636) baseStart_6959636 baseEnd_6959636 := by
    simpa [prefixWord, tailWord_6959636, baseEnd_6959636] using wordTrace_append hprefix tailTrace_6959636
  have hstable : (prefixWord ++ tailWord_6959636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959636).length < 2 ^ (prefixWord ++ tailWord_6959636).sum := by decide
  have hdescent : baseEnd_6959636 < baseStart_6959636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959649 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6959649 : Nat := 118140960795 + 6959649 * 2 ^ 59
def prefixEnd_6959649 : Nat := 4983230072969 + 3 ^ 40 * 6959649 * 2
def baseEnd_6959649 : Nat := 3573645123583146074980663

theorem tailTrace_6959649 : CollatzResearch.WordTrace tailWord_6959649 prefixEnd_6959649 3573645123583146074980663 := by
  unfold tailWord_6959649
  simp only [CollatzResearch.WordTrace]
  refine ⟨253839252763387761263962001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169226168508925174175974667 253839252763387761263962001)
  ·
    refine ⟨190379439572540820947971501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253839252763387761263962001 190379439572540820947971501)
    ·
      refine ⟨71392289839702807855489313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190379439572540820947971501 71392289839702807855489313)
      ·
        refine ⟨53544217379777105891616985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71392289839702807855489313 53544217379777105891616985)
        ·
          refine ⟨40158163034832829418712739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53544217379777105891616985 40158163034832829418712739)
          ·
            refine ⟨60237244552249244128069109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40158163034832829418712739 60237244552249244128069109)
            ·
              refine ⟨5647241676773366637006479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60237244552249244128069109 5647241676773366637006479)
              ·
                refine ⟨8470862515160049955509719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647241676773366637006479 8470862515160049955509719)
                ·
                  refine ⟨12706293772740074933264579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8470862515160049955509719 12706293772740074933264579)
                  ·
                    refine ⟨19059440659110112399896869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12706293772740074933264579 19059440659110112399896869)
                    ·
                      refine ⟨3573645123583146074980663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19059440659110112399896869 3573645123583146074980663)
                      ·
                        rfl

theorem cell23_6959649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6959649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959649 prefixEnd_6959649 := by exact prefixLift 6959649
  have htrace : WordTrace (prefixWord ++ tailWord_6959649) baseStart_6959649 baseEnd_6959649 := by
    simpa [prefixWord, tailWord_6959649, baseEnd_6959649] using wordTrace_append hprefix tailTrace_6959649
  have hstable : (prefixWord ++ tailWord_6959649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959649).length < 2 ^ (prefixWord ++ tailWord_6959649).sum := by decide
  have hdescent : baseEnd_6959649 < baseStart_6959649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959686 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6959686 : Nat := 118140960795 + 6959686 * 2 ^ 59
def prefixEnd_6959686 : Nat := 4983230072969 + 3 ^ 40 * 6959686 * 2
def baseEnd_6959686 : Nat := 3573664122367362430217993

theorem tailTrace_6959686 : CollatzResearch.WordTrace tailWord_6959686 prefixEnd_6959686 3573664122367362430217993 := by
  unfold tailWord_6959686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932518820757928643220591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169227068176169144388705941 7932518820757928643220591)
  ·
    refine ⟨11898778231136892964830887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7932518820757928643220591 11898778231136892964830887)
    ·
      refine ⟨17848167346705339447246331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11898778231136892964830887 17848167346705339447246331)
      ·
        refine ⟨26772251020058009170869497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17848167346705339447246331 26772251020058009170869497)
        ·
          refine ⟨20079188265043506878152123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26772251020058009170869497 20079188265043506878152123)
          ·
            refine ⟨30118782397565260317228185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20079188265043506878152123 30118782397565260317228185)
            ·
              refine ⟨22589086798173945237921139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30118782397565260317228185 22589086798173945237921139)
              ·
                refine ⟨33883630197260917856881709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22589086798173945237921139 33883630197260917856881709)
                ·
                  refine ⟨12706361323972844196330641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33883630197260917856881709 12706361323972844196330641)
                  ·
                    refine ⟨9529770992979633147247981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12706361323972844196330641 9529770992979633147247981)
                    ·
                      refine ⟨3573664122367362430217993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9529770992979633147247981 3573664122367362430217993)
                      ·
                        rfl

theorem cell23_6959686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6959686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959686 prefixEnd_6959686 := by exact prefixLift 6959686
  have htrace : WordTrace (prefixWord ++ tailWord_6959686) baseStart_6959686 baseEnd_6959686 := by
    simpa [prefixWord, tailWord_6959686, baseEnd_6959686] using wordTrace_append hprefix tailTrace_6959686
  have hstable : (prefixWord ++ tailWord_6959686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959686).length < 2 ^ (prefixWord ++ tailWord_6959686).sum := by decide
  have hdescent : baseEnd_6959686 < baseStart_6959686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959715 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 4, 6]
def baseStart_6959715 : Nat := 118140960795 + 6959715 * 2 ^ 59
def prefixEnd_6959715 : Nat := 4983230072969 + 3 ^ 40 * 6959715 * 2
def baseEnd_6959715 : Nat := 1191226337768780938918453

theorem tailTrace_6959715 : CollatzResearch.WordTrace tailWord_6959715 prefixEnd_6959715 1191226337768780938918453 := by
  unfold tailWord_6959715
  simp only [CollatzResearch.WordTrace]
  refine ⟨253841659981148654535864599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169227773320765769690576399 253841659981148654535864599)
  ·
    refine ⟨380762489971722981803796899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253841659981148654535864599 380762489971722981803796899)
    ·
      refine ⟨571143734957584472705695349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380762489971722981803796899 571143734957584472705695349)
      ·
        refine ⟨53544725152273544316158939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 571143734957584472705695349 53544725152273544316158939)
        ·
          refine ⟨80317087728410316474238409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53544725152273544316158939 80317087728410316474238409)
          ·
            refine ⟨60237815796307737355678807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80317087728410316474238409 60237815796307737355678807)
            ·
              refine ⟨90356723694461606033518211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60237815796307737355678807 90356723694461606033518211)
              ·
                refine ⟨135535085541692409050277317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90356723694461606033518211 135535085541692409050277317)
                ·
                  refine ⟨25412828539067326696926997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135535085541692409050277317 25412828539067326696926997)
                  ·
                    refine ⟨1191226337768780938918453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25412828539067326696926997 1191226337768780938918453)
                    ·
                      rfl

theorem cell23_6959715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 6].length) (baseStart_6959715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959715 prefixEnd_6959715 := by exact prefixLift 6959715
  have htrace : WordTrace (prefixWord ++ tailWord_6959715) baseStart_6959715 baseEnd_6959715 := by
    simpa [prefixWord, tailWord_6959715, baseEnd_6959715] using wordTrace_append hprefix tailTrace_6959715
  have hstable : (prefixWord ++ tailWord_6959715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959715).length < 2 ^ (prefixWord ++ tailWord_6959715).sum := by decide
  have hdescent : baseEnd_6959715 < baseStart_6959715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959733 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6959733 : Nat := 118140960795 + 6959733 * 2 ^ 59
def prefixEnd_6959733 : Nat := 4983230072969 + 3 ^ 40 * 6959733 * 2
def baseEnd_6959733 : Nat := 3573688255958123746330277

theorem tailTrace_6959733 : CollatzResearch.WordTrace tailWord_6959733 prefixEnd_6959733 3573688255958123746330277 := by
  unfold tailWord_6959733
  simp only [CollatzResearch.WordTrace]
  refine ⟨253842316495083443610019853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169228210996722295740013235 253842316495083443610019853)
  ·
    refine ⟨95190868685656291353757445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253842316495083443610019853 95190868685656291353757445)
    ·
      refine ⟨17848287878560554628829521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95190868685656291353757445 17848287878560554628829521)
      ·
        refine ⟨13386215908920415971622141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17848287878560554628829521 13386215908920415971622141)
        ·
          refine ⟨5019830965845155989358303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13386215908920415971622141 5019830965845155989358303)
          ·
            refine ⟨7529746448767733984037455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019830965845155989358303 7529746448767733984037455)
            ·
              refine ⟨11294619673151600976056183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7529746448767733984037455 11294619673151600976056183)
              ·
                refine ⟨16941929509727401464084275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11294619673151600976056183 16941929509727401464084275)
                ·
                  refine ⟨25412894264591102196126413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16941929509727401464084275 25412894264591102196126413)
                  ·
                    refine ⟨9529835349221663323547405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25412894264591102196126413 9529835349221663323547405)
                    ·
                      refine ⟨3573688255958123746330277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9529835349221663323547405 3573688255958123746330277)
                      ·
                        rfl

theorem cell23_6959733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6959733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959733 prefixEnd_6959733 := by exact prefixLift 6959733
  have htrace : WordTrace (prefixWord ++ tailWord_6959733) baseStart_6959733 baseEnd_6959733 := by
    simpa [prefixWord, tailWord_6959733, baseEnd_6959733] using wordTrace_append hprefix tailTrace_6959733
  have hstable : (prefixWord ++ tailWord_6959733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959733).length < 2 ^ (prefixWord ++ tailWord_6959733).sum := by decide
  have hdescent : baseEnd_6959733 < baseStart_6959733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959765 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6959765 : Nat := 118140960795 + 6959765 * 2 ^ 59
def prefixEnd_6959765 : Nat := 4983230072969 + 3 ^ 40 * 6959765 * 2
def baseEnd_6959765 : Nat := 3573704687339067621130129

theorem tailTrace_6959765 : CollatzResearch.WordTrace tailWord_6959765 prefixEnd_6959765 3573704687339067621130129 := by
  unfold tailWord_6959765
  simp only [CollatzResearch.WordTrace]
  refine ⟨253843483630967513075184749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169228989087311675383456499 253843483630967513075184749)
  ·
    refine ⟨95191306361612817403194281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253843483630967513075184749 95191306361612817403194281)
    ·
      refine ⟨71393479771209613052395711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95191306361612817403194281 71393479771209613052395711)
      ·
        refine ⟨107090219656814419578593567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71393479771209613052395711 107090219656814419578593567)
        ·
          refine ⟨160635329485221629367890351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107090219656814419578593567 160635329485221629367890351)
          ·
            refine ⟨240952994227832444051835527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160635329485221629367890351 240952994227832444051835527)
            ·
              refine ⟨361429491341748666077753291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240952994227832444051835527 361429491341748666077753291)
              ·
                refine ⟨542144237012622999116629937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361429491341748666077753291 542144237012622999116629937)
                ·
                  refine ⟨406608177759467249337472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542144237012622999116629937 406608177759467249337472453)
                  ·
                    refine ⟨76239033329900109250776085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 406608177759467249337472453 76239033329900109250776085)
                    ·
                      refine ⟨3573704687339067621130129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76239033329900109250776085 3573704687339067621130129)
                      ·
                        rfl

theorem cell23_6959765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6959765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959765 prefixEnd_6959765 := by exact prefixLift 6959765
  have htrace : WordTrace (prefixWord ++ tailWord_6959765) baseStart_6959765 baseEnd_6959765 := by
    simpa [prefixWord, tailWord_6959765, baseEnd_6959765] using wordTrace_append hprefix tailTrace_6959765
  have hstable : (prefixWord ++ tailWord_6959765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959765).length < 2 ^ (prefixWord ++ tailWord_6959765).sum := by decide
  have hdescent : baseEnd_6959765 < baseStart_6959765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959785 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_6959785 : Nat := 118140960795 + 6959785 * 2 ^ 59
def prefixEnd_6959785 : Nat := 4983230072969 + 3 ^ 40 * 6959785 * 2
def baseEnd_6959785 : Nat := 3573714956952157542880037

theorem tailTrace_6959785 : CollatzResearch.WordTrace tailWord_6959785 prefixEnd_6959785 3573714956952157542880037 := by
  unfold tailWord_6959785
  simp only [CollatzResearch.WordTrace]
  refine ⟨253844213090895056490912809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169229475393930037660608539 253844213090895056490912809)
  ·
    refine ⟨190383159818171292368184607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253844213090895056490912809 190383159818171292368184607)
    ·
      refine ⟨285574739727256938552276911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190383159818171292368184607 285574739727256938552276911)
      ·
        refine ⟨428362109590885407828415367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285574739727256938552276911 428362109590885407828415367)
        ·
          refine ⟨642543164386328111742623051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428362109590885407828415367 642543164386328111742623051)
          ·
            refine ⟨963814746579492167613934577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642543164386328111742623051 963814746579492167613934577)
            ·
              refine ⟨722861059934619125710450933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963814746579492167613934577 722861059934619125710450933)
              ·
                refine ⟨67768224368870543035354775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 722861059934619125710450933 67768224368870543035354775)
                ·
                  refine ⟨101652336553305814553032163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67768224368870543035354775 101652336553305814553032163)
                  ·
                    refine ⟨152478504829958721829548245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101652336553305814553032163 152478504829958721829548245)
                    ·
                      refine ⟨3573714956952157542880037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152478504829958721829548245 3573714956952157542880037)
                      ·
                        rfl

theorem cell23_6959785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_6959785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959785 prefixEnd_6959785 := by exact prefixLift 6959785
  have htrace : WordTrace (prefixWord ++ tailWord_6959785) baseStart_6959785 baseEnd_6959785 := by
    simpa [prefixWord, tailWord_6959785, baseEnd_6959785] using wordTrace_append hprefix tailTrace_6959785
  have hstable : (prefixWord ++ tailWord_6959785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959785).length < 2 ^ (prefixWord ++ tailWord_6959785).sum := by decide
  have hdescent : baseEnd_6959785 < baseStart_6959785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959790 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6959790 : Nat := 118140960795 + 6959790 * 2 ^ 59
def prefixEnd_6959790 : Nat := 4983230072969 + 3 ^ 40 * 6959790 * 2
def baseEnd_6959790 : Nat := 3573717524355430023317515

theorem tailTrace_6959790 : CollatzResearch.WordTrace tailWord_6959790 prefixEnd_6959790 3573717524355430023317515 := by
  unfold tailWord_6959790
  simp only [CollatzResearch.WordTrace]
  refine ⟨31730549431984617793105603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169229596970584628229896549 31730549431984617793105603)
  ·
    refine ⟨47595824147976926689658405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31730549431984617793105603 47595824147976926689658405)
    ·
      refine ⟨8924217027745673754310951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47595824147976926689658405 8924217027745673754310951)
      ·
        refine ⟨13386325541618510631466427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924217027745673754310951 13386325541618510631466427)
        ·
          refine ⟨20079488312427765947199641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13386325541618510631466427 20079488312427765947199641)
          ·
            refine ⟨15059616234320824460399731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20079488312427765947199641 15059616234320824460399731)
            ·
              refine ⟨22589424351481236690599597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15059616234320824460399731 22589424351481236690599597)
              ·
                refine ⟨8471034131805463758974849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22589424351481236690599597 8471034131805463758974849)
                ·
                  refine ⟨6353275598854097819231137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8471034131805463758974849 6353275598854097819231137)
                  ·
                    refine ⟨4764956699140573364423353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6353275598854097819231137 4764956699140573364423353)
                    ·
                      refine ⟨3573717524355430023317515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4764956699140573364423353 3573717524355430023317515)
                      ·
                        rfl

theorem cell23_6959790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6959790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959790 prefixEnd_6959790 := by exact prefixLift 6959790
  have htrace : WordTrace (prefixWord ++ tailWord_6959790) baseStart_6959790 baseEnd_6959790 := by
    simpa [prefixWord, tailWord_6959790, baseEnd_6959790] using wordTrace_append hprefix tailTrace_6959790
  have hstable : (prefixWord ++ tailWord_6959790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959790).length < 2 ^ (prefixWord ++ tailWord_6959790).sum := by decide
  have hdescent : baseEnd_6959790 < baseStart_6959790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959860 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6959860 : Nat := 118140960795 + 6959860 * 2 ^ 59
def prefixEnd_6959860 : Nat := 4983230072969 + 3 ^ 40 * 6959860 * 2
def baseEnd_6959860 : Nat := 1191251156000414916480731

theorem tailTrace_6959860 : CollatzResearch.WordTrace tailWord_6959860 prefixEnd_6959860 1191251156000414916480731 := by
  unfold tailWord_6959860
  simp only [CollatzResearch.WordTrace]
  refine ⟨126923474282811672149946517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169231299043748896199928689 126923474282811672149946517)
  ·
    refine ⟨5949537857006797132028743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126923474282811672149946517 5949537857006797132028743)
    ·
      refine ⟨8924306785510195698043115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949537857006797132028743 8924306785510195698043115)
      ·
        refine ⟨13386460178265293547064673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924306785510195698043115 13386460178265293547064673)
        ·
          refine ⟨10039845133698970160298505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13386460178265293547064673 10039845133698970160298505)
          ·
            refine ⟨7529883850274227620223879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10039845133698970160298505 7529883850274227620223879)
            ·
              refine ⟨11294825775411341430335819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7529883850274227620223879 11294825775411341430335819)
              ·
                refine ⟨16942238663117012145503729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11294825775411341430335819 16942238663117012145503729)
                ·
                  refine ⟨12706678997337759109127797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16942238663117012145503729 12706678997337759109127797)
                  ·
                    refine ⟨1191251156000414916480731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12706678997337759109127797 1191251156000414916480731)
                    ·
                      rfl

theorem cell23_6959860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6959860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959860 prefixEnd_6959860 := by exact prefixLift 6959860
  have htrace : WordTrace (prefixWord ++ tailWord_6959860) baseStart_6959860 baseEnd_6959860 := by
    simpa [prefixWord, tailWord_6959860, baseEnd_6959860] using wordTrace_append hprefix tailTrace_6959860
  have hstable : (prefixWord ++ tailWord_6959860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959860).length < 2 ^ (prefixWord ++ tailWord_6959860).sum := by decide
  have hdescent : baseEnd_6959860 < baseStart_6959860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959906 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_6959906 : Nat := 118140960795 + 6959906 * 2 ^ 59
def prefixEnd_6959906 : Nat := 4983230072969 + 3 ^ 40 * 6959906 * 2
def baseEnd_6959906 : Nat := 3573777088111351569466981

theorem tailTrace_6959906 : CollatzResearch.WordTrace tailWord_6959906 prefixEnd_6959906 3573777088111351569466981 := by
  unfold tailWord_6959906
  simp only [CollatzResearch.WordTrace]
  refine ⟨63462156580864173539016893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169232417548971129437378381 63462156580864173539016893)
  ·
    refine ⟨23798308717824065077131335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63462156580864173539016893 23798308717824065077131335)
    ·
      refine ⟨35697463076736097615697003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23798308717824065077131335 35697463076736097615697003)
      ·
        refine ⟨53546194615104146423545505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35697463076736097615697003 53546194615104146423545505)
        ·
          refine ⟨40159645961328109817659129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53546194615104146423545505 40159645961328109817659129)
          ·
            refine ⟨30119734470996082363244347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40159645961328109817659129 30119734470996082363244347)
            ·
              refine ⟨45179601706494123544866521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30119734470996082363244347 45179601706494123544866521)
              ·
                refine ⟨33884701279870592658649891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45179601706494123544866521 33884701279870592658649891)
                ·
                  refine ⟨50827051919805888987974837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33884701279870592658649891 50827051919805888987974837)
                  ·
                    refine ⟨4765036117481802092622641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50827051919805888987974837 4765036117481802092622641)
                    ·
                      refine ⟨3573777088111351569466981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765036117481802092622641 3573777088111351569466981)
                      ·
                        rfl

theorem cell23_6959906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_6959906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959906 prefixEnd_6959906 := by exact prefixLift 6959906
  have htrace : WordTrace (prefixWord ++ tailWord_6959906) baseStart_6959906 baseEnd_6959906 := by
    simpa [prefixWord, tailWord_6959906, baseEnd_6959906] using wordTrace_append hprefix tailTrace_6959906
  have hstable : (prefixWord ++ tailWord_6959906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959906).length < 2 ^ (prefixWord ++ tailWord_6959906).sum := by decide
  have hdescent : baseEnd_6959906 < baseStart_6959906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959936 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 5, 2, 2]
def baseStart_6959936 : Nat := 118140960795 + 6959936 * 2 ^ 59
def prefixEnd_6959936 : Nat := 4983230072969 + 3 ^ 40 * 6959936 * 2
def baseEnd_6959936 : Nat := 3573792492530986452091843

theorem tailTrace_6959936 : CollatzResearch.WordTrace tailWord_6959936 prefixEnd_6959936 3573792492530986452091843 := by
  unfold tailWord_6959936
  simp only [CollatzResearch.WordTrace]
  refine ⟨126924860256674004639829831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169233147008898672853106441 126924860256674004639829831)
  ·
    refine ⟨190387290385011006959744747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126924860256674004639829831 190387290385011006959744747)
    ·
      refine ⟨285580935577516510439617121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190387290385011006959744747 285580935577516510439617121)
      ·
        refine ⟨214185701683137382829712841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285580935577516510439617121 214185701683137382829712841)
        ·
          refine ⟨160639276262353037122284631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214185701683137382829712841 160639276262353037122284631)
          ·
            refine ⟨240958914393529555683426947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160639276262353037122284631 240958914393529555683426947)
            ·
              refine ⟨361438371590294333525140421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240958914393529555683426947 361438371590294333525140421)
              ·
                refine ⟨67769694673180187535963829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361438371590294333525140421 67769694673180187535963829)
                ·
                  refine ⟨6353408875610642581496609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67769694673180187535963829 6353408875610642581496609)
                  ·
                    refine ⟨4765056656707981936122457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6353408875610642581496609 4765056656707981936122457)
                    ·
                      refine ⟨3573792492530986452091843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765056656707981936122457 3573792492530986452091843)
                      ·
                        rfl

theorem cell23_6959936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_6959936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959936 prefixEnd_6959936 := by exact prefixLift 6959936
  have htrace : WordTrace (prefixWord ++ tailWord_6959936) baseStart_6959936 baseEnd_6959936 := by
    simpa [prefixWord, tailWord_6959936, baseEnd_6959936] using wordTrace_append hprefix tailTrace_6959936
  have hstable : (prefixWord ++ tailWord_6959936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959936).length < 2 ^ (prefixWord ++ tailWord_6959936).sum := by decide
  have hdescent : baseEnd_6959936 < baseStart_6959936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959939 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 5]
def baseStart_6959939 : Nat := 118140960795 + 6959939 * 2 ^ 59
def prefixEnd_6959939 : Nat := 4983230072969 + 3 ^ 40 * 6959939 * 2
def baseEnd_6959939 : Nat := 3573794032972949940354329

theorem tailTrace_6959939 : CollatzResearch.WordTrace tailWord_6959939 prefixEnd_6959939 3573794032972949940354329 := by
  unfold tailWord_6959939
  simp only [CollatzResearch.WordTrace]
  refine ⟨253849829932337140792018871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169233219954891427194679247 253849829932337140792018871)
  ·
    refine ⟨380774744898505711188028307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253849829932337140792018871 380774744898505711188028307)
    ·
      refine ⟨571162117347758566782042461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380774744898505711188028307 571162117347758566782042461)
      ·
        refine ⟨214185794005409462543265923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571162117347758566782042461 214185794005409462543265923)
        ·
          refine ⟨321278691008114193814898885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214185794005409462543265923 321278691008114193814898885)
          ·
            refine ⟨60239754564021411340293541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321278691008114193814898885 60239754564021411340293541)
            ·
              refine ⟨11294953980754014626305039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60239754564021411340293541 11294953980754014626305039)
              ·
                refine ⟨16942430971131021939457559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11294953980754014626305039 16942430971131021939457559)
                ·
                  refine ⟨25413646456696532909186339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16942430971131021939457559 25413646456696532909186339)
                  ·
                    refine ⟨38120469685044799363779509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25413646456696532909186339 38120469685044799363779509)
                    ·
                      refine ⟨3573794032972949940354329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38120469685044799363779509 3573794032972949940354329)
                      ·
                        rfl

theorem cell23_6959939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_6959939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959939 prefixEnd_6959939 := by exact prefixLift 6959939
  have htrace : WordTrace (prefixWord ++ tailWord_6959939) baseStart_6959939 baseEnd_6959939 := by
    simpa [prefixWord, tailWord_6959939, baseEnd_6959939] using wordTrace_append hprefix tailTrace_6959939
  have hstable : (prefixWord ++ tailWord_6959939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959939).length < 2 ^ (prefixWord ++ tailWord_6959939).sum := by decide
  have hdescent : baseEnd_6959939 < baseStart_6959939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959959 : List Nat := [1, 1, 3, 2, 4, 2, 2, 8]
def baseStart_6959959 : Nat := 118140960795 + 6959959 * 2 ^ 59
def prefixEnd_6959959 : Nat := 4983230072969 + 3 ^ 40 * 6959959 * 2
def baseEnd_6959959 : Nat := 132363122318001476374231

theorem tailTrace_6959959 : CollatzResearch.WordTrace tailWord_6959959 prefixEnd_6959959 132363122318001476374231 := by
  unfold tailWord_6959959
  simp only [CollatzResearch.WordTrace]
  refine ⟨253850559392264684207746931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169233706261509789471831287 253850559392264684207746931)
  ·
    refine ⟨380775839088397026311620397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253850559392264684207746931 380775839088397026311620397)
    ·
      refine ⟨142790939658148884866857649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380775839088397026311620397 142790939658148884866857649)
      ·
        refine ⟨107093204743611663650143237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142790939658148884866857649 107093204743611663650143237)
        ·
          refine ⟨20079975889427186934401857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107093204743611663650143237 20079975889427186934401857)
          ·
            refine ⟨15059981917070390200801393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20079975889427186934401857 15059981917070390200801393)
            ·
              refine ⟨11294986437802792650601045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15059981917070390200801393 11294986437802792650601045)
              ·
                refine ⟨132363122318001476374231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11294986437802792650601045 132363122318001476374231)
                ·
                  rfl

theorem cell23_6959959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 8].length) (baseStart_6959959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959959 prefixEnd_6959959 := by exact prefixLift 6959959
  have htrace : WordTrace (prefixWord ++ tailWord_6959959) baseStart_6959959 baseEnd_6959959 := by
    simpa [prefixWord, tailWord_6959959, baseEnd_6959959] using wordTrace_append hprefix tailTrace_6959959
  have hstable : (prefixWord ++ tailWord_6959959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959959).length < 2 ^ (prefixWord ++ tailWord_6959959).sum := by decide
  have hdescent : baseEnd_6959959 < baseStart_6959959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959970 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_6959970 : Nat := 118140960795 + 6959970 * 2 ^ 59
def prefixEnd_6959970 : Nat := 4983230072969 + 3 ^ 40 * 6959970 * 2
def baseEnd_6959970 : Nat := 3573809950873239319066687

theorem tailTrace_6959970 : CollatzResearch.WordTrace tailWord_6959970 prefixEnd_6959970 3573809950873239319066687 := by
  unfold tailWord_6959970
  simp only [CollatzResearch.WordTrace]
  refine ⟨63462740148806208271599341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169233973730149888724264909 63462740148806208271599341)
  ·
    refine ⟨23798527555802328101849753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63462740148806208271599341 23798527555802328101849753)
    ·
      refine ⟨17848895666851746076387315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23798527555802328101849753 17848895666851746076387315)
      ·
        refine ⟨26773343500277619114580973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17848895666851746076387315 26773343500277619114580973)
        ·
          refine ⟨10040003812604107167967865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26773343500277619114580973 10040003812604107167967865)
          ·
            refine ⟨7530002859453080375975899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10040003812604107167967865 7530002859453080375975899)
            ·
              refine ⟨11295004289179620563963849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530002859453080375975899 11295004289179620563963849)
              ·
                refine ⟨8471253216884715422972887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11295004289179620563963849 8471253216884715422972887)
                ·
                  refine ⟨12706879825327073134459331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471253216884715422972887 12706879825327073134459331)
                  ·
                    refine ⟨19060319737990609701688997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12706879825327073134459331 19060319737990609701688997)
                    ·
                      refine ⟨3573809950873239319066687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19060319737990609701688997 3573809950873239319066687)
                      ·
                        rfl

theorem cell23_6959970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_6959970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959970 prefixEnd_6959970 := by exact prefixLift 6959970
  have htrace : WordTrace (prefixWord ++ tailWord_6959970) baseStart_6959970 baseEnd_6959970 := by
    simpa [prefixWord, tailWord_6959970, baseEnd_6959970] using wordTrace_append hprefix tailTrace_6959970
  have hstable : (prefixWord ++ tailWord_6959970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959970).length < 2 ^ (prefixWord ++ tailWord_6959970).sum := by decide
  have hdescent : baseEnd_6959970 < baseStart_6959970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6959986 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_6959986 : Nat := 118140960795 + 6959986 * 2 ^ 59
def prefixEnd_6959986 : Nat := 4983230072969 + 3 ^ 40 * 6959986 * 2
def baseEnd_6959986 : Nat := 3573818166563711256466613

theorem tailTrace_6959986 : CollatzResearch.WordTrace tailWord_6959986 prefixEnd_6959986 3573818166563711256466613 := by
  unfold tailWord_6959986
  simp only [CollatzResearch.WordTrace]
  refine ⟨63462886040791716954744953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169234362775444578545986541 63462886040791716954744953)
  ·
    refine ⟨47597164530593787716058715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63462886040791716954744953 47597164530593787716058715)
    ·
      refine ⟨71395746795890681574088073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47597164530593787716058715 71395746795890681574088073)
      ·
        refine ⟨53546810096918011180566055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71395746795890681574088073 53546810096918011180566055)
        ·
          refine ⟨80320215145377016770849083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53546810096918011180566055 80320215145377016770849083)
          ·
            refine ⟨120480322718065525156273625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80320215145377016770849083 120480322718065525156273625)
            ·
              refine ⟨90360242038549143867205219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120480322718065525156273625 90360242038549143867205219)
              ·
                refine ⟨135540363057823715800807829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90360242038549143867205219 135540363057823715800807829)
                ·
                  refine ⟨6353454518335486678162867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135540363057823715800807829 6353454518335486678162867)
                  ·
                    refine ⟨9530181777503230017244301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353454518335486678162867 9530181777503230017244301)
                    ·
                      refine ⟨3573818166563711256466613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530181777503230017244301 3573818166563711256466613)
                      ·
                        rfl

theorem cell23_6959986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_6959986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6959986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6959986 prefixEnd_6959986 := by exact prefixLift 6959986
  have htrace : WordTrace (prefixWord ++ tailWord_6959986) baseStart_6959986 baseEnd_6959986 := by
    simpa [prefixWord, tailWord_6959986, baseEnd_6959986] using wordTrace_append hprefix tailTrace_6959986
  have hstable : (prefixWord ++ tailWord_6959986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6959986).length < 2 ^ (prefixWord ++ tailWord_6959986).sum := by decide
  have hdescent : baseEnd_6959986 < baseStart_6959986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6959986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960003 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 3]
def baseStart_6960003 : Nat := 118140960795 + 6960003 * 2 ^ 59
def prefixEnd_6960003 : Nat := 4983230072969 + 3 ^ 40 * 6960003 * 2
def baseEnd_6960003 : Nat := 3573826895734837689954035

theorem tailTrace_6960003 : CollatzResearch.WordTrace tailWord_6960003 prefixEnd_6960003 3573826895734837689954035 := by
  unfold tailWord_6960003
  simp only [CollatzResearch.WordTrace]
  refine ⟨253852164204105279722348663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169234776136070186481565775 253852164204105279722348663)
  ·
    refine ⟨380778246306157919583522995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253852164204105279722348663 380778246306157919583522995)
    ·
      refine ⟨571167369459236879375284493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380778246306157919583522995 571167369459236879375284493)
      ·
        refine ⟨214187763547213829765731685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 571167369459236879375284493 214187763547213829765731685)
        ·
          refine ⟨40160205665102593081074691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214187763547213829765731685 40160205665102593081074691)
          ·
            refine ⟨60240308497653889621612037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40160205665102593081074691 60240308497653889621612037)
            ·
              refine ⟨11295057843310104304052257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60240308497653889621612037 11295057843310104304052257)
              ·
                refine ⟨8471293382482578228039193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11295057843310104304052257 8471293382482578228039193)
                ·
                  refine ⟨6353470036861933671029395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8471293382482578228039193 6353470036861933671029395)
                  ·
                    refine ⟨9530205055292900506544093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353470036861933671029395 9530205055292900506544093)
                    ·
                      refine ⟨3573826895734837689954035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530205055292900506544093 3573826895734837689954035)
                      ·
                        rfl

theorem cell23_6960003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_6960003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960003 prefixEnd_6960003 := by exact prefixLift 6960003
  have htrace : WordTrace (prefixWord ++ tailWord_6960003) baseStart_6960003 baseEnd_6960003 := by
    simpa [prefixWord, tailWord_6960003, baseEnd_6960003] using wordTrace_append hprefix tailTrace_6960003
  have hstable : (prefixWord ++ tailWord_6960003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960003).length < 2 ^ (prefixWord ++ tailWord_6960003).sum := by decide
  have hdescent : baseEnd_6960003 < baseStart_6960003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960009 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_6960009 : Nat := 118140960795 + 6960009 * 2 ^ 59
def prefixEnd_6960009 : Nat := 4983230072969 + 3 ^ 40 * 6960009 * 2
def baseEnd_6960009 : Nat := 3573829976618764666479007

theorem tailTrace_6960009 : CollatzResearch.WordTrace tailWord_6960009 prefixEnd_6960009 3573829976618764666479007 := by
  unfold tailWord_6960009
  simp only [CollatzResearch.WordTrace]
  refine ⟨253852383042083542747067081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169234922028055695164711387 253852383042083542747067081)
  ·
    refine ⟨190389287281562657060300311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253852383042083542747067081 190389287281562657060300311)
    ·
      refine ⟨285583930922343985590450467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190389287281562657060300311 285583930922343985590450467)
      ·
        refine ⟨428375896383515978385675701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285583930922343985590450467 428375896383515978385675701)
        ·
          refine ⟨40160240285954622973657097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 428375896383515978385675701 40160240285954622973657097)
          ·
            refine ⟨30120180214465967230242823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40160240285954622973657097 30120180214465967230242823)
            ·
              refine ⟨45180270321698950845364235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30120180214465967230242823 45180270321698950845364235)
              ·
                refine ⟨67770405482548426268046353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45180270321698950845364235 67770405482548426268046353)
                ·
                  refine ⟨50827804111911319701034765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67770405482548426268046353 50827804111911319701034765)
                  ·
                    refine ⟨19060426541966744887888037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50827804111911319701034765 19060426541966744887888037)
                    ·
                      refine ⟨3573829976618764666479007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19060426541966744887888037 3573829976618764666479007)
                      ·
                        rfl

theorem cell23_6960009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_6960009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960009 prefixEnd_6960009 := by exact prefixLift 6960009
  have htrace : WordTrace (prefixWord ++ tailWord_6960009) baseStart_6960009 baseEnd_6960009 := by
    simpa [prefixWord, tailWord_6960009, baseEnd_6960009] using wordTrace_append hprefix tailTrace_6960009
  have hstable : (prefixWord ++ tailWord_6960009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960009).length < 2 ^ (prefixWord ++ tailWord_6960009).sum := by decide
  have hdescent : baseEnd_6960009 < baseStart_6960009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960054 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6960054 : Nat := 118140960795 + 6960054 * 2 ^ 59
def prefixEnd_6960054 : Nat := 4983230072969 + 3 ^ 40 * 6960054 * 2
def baseEnd_6960054 : Nat := 3573853083248216990416301

theorem tailTrace_6960054 : CollatzResearch.WordTrace tailWord_6960054 prefixEnd_6960054 3573853083248216990416301 := by
  unfold tailWord_6960054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15865876520432532214528451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169236016217947010288303477 15865876520432532214528451)
  ·
    refine ⟨23798814780648798321792677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15865876520432532214528451 23798814780648798321792677)
    ·
      refine ⟨4462277771371649685336127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23798814780648798321792677 4462277771371649685336127)
      ·
        refine ⟨6693416657057474528004191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462277771371649685336127 6693416657057474528004191)
        ·
          refine ⟨10040124985586211792006287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6693416657057474528004191 10040124985586211792006287)
          ·
            refine ⟨15060187478379317688009431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040124985586211792006287 15060187478379317688009431)
            ·
              refine ⟨22590281217568976532014147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15060187478379317688009431 22590281217568976532014147)
              ·
                refine ⟨33885421826353464798021221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22590281217568976532014147 33885421826353464798021221)
                ·
                  refine ⟨6353516592441274649628979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33885421826353464798021221 6353516592441274649628979)
                  ·
                    refine ⟨9530274888661911974443469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353516592441274649628979 9530274888661911974443469)
                    ·
                      refine ⟨3573853083248216990416301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530274888661911974443469 3573853083248216990416301)
                      ·
                        rfl

theorem cell23_6960054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6960054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960054 prefixEnd_6960054 := by exact prefixLift 6960054
  have htrace : WordTrace (prefixWord ++ tailWord_6960054) baseStart_6960054 baseEnd_6960054 := by
    simpa [prefixWord, tailWord_6960054, baseEnd_6960054] using wordTrace_append hprefix tailTrace_6960054
  have hstable : (prefixWord ++ tailWord_6960054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960054).length < 2 ^ (prefixWord ++ tailWord_6960054).sum := by decide
  have hdescent : baseEnd_6960054 < baseStart_6960054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960076 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_6960076 : Nat := 118140960795 + 6960076 * 2 ^ 59
def prefixEnd_6960076 : Nat := 4983230072969 + 3 ^ 40 * 6960076 * 2
def baseEnd_6960076 : Nat := 3573864379822615904341199

theorem tailTrace_6960076 : CollatzResearch.WordTrace tailWord_6960076 prefixEnd_6960076 3573864379822615904341199 := by
  unfold tailWord_6960076
  simp only [CollatzResearch.WordTrace]
  refine ⟨126927413366420406594878041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169236551155227208793170721 126927413366420406594878041)
  ·
    refine ⟨95195560024815304946158531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126927413366420406594878041 95195560024815304946158531)
    ·
      refine ⟨142793340037222957419237797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95195560024815304946158531 142793340037222957419237797)
      ·
        refine ⟨26773751256979304516107087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142793340037222957419237797 26773751256979304516107087)
        ·
          refine ⟨40160626885468956774160631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26773751256979304516107087 40160626885468956774160631)
          ·
            refine ⟨60240940328203435161240947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40160626885468956774160631 60240940328203435161240947)
            ·
              refine ⟨90361410492305152741861421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60240940328203435161240947 90361410492305152741861421)
              ·
                refine ⟨33885528934614432278198033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90361410492305152741861421 33885528934614432278198033)
                ·
                  refine ⟨25414146700960824208648525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33885528934614432278198033 25414146700960824208648525)
                  ·
                    refine ⟨9530305012860309078243197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25414146700960824208648525 9530305012860309078243197)
                    ·
                      refine ⟨3573864379822615904341199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530305012860309078243197 3573864379822615904341199)
                      ·
                        rfl

theorem cell23_6960076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_6960076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960076 prefixEnd_6960076 := by exact prefixLift 6960076
  have htrace : WordTrace (prefixWord ++ tailWord_6960076) baseStart_6960076 baseEnd_6960076 := by
    simpa [prefixWord, tailWord_6960076, baseEnd_6960076] using wordTrace_append hprefix tailTrace_6960076
  have hstable : (prefixWord ++ tailWord_6960076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960076).length < 2 ^ (prefixWord ++ tailWord_6960076).sum := by decide
  have hdescent : baseEnd_6960076 < baseStart_6960076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960079 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 1, 7]
def baseStart_6960079 : Nat := 118140960795 + 6960079 * 2 ^ 59
def prefixEnd_6960079 : Nat := 4983230072969 + 3 ^ 40 * 6960079 * 2
def baseEnd_6960079 : Nat := 1191288640088193130867895

theorem tailTrace_6960079 : CollatzResearch.WordTrace tailWord_6960079 prefixEnd_6960079 1191288640088193130867895 := by
  unfold tailWord_6960079
  simp only [CollatzResearch.WordTrace]
  refine ⟨253854936151829944702115291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169236624101219963134743527 253854936151829944702115291)
  ·
    refine ⟨380782404227744917053172937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253854936151829944702115291 380782404227744917053172937)
    ·
      refine ⟨285586803170808687789879703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380782404227744917053172937 285586803170808687789879703)
      ·
        refine ⟨428380204756213031684819555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285586803170808687789879703 428380204756213031684819555)
        ·
          refine ⟨642570307134319547527229333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428380204756213031684819555 642570307134319547527229333)
          ·
            refine ⟨30120483146921228790338875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 642570307134319547527229333 30120483146921228790338875)
            ·
              refine ⟨45180724720381843185508313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30120483146921228790338875 45180724720381843185508313)
              ·
                refine ⟨33885543540286382389131235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45180724720381843185508313 33885543540286382389131235)
                ·
                  refine ⟨50828315310429573583696853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33885543540286382389131235 50828315310429573583696853)
                  ·
                    refine ⟨1191288640088193130867895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50828315310429573583696853 1191288640088193130867895)
                    ·
                      rfl

theorem cell23_6960079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_6960079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960079 prefixEnd_6960079 := by exact prefixLift 6960079
  have htrace : WordTrace (prefixWord ++ tailWord_6960079) baseStart_6960079 baseEnd_6960079 := by
    simpa [prefixWord, tailWord_6960079, baseEnd_6960079] using wordTrace_append hprefix tailTrace_6960079
  have hstable : (prefixWord ++ tailWord_6960079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960079).length < 2 ^ (prefixWord ++ tailWord_6960079).sum := by decide
  have hdescent : baseEnd_6960079 < baseStart_6960079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960117 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 7]
def baseStart_6960117 : Nat := 118140960795 + 6960117 * 2 ^ 59
def prefixEnd_6960117 : Nat := 4983230072969 + 3 ^ 40 * 6960117 * 2
def baseEnd_6960117 : Nat := 397098381392161138214279

theorem tailTrace_6960117 : CollatzResearch.WordTrace tailWord_6960117 prefixEnd_6960117 397098381392161138214279 := by
  unfold tailWord_6960117
  simp only [CollatzResearch.WordTrace]
  refine ⟨253856322125692277191998605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169237548083794851461332403 253856322125692277191998605)
  ·
    refine ⟨95196120797134603946999477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253856322125692277191998605 95196120797134603946999477)
    ·
      refine ⟨8924636324731369120031201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95196120797134603946999477 8924636324731369120031201)
      ·
        refine ⟨6693477243548526840023401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8924636324731369120031201 6693477243548526840023401)
        ·
          refine ⟨5020107932661395130017551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6693477243548526840023401 5020107932661395130017551)
          ·
            refine ⟨7530161898992092695026327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020107932661395130017551 7530161898992092695026327)
            ·
              refine ⟨11295242848488139042539491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530161898992092695026327 11295242848488139042539491)
              ·
                refine ⟨16942864272732208563809237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11295242848488139042539491 16942864272732208563809237)
                ·
                  refine ⟨397098381392161138214279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16942864272732208563809237 397098381392161138214279)
                  ·
                    rfl

theorem cell23_6960117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_6960117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960117 prefixEnd_6960117 := by exact prefixLift 6960117
  have htrace : WordTrace (prefixWord ++ tailWord_6960117) baseStart_6960117 baseEnd_6960117 := by
    simpa [prefixWord, tailWord_6960117, baseEnd_6960117] using wordTrace_append hprefix tailTrace_6960117
  have hstable : (prefixWord ++ tailWord_6960117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960117).length < 2 ^ (prefixWord ++ tailWord_6960117).sum := by decide
  have hdescent : baseEnd_6960117 < baseStart_6960117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960183 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_6960183 : Nat := 118140960795 + 6960183 * 2 ^ 59
def prefixEnd_6960183 : Nat := 4983230072969 + 3 ^ 40 * 6960183 * 2
def baseEnd_6960183 : Nat := 3573919322252646985703207

theorem tailTrace_6960183 : CollatzResearch.WordTrace tailWord_6960183 prefixEnd_6960183 3573919322252646985703207 := by
  unfold tailWord_6960183
  simp only [CollatzResearch.WordTrace]
  refine ⟨253858729343453170463901203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169239152895635446975934135 253858729343453170463901203)
  ·
    refine ⟨380788094015179755695851805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253858729343453170463901203 380788094015179755695851805)
    ·
      refine ⟨142795535255692408385944427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380788094015179755695851805 142795535255692408385944427)
      ·
        refine ⟨214193302883538612578916641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142795535255692408385944427 214193302883538612578916641)
        ·
          refine ⟨160644977162653959434187481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214193302883538612578916641 160644977162653959434187481)
          ·
            refine ⟨120483732871990469575640611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160644977162653959434187481 120483732871990469575640611)
            ·
              refine ⟨180725599307985704363460917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120483732871990469575640611 180725599307985704363460917)
              ·
                refine ⟨16943024935123659784074461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180725599307985704363460917 16943024935123659784074461)
                ·
                  refine ⟨6353634350671372419027923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16943024935123659784074461 6353634350671372419027923)
                  ·
                    refine ⟨9530451526007058628541885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353634350671372419027923 9530451526007058628541885)
                    ·
                      refine ⟨3573919322252646985703207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530451526007058628541885 3573919322252646985703207)
                      ·
                        rfl

theorem cell23_6960183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_6960183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960183 prefixEnd_6960183 := by exact prefixLift 6960183
  have htrace : WordTrace (prefixWord ++ tailWord_6960183) baseStart_6960183 baseEnd_6960183 := by
    simpa [prefixWord, tailWord_6960183, baseEnd_6960183] using wordTrace_append hprefix tailTrace_6960183
  have hstable : (prefixWord ++ tailWord_6960183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960183).length < 2 ^ (prefixWord ++ tailWord_6960183).sum := by decide
  have hdescent : baseEnd_6960183 < baseStart_6960183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960186 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_6960186 : Nat := 118140960795 + 6960186 * 2 ^ 59
def prefixEnd_6960186 : Nat := 4983230072969 + 3 ^ 40 * 6960186 * 2
def baseEnd_6960186 : Nat := 1191306954231536824655231

theorem tailTrace_6960186 : CollatzResearch.WordTrace tailWord_6960186 prefixEnd_6960186 1191306954231536824655231 := by
  unfold tailWord_6960186
  simp only [CollatzResearch.WordTrace]
  refine ⟨63464709690610575494065103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169239225841628201317506941 63464709690610575494065103)
  ·
    refine ⟨95197064535915863241097655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63464709690610575494065103 95197064535915863241097655)
    ·
      refine ⟨142795596803873794861646483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95197064535915863241097655 142795596803873794861646483)
      ·
        refine ⟨214193395205810692292469725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142795596803873794861646483 214193395205810692292469725)
        ·
          refine ⟨80322523202179009609676147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214193395205810692292469725 80322523202179009609676147)
          ·
            refine ⟨120483784803268514414514221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80322523202179009609676147 120483784803268514414514221)
            ·
              refine ⟨45181419301225692905442833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120483784803268514414514221 45181419301225692905442833)
              ·
                refine ⟨33886064475919269679082125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45181419301225692905442833 33886064475919269679082125)
                ·
                  refine ⟨12707274178469726129655797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33886064475919269679082125 12707274178469726129655797)
                  ·
                    refine ⟨1191306954231536824655231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12707274178469726129655797 1191306954231536824655231)
                    ·
                      rfl

theorem cell23_6960186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_6960186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960186 prefixEnd_6960186 := by exact prefixLift 6960186
  have htrace : WordTrace (prefixWord ++ tailWord_6960186) baseStart_6960186 baseEnd_6960186 := by
    simpa [prefixWord, tailWord_6960186, baseEnd_6960186] using wordTrace_append hprefix tailTrace_6960186
  have hstable : (prefixWord ++ tailWord_6960186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960186).length < 2 ^ (prefixWord ++ tailWord_6960186).sum := by decide
  have hdescent : baseEnd_6960186 < baseStart_6960186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960210 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_6960210 : Nat := 118140960795 + 6960210 * 2 ^ 59
def prefixEnd_6960210 : Nat := 4983230072969 + 3 ^ 40 * 6960210 * 2
def baseEnd_6960210 : Nat := 3573933186230318380065583

theorem tailTrace_6960210 : CollatzResearch.WordTrace tailWord_6960210 prefixEnd_6960210 3573933186230318380065583 := by
  unfold tailWord_6960210
  simp only [CollatzResearch.WordTrace]
  refine ⟨63464928528588838518783521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169239809409570236050089389 63464928528588838518783521)
  ·
    refine ⟨47598696396441628889087641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63464928528588838518783521 47598696396441628889087641)
    ·
      refine ⟨35699022297331221666815731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47598696396441628889087641 35699022297331221666815731)
      ·
        refine ⟨53548533445996832500223597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35699022297331221666815731 53548533445996832500223597)
        ·
          refine ⟨20080700042248812187583849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53548533445996832500223597 20080700042248812187583849)
          ·
            refine ⟨15060525031686609140687887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20080700042248812187583849 15060525031686609140687887)
            ·
              refine ⟨22590787547529913711031831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15060525031686609140687887 22590787547529913711031831)
              ·
                refine ⟨33886181321294870566547747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22590787547529913711031831 33886181321294870566547747)
                ·
                  refine ⟨50829271981942305849821621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33886181321294870566547747 50829271981942305849821621)
                  ·
                    refine ⟨4765244248307091173420777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50829271981942305849821621 4765244248307091173420777)
                    ·
                      refine ⟨3573933186230318380065583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765244248307091173420777 3573933186230318380065583)
                      ·
                        rfl

theorem cell23_6960210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_6960210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960210 prefixEnd_6960210 := by exact prefixLift 6960210
  have htrace : WordTrace (prefixWord ++ tailWord_6960210) baseStart_6960210 baseEnd_6960210 := by
    simpa [prefixWord, tailWord_6960210, baseEnd_6960210] using wordTrace_append hprefix tailTrace_6960210
  have hstable : (prefixWord ++ tailWord_6960210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960210).length < 2 ^ (prefixWord ++ tailWord_6960210).sum := by decide
  have hdescent : baseEnd_6960210 < baseStart_6960210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960216 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_6960216 : Nat := 118140960795 + 6960216 * 2 ^ 59
def prefixEnd_6960216 : Nat := 4983230072969 + 3 ^ 40 * 6960216 * 2
def baseEnd_6960216 : Nat := 1191312089038081785530185

theorem tailTrace_6960216 : CollatzResearch.WordTrace tailWord_6960216 prefixEnd_6960216 1191312089038081785530185 := by
  unfold tailWord_6960216
  simp only [CollatzResearch.WordTrace]
  refine ⟨126929966476166808549926251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169239955301555744733235001 126929966476166808549926251)
  ·
    refine ⟨190394949714250212824889377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126929966476166808549926251 190394949714250212824889377)
    ·
      refine ⟨142796212285687659618667033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190394949714250212824889377 142796212285687659618667033)
      ·
        refine ⟨107097159214265744714000275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142796212285687659618667033 107097159214265744714000275)
        ·
          refine ⟨160645738821398617071000413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107097159214265744714000275 160645738821398617071000413)
          ·
            refine ⟨60242152058024481401625155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160645738821398617071000413 60242152058024481401625155)
            ·
              refine ⟨90363228087036722102437733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60242152058024481401625155 90363228087036722102437733)
              ·
                refine ⟨16943105266319385394207075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90363228087036722102437733 16943105266319385394207075)
                ·
                  refine ⟨25414657899479078091310613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16943105266319385394207075 25414657899479078091310613)
                  ·
                    refine ⟨1191312089038081785530185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25414657899479078091310613 1191312089038081785530185)
                    ·
                      rfl

theorem cell23_6960216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_6960216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960216 prefixEnd_6960216 := by exact prefixLift 6960216
  have htrace : WordTrace (prefixWord ++ tailWord_6960216) baseStart_6960216 baseEnd_6960216 := by
    simpa [prefixWord, tailWord_6960216, baseEnd_6960216] using wordTrace_append hprefix tailTrace_6960216
  have hstable : (prefixWord ++ tailWord_6960216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960216).length < 2 ^ (prefixWord ++ tailWord_6960216).sum := by decide
  have hdescent : baseEnd_6960216 < baseStart_6960216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960223 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 4]
def baseStart_6960223 : Nat := 118140960795 + 6960223 * 2 ^ 59
def prefixEnd_6960223 : Nat := 4983230072969 + 3 ^ 40 * 6960223 * 2
def baseEnd_6960223 : Nat := 3573939861478826829203023

theorem tailTrace_6960223 : CollatzResearch.WordTrace tailWord_6960223 prefixEnd_6960223 3573939861478826829203023 := by
  unfold tailWord_6960223
  simp only [CollatzResearch.WordTrace]
  refine ⟨253860188263308257295357323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169240125508872171530238215 253860188263308257295357323)
  ·
    refine ⟨380790282394962385943035985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253860188263308257295357323 380790282394962385943035985)
    ·
      refine ⟨285592711796221789457276989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380790282394962385943035985 285592711796221789457276989)
      ·
        refine ⟨107097266923583171046478871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285592711796221789457276989 107097266923583171046478871)
        ·
          refine ⟨160645900385374756569718307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107097266923583171046478871 160645900385374756569718307)
          ·
            refine ⟨240968850578062134854577461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160645900385374756569718307 240968850578062134854577461)
            ·
              refine ⟨22590829741693325142616637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240968850578062134854577461 22590829741693325142616637)
              ·
                refine ⟨8471561153134996928481239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22590829741693325142616637 8471561153134996928481239)
                ·
                  refine ⟨12707341729702495392721859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471561153134996928481239 12707341729702495392721859)
                  ·
                    refine ⟨19061012594553743089082789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12707341729702495392721859 19061012594553743089082789)
                    ·
                      refine ⟨3573939861478826829203023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19061012594553743089082789 3573939861478826829203023)
                      ·
                        rfl

theorem cell23_6960223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_6960223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960223 prefixEnd_6960223 := by exact prefixLift 6960223
  have htrace : WordTrace (prefixWord ++ tailWord_6960223) baseStart_6960223 baseEnd_6960223 := by
    simpa [prefixWord, tailWord_6960223, baseEnd_6960223] using wordTrace_append hprefix tailTrace_6960223
  have hstable : (prefixWord ++ tailWord_6960223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960223).length < 2 ^ (prefixWord ++ tailWord_6960223).sum := by decide
  have hdescent : baseEnd_6960223 < baseStart_6960223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960233 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 4, 4]
def baseStart_6960233 : Nat := 118140960795 + 6960233 * 2 ^ 59
def prefixEnd_6960233 : Nat := 4983230072969 + 3 ^ 40 * 6960233 * 2
def baseEnd_6960233 : Nat := 1191314998761790596692659

theorem tailTrace_6960233 : CollatzResearch.WordTrace tailWord_6960233 prefixEnd_6960233 1191314998761790596692659 := by
  unfold tailWord_6960233
  simp only [CollatzResearch.WordTrace]
  refine ⟨253860552993272029003221353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169240368662181352668814235 253860552993272029003221353)
  ·
    refine ⟨190395414744954021752416015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253860552993272029003221353 190395414744954021752416015)
    ·
      refine ⟨285593122117431032628624023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190395414744954021752416015 285593122117431032628624023)
      ·
        refine ⟨428389683176146548942936035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285593122117431032628624023 428389683176146548942936035)
        ·
          refine ⟨642584524764219823414404053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428389683176146548942936035 642584524764219823414404053)
          ·
            refine ⟨15060574799161402111275095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 642584524764219823414404053 15060574799161402111275095)
            ·
              refine ⟨22590862198742103166912643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15060574799161402111275095 22590862198742103166912643)
              ·
                refine ⟨33886293298113154750368965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22590862198742103166912643 33886293298113154750368965)
                ·
                  refine ⟨6353679993396216515694181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33886293298113154750368965 6353679993396216515694181)
                  ·
                    refine ⟨1191314998761790596692659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353679993396216515694181 1191314998761790596692659)
                    ·
                      rfl

theorem cell23_6960233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 4].length) (baseStart_6960233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960233 prefixEnd_6960233 := by exact prefixLift 6960233
  have htrace : WordTrace (prefixWord ++ tailWord_6960233) baseStart_6960233 baseEnd_6960233 := by
    simpa [prefixWord, tailWord_6960233, baseEnd_6960233] using wordTrace_append hprefix tailTrace_6960233
  have hstable : (prefixWord ++ tailWord_6960233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960233).length < 2 ^ (prefixWord ++ tailWord_6960233).sum := by decide
  have hdescent : baseEnd_6960233 < baseStart_6960233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960236 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_6960236 : Nat := 118140960795 + 6960236 * 2 ^ 59
def prefixEnd_6960236 : Nat := 4983230072969 + 3 ^ 40 * 6960236 * 2
def baseEnd_6960236 : Nat := 3573946536727335278340463

theorem tailTrace_6960236 : CollatzResearch.WordTrace tailWord_6960236 prefixEnd_6960236 3573946536727335278340463 := by
  unfold tailWord_6960236
  simp only [CollatzResearch.WordTrace]
  refine ⟨126930331206130580257790281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169240441608174107010387041 126930331206130580257790281)
  ·
    refine ⟨95197748404597935193342711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126930331206130580257790281 95197748404597935193342711)
    ·
      refine ⟨142796622606896902790014067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95197748404597935193342711 142796622606896902790014067)
      ·
        refine ⟨214194933910345354185021101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142796622606896902790014067 214194933910345354185021101)
        ·
          refine ⟨80323100216379507819382913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214194933910345354185021101 80323100216379507819382913)
          ·
            refine ⟨60242325162284630864537185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80323100216379507819382913 60242325162284630864537185)
            ·
              refine ⟨45181743871713473148402889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60242325162284630864537185 45181743871713473148402889)
              ·
                refine ⟨33886307903785104861302167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45181743871713473148402889 33886307903785104861302167)
                ·
                  refine ⟨50829461855677657291953251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33886307903785104861302167 50829461855677657291953251)
                  ·
                    refine ⟨76244192783516485937929877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50829461855677657291953251 76244192783516485937929877)
                    ·
                      refine ⟨3573946536727335278340463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76244192783516485937929877 3573946536727335278340463)
                      ·
                        rfl

theorem cell23_6960236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_6960236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960236 prefixEnd_6960236 := by exact prefixLift 6960236
  have htrace : WordTrace (prefixWord ++ tailWord_6960236) baseStart_6960236 baseEnd_6960236 := by
    simpa [prefixWord, tailWord_6960236, baseEnd_6960236] using wordTrace_append hprefix tailTrace_6960236
  have hstable : (prefixWord ++ tailWord_6960236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960236).length < 2 ^ (prefixWord ++ tailWord_6960236).sum := by decide
  have hdescent : baseEnd_6960236 < baseStart_6960236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960257 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6960257 : Nat := 118140960795 + 6960257 * 2 ^ 59
def prefixEnd_6960257 : Nat := 4983230072969 + 3 ^ 40 * 6960257 * 2
def baseEnd_6960257 : Nat := 3573957319821079696177867

theorem tailTrace_6960257 : CollatzResearch.WordTrace tailWord_6960257 prefixEnd_6960257 3573957319821079696177867 := by
  unfold tailWord_6960257
  simp only [CollatzResearch.WordTrace]
  refine ⟨253861428345185081102095025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169240952230123387401396683 253861428345185081102095025)
  ·
    refine ⟨190396071258888810826571269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253861428345185081102095025 190396071258888810826571269)
    ·
      refine ⟨35699263361041652029982113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190396071258888810826571269 35699263361041652029982113)
      ·
        refine ⟨26774447520781239022486585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35699263361041652029982113 26774447520781239022486585)
        ·
          refine ⟨20080835640585929266864939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26774447520781239022486585 20080835640585929266864939)
          ·
            refine ⟨30121253460878893900297409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20080835640585929266864939 30121253460878893900297409)
            ·
              refine ⟨22590940095659170425223057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30121253460878893900297409 22590940095659170425223057)
              ·
                refine ⟨16943205071744377818917293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22590940095659170425223057 16943205071744377818917293)
                ·
                  refine ⟨6353701901904141682093985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16943205071744377818917293 6353701901904141682093985)
                  ·
                    refine ⟨4765276426428106261570489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6353701901904141682093985 4765276426428106261570489)
                    ·
                      refine ⟨3573957319821079696177867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765276426428106261570489 3573957319821079696177867)
                      ·
                        rfl

theorem cell23_6960257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6960257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960257 prefixEnd_6960257 := by exact prefixLift 6960257
  have htrace : WordTrace (prefixWord ++ tailWord_6960257) baseStart_6960257 baseEnd_6960257 := by
    simpa [prefixWord, tailWord_6960257, baseEnd_6960257] using wordTrace_append hprefix tailTrace_6960257
  have hstable : (prefixWord ++ tailWord_6960257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960257).length < 2 ^ (prefixWord ++ tailWord_6960257).sum := by decide
  have hdescent : baseEnd_6960257 < baseStart_6960257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960260 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_6960260 : Nat := 118140960795 + 6960260 * 2 ^ 59
def prefixEnd_6960260 : Nat := 4983230072969 + 3 ^ 40 * 6960260 * 2
def baseEnd_6960260 : Nat := 3573958860263043184440353

theorem tailTrace_6960260 : CollatzResearch.WordTrace tailWord_6960260 prefixEnd_6960260 3573958860263043184440353 := by
  unfold tailWord_6960260
  simp only [CollatzResearch.WordTrace]
  refine ⟨126930768882087106307227117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169241025176116141742969489 126930768882087106307227117)
  ·
    refine ⟨47599038330782664865210169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126930768882087106307227117 47599038330782664865210169)
    ·
      refine ⟨35699278748086998648907627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47599038330782664865210169 35699278748086998648907627)
      ·
        refine ⟨53548918122130497973361441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35699278748086998648907627 53548918122130497973361441)
        ·
          refine ⟨40161688591597873480021081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53548918122130497973361441 40161688591597873480021081)
          ·
            refine ⟨30121266443698405110015811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40161688591597873480021081 30121266443698405110015811)
            ·
              refine ⟨45181899665547607665023717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30121266443698405110015811 45181899665547607665023717)
              ·
                refine ⟨8471606187290176437191947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45181899665547607665023717 8471606187290176437191947)
                ·
                  refine ⟨12707409280935264655787921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471606187290176437191947 12707409280935264655787921)
                  ·
                    refine ⟨9530556960701448491840941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12707409280935264655787921 9530556960701448491840941)
                    ·
                      refine ⟨3573958860263043184440353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530556960701448491840941 3573958860263043184440353)
                      ·
                        rfl

theorem cell23_6960260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_6960260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960260 prefixEnd_6960260 := by exact prefixLift 6960260
  have htrace : WordTrace (prefixWord ++ tailWord_6960260) baseStart_6960260 baseEnd_6960260 := by
    simpa [prefixWord, tailWord_6960260, baseEnd_6960260] using wordTrace_append hprefix tailTrace_6960260
  have hstable : (prefixWord ++ tailWord_6960260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960260).length < 2 ^ (prefixWord ++ tailWord_6960260).sum := by decide
  have hdescent : baseEnd_6960260 < baseStart_6960260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960301 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6960301 : Nat := 118140960795 + 6960301 * 2 ^ 59
def prefixEnd_6960301 : Nat := 4983230072969 + 3 ^ 40 * 6960301 * 2
def baseEnd_6960301 : Nat := 1191326637656625841342555

theorem tailTrace_6960301 : CollatzResearch.WordTrace tailWord_6960301 prefixEnd_6960301 1191326637656625841342555 := by
  unfold tailWord_6960301
  simp only [CollatzResearch.WordTrace]
  refine ⟨253863033157025676616696757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169242022104683784411131171 253863033157025676616696757)
  ·
    refine ⟨23799659358471157182815321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253863033157025676616696757 23799659358471157182815321)
    ·
      refine ⟨17849744518853367887111491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23799659358471157182815321 17849744518853367887111491)
      ·
        refine ⟨26774616778280051830667237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17849744518853367887111491 26774616778280051830667237)
        ·
          refine ⟨5020240645927509718250107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26774616778280051830667237 5020240645927509718250107)
          ·
            refine ⟨7530360968891264577375161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020240645927509718250107 7530360968891264577375161)
            ·
              refine ⟨5647770726668448433031371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7530360968891264577375161 5647770726668448433031371)
              ·
                refine ⟨8471656090002672649547057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647770726668448433031371 8471656090002672649547057)
                ·
                  refine ⟨6353742067502004487160293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8471656090002672649547057 6353742067502004487160293)
                  ·
                    refine ⟨1191326637656625841342555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353742067502004487160293 1191326637656625841342555)
                    ·
                      rfl

theorem cell23_6960301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6960301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960301 prefixEnd_6960301 := by exact prefixLift 6960301
  have htrace : WordTrace (prefixWord ++ tailWord_6960301) baseStart_6960301 baseEnd_6960301 := by
    simpa [prefixWord, tailWord_6960301, baseEnd_6960301] using wordTrace_append hprefix tailTrace_6960301
  have hstable : (prefixWord ++ tailWord_6960301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960301).length < 2 ^ (prefixWord ++ tailWord_6960301).sum := by decide
  have hdescent : baseEnd_6960301 < baseStart_6960301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960307 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 2, 1, 3]
def baseStart_6960307 : Nat := 118140960795 + 6960307 * 2 ^ 59
def prefixEnd_6960307 : Nat := 4983230072969 + 3 ^ 40 * 6960307 * 2
def baseEnd_6960307 : Nat := 3573982993853804500552637

theorem tailTrace_6960307 : CollatzResearch.WordTrace tailWord_6960307 prefixEnd_6960307 3573982993853804500552637 := by
  unfold tailWord_6960307
  simp only [CollatzResearch.WordTrace]
  refine ⟨253863251995003939641415175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169242167996669293094276783 253863251995003939641415175)
  ·
    refine ⟨380794877992505909462122763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253863251995003939641415175 380794877992505909462122763)
    ·
      refine ⟨571192316988758864193184145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380794877992505909462122763 571192316988758864193184145)
      ·
        refine ⟨428394237741569148144888109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571192316988758864193184145 428394237741569148144888109)
        ·
          refine ⟨160647839153088430554333041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428394237741569148144888109 160647839153088430554333041)
          ·
            refine ⟨120485879364816322915749781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160647839153088430554333041 120485879364816322915749781)
            ·
              refine ⟨5647775595225765136675771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120485879364816322915749781 5647775595225765136675771)
              ·
                refine ⟨8471663392838647705013657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647775595225765136675771 8471663392838647705013657)
                ·
                  refine ⟨6353747544628985778760243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8471663392838647705013657 6353747544628985778760243)
                  ·
                    refine ⟨9530621316943478668140365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353747544628985778760243 9530621316943478668140365)
                    ·
                      refine ⟨3573982993853804500552637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530621316943478668140365 3573982993853804500552637)
                      ·
                        rfl

theorem cell23_6960307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 2, 1, 3].length) (baseStart_6960307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960307 prefixEnd_6960307 := by exact prefixLift 6960307
  have htrace : WordTrace (prefixWord ++ tailWord_6960307) baseStart_6960307 baseEnd_6960307 := by
    simpa [prefixWord, tailWord_6960307, baseEnd_6960307] using wordTrace_append hprefix tailTrace_6960307
  have hstable : (prefixWord ++ tailWord_6960307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960307).length < 2 ^ (prefixWord ++ tailWord_6960307).sum := by decide
  have hdescent : baseEnd_6960307 < baseStart_6960307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960317 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_6960317 : Nat := 118140960795 + 6960317 * 2 ^ 59
def prefixEnd_6960317 : Nat := 4983230072969 + 3 ^ 40 * 6960317 * 2
def baseEnd_6960317 : Nat := 3573988128660349461427591

theorem tailTrace_6960317 : CollatzResearch.WordTrace tailWord_6960317 prefixEnd_6960317 3573988128660349461427591 := by
  unfold tailWord_6960317
  simp only [CollatzResearch.WordTrace]
  refine ⟨253863616724967711349279205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169242411149978474232852803 253863616724967711349279205)
  ·
    refine ⟨47599428135931445877989851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253863616724967711349279205 47599428135931445877989851)
    ·
      refine ⟨71399142203897168816984777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47599428135931445877989851 71399142203897168816984777)
      ·
        refine ⟨53549356652922876612738583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71399142203897168816984777 53549356652922876612738583)
        ·
          refine ⟨80324034979384314919107875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53549356652922876612738583 80324034979384314919107875)
          ·
            refine ⟨120486052469076472378661813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80324034979384314919107875 120486052469076472378661813)
            ·
              refine ⟨11295567418975919285499545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120486052469076472378661813 11295567418975919285499545)
              ·
                refine ⟨8471675564231939464124659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11295567418975919285499545 8471675564231939464124659)
                ·
                  refine ⟨12707513346347909196186989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471675564231939464124659 12707513346347909196186989)
                  ·
                    refine ⟨4765317504880465948570121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12707513346347909196186989 4765317504880465948570121)
                    ·
                      refine ⟨3573988128660349461427591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765317504880465948570121 3573988128660349461427591)
                      ·
                        rfl

theorem cell23_6960317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_6960317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960317 prefixEnd_6960317 := by exact prefixLift 6960317
  have htrace : WordTrace (prefixWord ++ tailWord_6960317) baseStart_6960317 baseEnd_6960317 := by
    simpa [prefixWord, tailWord_6960317, baseEnd_6960317] using wordTrace_append hprefix tailTrace_6960317
  have hstable : (prefixWord ++ tailWord_6960317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960317).length < 2 ^ (prefixWord ++ tailWord_6960317).sum := by decide
  have hdescent : baseEnd_6960317 < baseStart_6960317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960330 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_6960330 : Nat := 118140960795 + 6960330 * 2 ^ 59
def prefixEnd_6960330 : Nat := 4983230072969 + 3 ^ 40 * 6960330 * 2
def baseEnd_6960330 : Nat := 3573994803908857910565031

theorem tailTrace_6960330 : CollatzResearch.WordTrace tailWord_6960330 prefixEnd_6960330 3573994803908857910565031 := by
  unfold tailWord_6960330
  simp only [CollatzResearch.WordTrace]
  refine ⟨63466022718480153642375611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169242727249280409713001629 63466022718480153642375611)
  ·
    refine ⟨95199034077720230463563417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63466022718480153642375611 95199034077720230463563417)
    ·
      refine ⟨71399275558290172847672563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95199034077720230463563417 71399275558290172847672563)
      ·
        refine ⟨107098913337435259271508845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71399275558290172847672563 107098913337435259271508845)
        ·
          refine ⟨40162092501538222226815817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107098913337435259271508845 40162092501538222226815817)
          ·
            refine ⟨30121569376153666670111863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40162092501538222226815817 30121569376153666670111863)
            ·
              refine ⟨45182354064230500005167795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30121569376153666670111863 45182354064230500005167795)
              ·
                refine ⟨67773531096345750007751693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45182354064230500005167795 67773531096345750007751693)
                ·
                  refine ⟨25415074161129656252906885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67773531096345750007751693 25415074161129656252906885)
                  ·
                    refine ⟨4765326405211810547420041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25415074161129656252906885 4765326405211810547420041)
                    ·
                      refine ⟨3573994803908857910565031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765326405211810547420041 3573994803908857910565031)
                      ·
                        rfl

theorem cell23_6960330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_6960330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960330 prefixEnd_6960330 := by exact prefixLift 6960330
  have htrace : WordTrace (prefixWord ++ tailWord_6960330) baseStart_6960330 baseEnd_6960330 := by
    simpa [prefixWord, tailWord_6960330, baseEnd_6960330] using wordTrace_append hprefix tailTrace_6960330
  have hstable : (prefixWord ++ tailWord_6960330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960330).length < 2 ^ (prefixWord ++ tailWord_6960330).sum := by decide
  have hdescent : baseEnd_6960330 < baseStart_6960330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960342 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6960342 : Nat := 118140960795 + 6960342 * 2 ^ 59
def prefixEnd_6960342 : Nat := 4983230072969 + 3 ^ 40 * 6960342 * 2
def baseEnd_6960342 : Nat := 3574000965676711863614977

theorem tailTrace_6960342 : CollatzResearch.WordTrace tailWord_6960342 prefixEnd_6960342 3574000965676711863614977 := by
  unfold tailWord_6960342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866533034367321288683705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169243019033251427079292853 15866533034367321288683705)
  ·
    refine ⟨11899899775775490966512779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15866533034367321288683705 11899899775775490966512779)
    ·
      refine ⟨17849849663663236449769169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11899899775775490966512779 17849849663663236449769169)
      ·
        refine ⟨13387387247747427337326877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17849849663663236449769169 13387387247747427337326877)
        ·
          refine ⟨5020270217905285251497579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13387387247747427337326877 5020270217905285251497579)
          ·
            refine ⟨7530405326857927877246369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020270217905285251497579 7530405326857927877246369)
            ·
              refine ⟨5647803995143445907934777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7530405326857927877246369 5647803995143445907934777)
              ·
                refine ⟨4235852996357584430951083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647803995143445907934777 4235852996357584430951083)
                ·
                  refine ⟨6353779494536376646426625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235852996357584430951083 6353779494536376646426625)
                  ·
                    refine ⟨4765334620902282484819969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6353779494536376646426625 4765334620902282484819969)
                    ·
                      refine ⟨3574000965676711863614977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765334620902282484819969 3574000965676711863614977)
                      ·
                        rfl

theorem cell23_6960342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6960342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960342 prefixEnd_6960342 := by exact prefixLift 6960342
  have htrace : WordTrace (prefixWord ++ tailWord_6960342) baseStart_6960342 baseEnd_6960342 := by
    simpa [prefixWord, tailWord_6960342, baseEnd_6960342] using wordTrace_append hprefix tailTrace_6960342
  have hstable : (prefixWord ++ tailWord_6960342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960342).length < 2 ^ (prefixWord ++ tailWord_6960342).sum := by decide
  have hdescent : baseEnd_6960342 < baseStart_6960342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960363 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 3]
def baseStart_6960363 : Nat := 118140960795 + 6960363 * 2 ^ 59
def prefixEnd_6960363 : Nat := 4983230072969 + 3 ^ 40 * 6960363 * 2
def baseEnd_6960363 : Nat := 3574011748770456281452379

theorem tailTrace_6960363 : CollatzResearch.WordTrace tailWord_6960363 prefixEnd_6960363 3574011748770456281452379 := by
  unfold tailWord_6960363
  simp only [CollatzResearch.WordTrace]
  refine ⟨253865294482801061205453743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169243529655200707470302495 253865294482801061205453743)
  ·
    refine ⟨380797941724201591808180615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253865294482801061205453743 380797941724201591808180615)
    ·
      refine ⟨571196912586302387712270923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380797941724201591808180615 571196912586302387712270923)
      ·
        refine ⟨856795368879453581568406385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571196912586302387712270923 856795368879453581568406385)
        ·
          refine ⟨642596526659590186176304789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856795368879453581568406385 642596526659590186176304789)
          ·
            refine ⟨30121712187168289977014287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 642596526659590186176304789 30121712187168289977014287)
            ·
              refine ⟨45182568280752434965521431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30121712187168289977014287 45182568280752434965521431)
              ·
                refine ⟨67773852421128652448282147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45182568280752434965521431 67773852421128652448282147)
                ·
                  refine ⟨101660778631692978672423221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67773852421128652448282147 101660778631692978672423221)
                  ·
                    refine ⟨9530697996721216750539677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101660778631692978672423221 9530697996721216750539677)
                    ·
                      refine ⟨3574011748770456281452379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530697996721216750539677 3574011748770456281452379)
                      ·
                        rfl

theorem cell23_6960363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 3].length) (baseStart_6960363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960363 prefixEnd_6960363 := by exact prefixLift 6960363
  have htrace : WordTrace (prefixWord ++ tailWord_6960363) baseStart_6960363 baseEnd_6960363 := by
    simpa [prefixWord, tailWord_6960363, baseEnd_6960363] using wordTrace_append hprefix tailTrace_6960363
  have hstable : (prefixWord ++ tailWord_6960363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960363).length < 2 ^ (prefixWord ++ tailWord_6960363).sum := by decide
  have hdescent : baseEnd_6960363 < baseStart_6960363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960370 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_6960370 : Nat := 118140960795 + 6960370 * 2 ^ 59
def prefixEnd_6960370 : Nat := 4983230072969 + 3 ^ 40 * 6960370 * 2
def baseEnd_6960370 : Nat := 397112815903893083784983

theorem tailTrace_6960370 : CollatzResearch.WordTrace tailWord_6960370 prefixEnd_6960370 397112815903893083784983 := by
  unfold tailWord_6960370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63466387448443925350239641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169243699862517134267305709 63466387448443925350239641)
  ·
    refine ⟨47599790586332944012679731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63466387448443925350239641 47599790586332944012679731)
    ·
      refine ⟨71399685879499416019019597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47599790586332944012679731 71399685879499416019019597)
      ·
        refine ⟨26774882204812281007132349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71399685879499416019019597 26774882204812281007132349)
        ·
          refine ⟨10040580826804605377674631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26774882204812281007132349 10040580826804605377674631)
          ·
            refine ⟨15060871240206908066511947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040580826804605377674631 15060871240206908066511947)
            ·
              refine ⟨22591306860310362099767921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15060871240206908066511947 22591306860310362099767921)
              ·
                refine ⟨16943480145232771574825941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22591306860310362099767921 16943480145232771574825941)
                ·
                  refine ⟨397112815903893083784983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16943480145232771574825941 397112815903893083784983)
                  ·
                    rfl

theorem cell23_6960370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_6960370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960370 prefixEnd_6960370 := by exact prefixLift 6960370
  have htrace : WordTrace (prefixWord ++ tailWord_6960370) baseStart_6960370 baseEnd_6960370 := by
    simpa [prefixWord, tailWord_6960370, baseEnd_6960370] using wordTrace_append hprefix tailTrace_6960370
  have hstable : (prefixWord ++ tailWord_6960370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960370).length < 2 ^ (prefixWord ++ tailWord_6960370).sum := by decide
  have hdescent : baseEnd_6960370 < baseStart_6960370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960383 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 1, 7]
def baseStart_6960383 : Nat := 118140960795 + 6960383 * 2 ^ 59
def prefixEnd_6960383 : Nat := 4983230072969 + 3 ^ 40 * 6960383 * 2
def baseEnd_6960383 : Nat := 1191340672794515401067429

theorem tailTrace_6960383 : CollatzResearch.WordTrace tailWord_6960383 prefixEnd_6960383 1191340672794515401067429 := by
  unfold tailWord_6960383
  simp only [CollatzResearch.WordTrace]
  refine ⟨253866023942728604621181803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169244015961819069747454535 253866023942728604621181803)
  ·
    refine ⟨380799035914092906931772705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253866023942728604621181803 380799035914092906931772705)
    ·
      refine ⟨285599276935569680198829529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380799035914092906931772705 285599276935569680198829529)
      ·
        refine ⟨214199457701677260149122147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285599276935569680198829529 214199457701677260149122147)
        ·
          refine ⟨321299186552515890223683221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214199457701677260149122147 321299186552515890223683221)
          ·
            refine ⟨15060899369649182354235151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 321299186552515890223683221 15060899369649182354235151)
            ·
              refine ⟨22591349054473773531352727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15060899369649182354235151 22591349054473773531352727)
              ·
                refine ⟨33887023581710660297029091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22591349054473773531352727 33887023581710660297029091)
                ·
                  refine ⟨50830535372565990445543637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33887023581710660297029091 50830535372565990445543637)
                  ·
                    refine ⟨1191340672794515401067429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50830535372565990445543637 1191340672794515401067429)
                    ·
                      rfl

theorem cell23_6960383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_6960383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960383 prefixEnd_6960383 := by exact prefixLift 6960383
  have htrace : WordTrace (prefixWord ++ tailWord_6960383) baseStart_6960383 baseEnd_6960383 := by
    simpa [prefixWord, tailWord_6960383, baseEnd_6960383] using wordTrace_append hprefix tailTrace_6960383
  have hstable : (prefixWord ++ tailWord_6960383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960383).length < 2 ^ (prefixWord ++ tailWord_6960383).sum := by decide
  have hdescent : baseEnd_6960383 < baseStart_6960383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960438 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_6960438 : Nat := 118140960795 + 6960438 * 2 ^ 59
def prefixEnd_6960438 : Nat := 4983230072969 + 3 ^ 40 * 6960438 * 2
def baseEnd_6960438 : Nat := 397116695535504832001615

theorem tailTrace_6960438 : CollatzResearch.WordTrace tailWord_6960438 prefixEnd_6960438 397116695535504832001615 := by
  unfold tailWord_6960438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866751872345584313402123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169245353305019566009622645 15866751872345584313402123)
  ·
    refine ⟨23800127808518376470103185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15866751872345584313402123 23800127808518376470103185)
    ·
      refine ⟨17850095856388782352577389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23800127808518376470103185 17850095856388782352577389)
      ·
        refine ⟨6693785946145793382216521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17850095856388782352577389 6693785946145793382216521)
        ·
          refine ⟨5020339459609345036662391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6693785946145793382216521 5020339459609345036662391)
          ·
            refine ⟨7530509189414017554993587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020339459609345036662391 7530509189414017554993587)
            ·
              refine ⟨11295763784121026332490381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7530509189414017554993587 11295763784121026332490381)
              ·
                refine ⟨4235911419045384874683893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11295763784121026332490381 4235911419045384874683893)
                ·
                  refine ⟨397116695535504832001615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4235911419045384874683893 397116695535504832001615)
                  ·
                    rfl

theorem cell23_6960438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_6960438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960438 prefixEnd_6960438 := by exact prefixLift 6960438
  have htrace : WordTrace (prefixWord ++ tailWord_6960438) baseStart_6960438 baseEnd_6960438 := by
    simpa [prefixWord, tailWord_6960438, baseEnd_6960438] using wordTrace_append hprefix tailTrace_6960438
  have hstable : (prefixWord ++ tailWord_6960438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960438).length < 2 ^ (prefixWord ++ tailWord_6960438).sum := by decide
  have hdescent : baseEnd_6960438 < baseStart_6960438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960440 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_6960440 : Nat := 118140960795 + 6960440 * 2 ^ 59
def prefixEnd_6960440 : Nat := 4983230072969 + 3 ^ 40 * 6960440 * 2
def baseEnd_6960440 : Nat := 3574051286780852480189525

theorem tailTrace_6960440 : CollatzResearch.WordTrace tailWord_6960440 prefixEnd_6960440 3574051286780852480189525 := by
  unfold tailWord_6960440
  simp only [CollatzResearch.WordTrace]
  refine ⟨126934051451761051678003387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169245401935681402237337849 126934051451761051678003387)
  ·
    refine ⟨190401077177641577517005081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126934051451761051678003387 190401077177641577517005081)
    ·
      refine ⟨142800807883231183137753811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190401077177641577517005081 142800807883231183137753811)
      ·
        refine ⟨214201211824846774706630717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142800807883231183137753811 214201211824846774706630717)
        ·
          refine ⟨80325454434317540514986519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214201211824846774706630717 80325454434317540514986519)
          ·
            refine ⟨120488181651476310772479779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80325454434317540514986519 120488181651476310772479779)
            ·
              refine ⟨180732272477214466158719669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120488181651476310772479779 180732272477214466158719669)
              ·
                refine ⟨16943650544738856202379969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180732272477214466158719669 16943650544738856202379969)
                ·
                  refine ⟨12707737908554142151784977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16943650544738856202379969 12707737908554142151784977)
                  ·
                    refine ⟨9530803431415606613838733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12707737908554142151784977 9530803431415606613838733)
                    ·
                      refine ⟨3574051286780852480189525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530803431415606613838733 3574051286780852480189525)
                      ·
                        rfl

theorem cell23_6960440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_6960440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960440 prefixEnd_6960440 := by exact prefixLift 6960440
  have htrace : WordTrace (prefixWord ++ tailWord_6960440) baseStart_6960440 baseEnd_6960440 := by
    simpa [prefixWord, tailWord_6960440, baseEnd_6960440] using wordTrace_append hprefix tailTrace_6960440
  have hstable : (prefixWord ++ tailWord_6960440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960440).length < 2 ^ (prefixWord ++ tailWord_6960440).sum := by decide
  have hdescent : baseEnd_6960440 < baseStart_6960440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960464 : List Nat := [2, 1, 1, 1, 1, 5, 5, 2, 1, 4]
def baseStart_6960464 : Nat := 118140960795 + 6960464 * 2 ^ 59
def prefixEnd_6960464 : Nat := 4983230072969 + 3 ^ 40 * 6960464 * 2
def baseEnd_6960464 : Nat := 1191354536772186795429805

theorem tailTrace_6960464 : CollatzResearch.WordTrace tailWord_6960464 prefixEnd_6960464 1191354536772186795429805 := by
  unfold tailWord_6960464
  simp only [CollatzResearch.WordTrace]
  refine ⟨126934489127717577727440223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169245985503623436969920297 126934489127717577727440223)
  ·
    refine ⟨190401733691576366591160335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126934489127717577727440223 190401733691576366591160335)
    ·
      refine ⟨285602600537364549886740503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190401733691576366591160335 285602600537364549886740503)
      ·
        refine ⟨428403900806046824830110755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285602600537364549886740503 428403900806046824830110755)
        ·
          refine ⟨642605851209070237245166133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428403900806046824830110755 642605851209070237245166133)
          ·
            refine ⟨60244298550850334741734325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 642605851209070237245166133 60244298550850334741734325)
            ·
              refine ⟨5647902989142218882037593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60244298550850334741734325 5647902989142218882037593)
              ·
                refine ⟨4235927241856664161528195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647902989142218882037593 4235927241856664161528195)
                ·
                  refine ⟨6353890862784996242292293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235927241856664161528195 6353890862784996242292293)
                  ·
                    refine ⟨1191354536772186795429805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353890862784996242292293 1191354536772186795429805)
                    ·
                      rfl

theorem cell23_6960464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 4].length) (baseStart_6960464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960464 prefixEnd_6960464 := by exact prefixLift 6960464
  have htrace : WordTrace (prefixWord ++ tailWord_6960464) baseStart_6960464 baseEnd_6960464 := by
    simpa [prefixWord, tailWord_6960464, baseEnd_6960464] using wordTrace_append hprefix tailTrace_6960464
  have hstable : (prefixWord ++ tailWord_6960464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960464).length < 2 ^ (prefixWord ++ tailWord_6960464).sum := by decide
  have hdescent : baseEnd_6960464 < baseStart_6960464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960497 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 2, 3, 2]
def baseStart_6960497 : Nat := 118140960795 + 6960497 * 2 ^ 59
def prefixEnd_6960497 : Nat := 4983230072969 + 3 ^ 40 * 6960497 * 2
def baseEnd_6960497 : Nat := 3574080555178158757176763

theorem tailTrace_6960497 : CollatzResearch.WordTrace tailWord_6960497 prefixEnd_6960497 3574080555178158757176763 := by
  unfold tailWord_6960497
  simp only [CollatzResearch.WordTrace]
  refine ⟨253870181864315602090831745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169246787909543734727221163 253870181864315602090831745)
  ·
    refine ⟨190402636398236701568123809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253870181864315602090831745 190402636398236701568123809)
    ·
      refine ⟨142801977298677526176092857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190402636398236701568123809 142801977298677526176092857)
      ·
        refine ⟨107101482974008144632069643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142801977298677526176092857 107101482974008144632069643)
        ·
          refine ⟨160652224461012216948104465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107101482974008144632069643 160652224461012216948104465)
          ·
            refine ⟨120489168345759162711078349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160652224461012216948104465 120489168345759162711078349)
            ·
              refine ⟨45183438129659686016654381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120489168345759162711078349 45183438129659686016654381)
              ·
                refine ⟨16943789298622382256245393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45183438129659686016654381 16943789298622382256245393)
                ·
                  refine ⟨12707841973966786692184045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16943789298622382256245393 12707841973966786692184045)
                  ·
                    refine ⟨4765440740237545009569017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12707841973966786692184045 4765440740237545009569017)
                    ·
                      refine ⟨3574080555178158757176763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765440740237545009569017 3574080555178158757176763)
                      ·
                        rfl

theorem cell23_6960497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_6960497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960497 prefixEnd_6960497 := by exact prefixLift 6960497
  have htrace : WordTrace (prefixWord ++ tailWord_6960497) baseStart_6960497 baseEnd_6960497 := by
    simpa [prefixWord, tailWord_6960497, baseEnd_6960497] using wordTrace_append hprefix tailTrace_6960497
  have hstable : (prefixWord ++ tailWord_6960497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960497).length < 2 ^ (prefixWord ++ tailWord_6960497).sum := by decide
  have hdescent : baseEnd_6960497 < baseStart_6960497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960507 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 1, 5]
def baseStart_6960507 : Nat := 118140960795 + 6960507 * 2 ^ 59
def prefixEnd_6960507 : Nat := 4983230072969 + 3 ^ 40 * 6960507 * 2
def baseEnd_6960507 : Nat := 1191361896661567906017239

theorem tailTrace_6960507 : CollatzResearch.WordTrace tailWord_6960507 prefixEnd_6960507 1191361896661567906017239 := by
  unfold tailWord_6960507
  simp only [CollatzResearch.WordTrace]
  refine ⟨253870546594279373798695775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169247031062852915865797183 253870546594279373798695775)
  ·
    refine ⟨380805819891419060698043663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253870546594279373798695775 380805819891419060698043663)
    ·
      refine ⟨571208729837128591047065495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380805819891419060698043663 571208729837128591047065495)
      ·
        refine ⟨856813094755692886570598243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571208729837128591047065495 856813094755692886570598243)
        ·
          refine ⟨1285219642133539329855897365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856813094755692886570598243 1285219642133539329855897365)
          ·
            refine ⟨60244670725009656086995189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1285219642133539329855897365 60244670725009656086995189)
            ·
              refine ⟨5647937880469655258155799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60244670725009656086995189 5647937880469655258155799)
              ·
                refine ⟨8471906820704482887233699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5647937880469655258155799 8471906820704482887233699)
                ·
                  refine ⟨12707860231056724330850549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471906820704482887233699 12707860231056724330850549)
                  ·
                    refine ⟨1191361896661567906017239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12707860231056724330850549 1191361896661567906017239)
                    ·
                      rfl

theorem cell23_6960507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 5].length) (baseStart_6960507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960507 prefixEnd_6960507 := by exact prefixLift 6960507
  have htrace : WordTrace (prefixWord ++ tailWord_6960507) baseStart_6960507 baseEnd_6960507 := by
    simpa [prefixWord, tailWord_6960507, baseEnd_6960507] using wordTrace_append hprefix tailTrace_6960507
  have hstable : (prefixWord ++ tailWord_6960507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960507).length < 2 ^ (prefixWord ++ tailWord_6960507).sum := by decide
  have hdescent : baseEnd_6960507 < baseStart_6960507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960521 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 1, 1, 3]
def baseStart_6960521 : Nat := 118140960795 + 6960521 * 2 ^ 59
def prefixEnd_6960521 : Nat := 4983230072969 + 3 ^ 40 * 6960521 * 2
def baseEnd_6960521 : Nat := 3574092878713866663276653

theorem tailTrace_6960521 : CollatzResearch.WordTrace tailWord_6960521 prefixEnd_6960521 3574092878713866663276653 := by
  unfold tailWord_6960521
  simp only [CollatzResearch.WordTrace]
  refine ⟨253871057216228654189705417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169247371477485769459803611 253871057216228654189705417)
  ·
    refine ⟨190403292912171490642279063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253871057216228654189705417 190403292912171490642279063)
    ·
      refine ⟨285604939368257235963418595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190403292912171490642279063 285604939368257235963418595)
      ·
        refine ⟨428407409052385853945127893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285604939368257235963418595 428407409052385853945127893)
        ·
          refine ⟨10040798649665293451838935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 428407409052385853945127893 10040798649665293451838935)
          ·
            refine ⟨15061197974497940177758403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10040798649665293451838935 15061197974497940177758403)
            ·
              refine ⟨22591796961746910266637605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15061197974497940177758403 22591796961746910266637605)
              ·
                refine ⟨4235961930327545674994551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22591796961746910266637605 4235961930327545674994551)
                ·
                  refine ⟨6353942895491318512491827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4235961930327545674994551 6353942895491318512491827)
                  ·
                    refine ⟨9530914343236977768737741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6353942895491318512491827 9530914343236977768737741)
                    ·
                      refine ⟨3574092878713866663276653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530914343236977768737741 3574092878713866663276653)
                      ·
                        rfl

theorem cell23_6960521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 1, 3].length) (baseStart_6960521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960521 prefixEnd_6960521 := by exact prefixLift 6960521
  have htrace : WordTrace (prefixWord ++ tailWord_6960521) baseStart_6960521 baseEnd_6960521 := by
    simpa [prefixWord, tailWord_6960521, baseEnd_6960521] using wordTrace_append hprefix tailTrace_6960521
  have hstable : (prefixWord ++ tailWord_6960521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960521).length < 2 ^ (prefixWord ++ tailWord_6960521).sum := by decide
  have hdescent : baseEnd_6960521 < baseStart_6960521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960537 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 2, 4]
def baseStart_6960537 : Nat := 118140960795 + 6960537 * 2 ^ 59
def prefixEnd_6960537 : Nat := 4983230072969 + 3 ^ 40 * 6960537 * 2
def baseEnd_6960537 : Nat := 1191367031468112866892193

theorem tailTrace_6960537 : CollatzResearch.WordTrace tailWord_6960537 prefixEnd_6960537 1191367031468112866892193 := by
  unfold tailWord_6960537
  simp only [CollatzResearch.WordTrace]
  refine ⟨253871640784170688922287865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169247760522780459281525243 253871640784170688922287865)
  ·
    refine ⟨190403730588128016691715899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253871640784170688922287865 190403730588128016691715899)
    ·
      refine ⟨285605595882192025037573849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190403730588128016691715899 285605595882192025037573849)
      ·
        refine ⟨214204196911644018778180387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285605595882192025037573849 214204196911644018778180387)
        ·
          refine ⟨321306295367466028167270581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214204196911644018778180387 321306295367466028167270581)
          ·
            refine ⟨30122465190699940140681617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321306295367466028167270581 30122465190699940140681617)
            ·
              refine ⟨22591848893024955105511213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30122465190699940140681617 22591848893024955105511213)
              ·
                refine ⟨8471943334884358164566705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22591848893024955105511213 8471943334884358164566705)
                ·
                  refine ⟨6353957501163268623425029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8471943334884358164566705 6353957501163268623425029)
                  ·
                    refine ⟨1191367031468112866892193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6353957501163268623425029 1191367031468112866892193)
                    ·
                      rfl

theorem cell23_6960537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 4].length) (baseStart_6960537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960537 prefixEnd_6960537 := by exact prefixLift 6960537
  have htrace : WordTrace (prefixWord ++ tailWord_6960537) baseStart_6960537 baseEnd_6960537 := by
    simpa [prefixWord, tailWord_6960537, baseEnd_6960537] using wordTrace_append hprefix tailTrace_6960537
  have hstable : (prefixWord ++ tailWord_6960537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960537).length < 2 ^ (prefixWord ++ tailWord_6960537).sum := by decide
  have hdescent : baseEnd_6960537 < baseStart_6960537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960544 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 3, 2, 2]
def baseStart_6960544 : Nat := 118140960795 + 6960544 * 2 ^ 59
def prefixEnd_6960544 : Nat := 4983230072969 + 3 ^ 40 * 6960544 * 2
def baseEnd_6960544 : Nat := 3574104688768920073289047

theorem tailTrace_6960544 : CollatzResearch.WordTrace tailWord_6960544 prefixEnd_6960544 3574104688768920073289047 := by
  unfold tailWord_6960544
  simp only [CollatzResearch.WordTrace]
  refine ⟨126935948047572664558896343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169247930730096886078528457 126935948047572664558896343)
  ·
    refine ⟨190403922071358996838344515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126935948047572664558896343 190403922071358996838344515)
    ·
      refine ⟨285605883107038495257516773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190403922071358996838344515 285605883107038495257516773)
      ·
        refine ⟨53551103082569717860784395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285605883107038495257516773 53551103082569717860784395)
        ·
          refine ⟨80326654623854576791176593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53551103082569717860784395 80326654623854576791176593)
          ·
            refine ⟨60244990967890932593382445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80326654623854576791176593 60244990967890932593382445)
            ·
              refine ⟨22591871612959099722518417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60244990967890932593382445 22591871612959099722518417)
              ·
                refine ⟨16943903709719324791888813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22591871612959099722518417 16943903709719324791888813)
                ·
                  refine ⟨6353963891144746796958305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16943903709719324791888813 6353963891144746796958305)
                  ·
                    refine ⟨4765472918358560097718729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6353963891144746796958305 4765472918358560097718729)
                    ·
                      refine ⟨3574104688768920073289047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765472918358560097718729 3574104688768920073289047)
                      ·
                        rfl

theorem cell23_6960544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_6960544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960544 prefixEnd_6960544 := by exact prefixLift 6960544
  have htrace : WordTrace (prefixWord ++ tailWord_6960544) baseStart_6960544 baseEnd_6960544 := by
    simpa [prefixWord, tailWord_6960544, baseEnd_6960544] using wordTrace_append hprefix tailTrace_6960544
  have hstable : (prefixWord ++ tailWord_6960544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960544).length < 2 ^ (prefixWord ++ tailWord_6960544).sum := by decide
  have hdescent : baseEnd_6960544 < baseStart_6960544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960547 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 3]
def baseStart_6960547 : Nat := 118140960795 + 6960547 * 2 ^ 59
def prefixEnd_6960547 : Nat := 4983230072969 + 3 ^ 40 * 6960547 * 2
def baseEnd_6960547 : Nat := 3574106229210883561551533

theorem tailTrace_6960547 : CollatzResearch.WordTrace tailWord_6960547 prefixEnd_6960547 3574106229210883561551533 := by
  unfold tailWord_6960547
  simp only [CollatzResearch.WordTrace]
  refine ⟨253872005514134460630151895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169248003676089640420101263 253872005514134460630151895)
  ·
    refine ⟨380808008271201690945227843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253872005514134460630151895 380808008271201690945227843)
    ·
      refine ⟨571212012406802536417841765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380808008271201690945227843 571212012406802536417841765)
      ·
        refine ⟨107102252326275475578345331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 571212012406802536417841765 107102252326275475578345331)
        ·
          refine ⟨160653378489413213367517997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107102252326275475578345331 160653378489413213367517997)
          ·
            refine ⟨60245016933529955012819249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160653378489413213367517997 60245016933529955012819249)
            ·
              refine ⟨45183762700147466259614437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60245016933529955012819249 45183762700147466259614437)
              ·
                refine ⟨8471955506277649923677707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45183762700147466259614437 8471955506277649923677707)
                ·
                  refine ⟨12707933259416474885516561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8471955506277649923677707 12707933259416474885516561)
                  ·
                    refine ⟨9530949944562356164137421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12707933259416474885516561 9530949944562356164137421)
                    ·
                      refine ⟨3574106229210883561551533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530949944562356164137421 3574106229210883561551533)
                      ·
                        rfl

theorem cell23_6960547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_6960547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960547 prefixEnd_6960547 := by exact prefixLift 6960547
  have htrace : WordTrace (prefixWord ++ tailWord_6960547) baseStart_6960547 baseEnd_6960547 := by
    simpa [prefixWord, tailWord_6960547, baseEnd_6960547] using wordTrace_append hprefix tailTrace_6960547
  have hstable : (prefixWord ++ tailWord_6960547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960547).length < 2 ^ (prefixWord ++ tailWord_6960547).sum := by decide
  have hdescent : baseEnd_6960547 < baseStart_6960547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960560 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_6960560 : Nat := 118140960795 + 6960560 * 2 ^ 59
def prefixEnd_6960560 : Nat := 4983230072969 + 3 ^ 40 * 6960560 * 2
def baseEnd_6960560 : Nat := 3574112904459392010688973

theorem tailTrace_6960560 : CollatzResearch.WordTrace tailWord_6960560 prefixEnd_6960560 3574112904459392010688973 := by
  unfold tailWord_6960560
  simp only [CollatzResearch.WordTrace]
  refine ⟨126936239831543681925187567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169248319775391575900250089 126936239831543681925187567)
  ·
    refine ⟨190404359747315522887781351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126936239831543681925187567 190404359747315522887781351)
    ·
      refine ⟨285606539620973284331672027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190404359747315522887781351 285606539620973284331672027)
      ·
        refine ⟨428409809431459926497508041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285606539620973284331672027 428409809431459926497508041)
        ·
          refine ⟨321307357073594944873131031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428409809431459926497508041 321307357073594944873131031)
          ·
            refine ⟨481961035610392417309696547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321307357073594944873131031 481961035610392417309696547)
            ·
              refine ⟨722941553415588625964544821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481961035610392417309696547 722941553415588625964544821)
              ·
                refine ⟨67775770632711433684176077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 722941553415588625964544821 67775770632711433684176077)
                ·
                  refine ⟨25415913987266787631566029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67775770632711433684176077 25415913987266787631566029)
                  ·
                    refine ⟨9530967745225045361837261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25415913987266787631566029 9530967745225045361837261)
                    ·
                      refine ⟨3574112904459392010688973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9530967745225045361837261 3574112904459392010688973)
                      ·
                        rfl

theorem cell23_6960560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_6960560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960560 prefixEnd_6960560 := by exact prefixLift 6960560
  have htrace : WordTrace (prefixWord ++ tailWord_6960560) baseStart_6960560 baseEnd_6960560 := by
    simpa [prefixWord, tailWord_6960560, baseEnd_6960560] using wordTrace_append hprefix tailTrace_6960560
  have hstable : (prefixWord ++ tailWord_6960560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960560).length < 2 ^ (prefixWord ++ tailWord_6960560).sum := by decide
  have hdescent : baseEnd_6960560 < baseStart_6960560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960587 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 5, 3, 2]
def baseStart_6960587 : Nat := 118140960795 + 6960587 * 2 ^ 59
def prefixEnd_6960587 : Nat := 4983230072969 + 3 ^ 40 * 6960587 * 2
def baseEnd_6960587 : Nat := 3574126768437063405051349

theorem tailTrace_6960587 : CollatzResearch.WordTrace tailWord_6960587 prefixEnd_6960587 3574126768437063405051349 := by
  unfold tailWord_6960587
  simp only [CollatzResearch.WordTrace]
  refine ⟨253873464433989547461608015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169248976289326364974405343 253873464433989547461608015)
  ·
    refine ⟨380810196650984321192412023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253873464433989547461608015 380810196650984321192412023)
    ·
      refine ⟨571215294976476481788618035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380810196650984321192412023 571215294976476481788618035)
      ·
        refine ⟨856822942464714722682927053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571215294976476481788618035 856822942464714722682927053)
        ·
          refine ⟨321308603424268021006097645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 856822942464714722682927053 321308603424268021006097645)
          ·
            refine ⟨120490726284100507877286617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321308603424268021006097645 120490726284100507877286617)
            ·
              refine ⟨90368044713075380907964963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120490726284100507877286617 90368044713075380907964963)
              ·
                refine ⟨135552067069613071361947445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90368044713075380907964963 135552067069613071361947445)
                ·
                  refine ⟨12708006287776225440182573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135552067069613071361947445 12708006287776225440182573)
                  ·
                    refine ⟨4765502357916084540068465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12708006287776225440182573 4765502357916084540068465)
                    ·
                      refine ⟨3574126768437063405051349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765502357916084540068465 3574126768437063405051349)
                      ·
                        rfl

theorem cell23_6960587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3, 2].length) (baseStart_6960587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960587 prefixEnd_6960587 := by exact prefixLift 6960587
  have htrace : WordTrace (prefixWord ++ tailWord_6960587) baseStart_6960587 baseEnd_6960587 := by
    simpa [prefixWord, tailWord_6960587, baseEnd_6960587] using wordTrace_append hprefix tailTrace_6960587
  have hstable : (prefixWord ++ tailWord_6960587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960587).length < 2 ^ (prefixWord ++ tailWord_6960587).sum := by decide
  have hdescent : baseEnd_6960587 < baseStart_6960587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960600 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_6960600 : Nat := 118140960795 + 6960600 * 2 ^ 59
def prefixEnd_6960600 : Nat := 4983230072969 + 3 ^ 40 * 6960600 * 2
def baseEnd_6960600 : Nat := 3574133443685571854188789

theorem tailTrace_6960600 : CollatzResearch.WordTrace tailWord_6960600 prefixEnd_6960600 3574133443685571854188789 := by
  unfold tailWord_6960600
  simp only [CollatzResearch.WordTrace]
  refine ⟨126936969291471225340915627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169249292388628300454554169 126936969291471225340915627)
  ·
    refine ⟨190405453937206838011373441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126936969291471225340915627 190405453937206838011373441)
    ·
      refine ⟨142804090452905128508530081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190405453937206838011373441 142804090452905128508530081)
      ·
        refine ⟨107103067839678846381397561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142804090452905128508530081 107103067839678846381397561)
        ·
          refine ⟨80327300879759134786048171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107103067839678846381397561 80327300879759134786048171)
          ·
            refine ⟨120490951319638702179072257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80327300879759134786048171 120490951319638702179072257)
            ·
              refine ⟨90368213489729026634304193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120490951319638702179072257 90368213489729026634304193)
              ·
                refine ⟨67776160117296769975728145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90368213489729026634304193 67776160117296769975728145)
                ·
                  refine ⟨50832120087972577481796109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67776160117296769975728145 50832120087972577481796109)
                  ·
                    refine ⟨19062045032989716555673541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50832120087972577481796109 19062045032989716555673541)
                    ·
                      refine ⟨3574133443685571854188789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19062045032989716555673541 3574133443685571854188789)
                      ·
                        rfl

theorem cell23_6960600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_6960600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960600 prefixEnd_6960600 := by exact prefixLift 6960600
  have htrace : WordTrace (prefixWord ++ tailWord_6960600) baseStart_6960600 baseEnd_6960600 := by
    simpa [prefixWord, tailWord_6960600, baseEnd_6960600] using wordTrace_append hprefix tailTrace_6960600
  have hstable : (prefixWord ++ tailWord_6960600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960600).length < 2 ^ (prefixWord ++ tailWord_6960600).sum := by decide
  have hdescent : baseEnd_6960600 < baseStart_6960600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960634 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2]
def baseStart_6960634 : Nat := 118140960795 + 6960634 * 2 ^ 59
def prefixEnd_6960634 : Nat := 4983230072969 + 3 ^ 40 * 6960634 * 2
def baseEnd_6960634 : Nat := 3574150902027824721163633

theorem tailTrace_6960634 : CollatzResearch.WordTrace tailWord_6960634 prefixEnd_6960634 3574150902027824721163633 := by
  unfold tailWord_6960634
  simp only [CollatzResearch.WordTrace]
  refine ⟨63468794666204818622142239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169250119109879516325712637 63468794666204818622142239)
  ·
    refine ⟨95203191999307227933213359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63468794666204818622142239 95203191999307227933213359)
    ·
      refine ⟨142804787998960841899820039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95203191999307227933213359 142804787998960841899820039)
      ·
        refine ⟨214207181998441262849730059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142804787998960841899820039 214207181998441262849730059)
        ·
          refine ⟨321310772997661894274595089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214207181998441262849730059 321310772997661894274595089)
          ·
            refine ⟨240983079748246420705946317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321310772997661894274595089 240983079748246420705946317)
            ·
              refine ⟨90368654905592407764729869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240983079748246420705946317 90368654905592407764729869)
              ·
                refine ⟨33888245589597152911773701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90368654905592407764729869 33888245589597152911773701)
                ·
                  refine ⟨6354046048049466170957569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33888245589597152911773701 6354046048049466170957569)
                  ·
                    refine ⟨4765534536037099628218177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6354046048049466170957569 4765534536037099628218177)
                    ·
                      refine ⟨3574150902027824721163633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765534536037099628218177 3574150902027824721163633)
                      ·
                        rfl

theorem cell23_6960634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_6960634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960634 prefixEnd_6960634 := by exact prefixLift 6960634
  have htrace : WordTrace (prefixWord ++ tailWord_6960634) baseStart_6960634 baseEnd_6960634 := by
    simpa [prefixWord, tailWord_6960634, baseEnd_6960634] using wordTrace_append hprefix tailTrace_6960634
  have hstable : (prefixWord ++ tailWord_6960634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960634).length < 2 ^ (prefixWord ++ tailWord_6960634).sum := by decide
  have hdescent : baseEnd_6960634 < baseStart_6960634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960691 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 5]
def baseStart_6960691 : Nat := 118140960795 + 6960691 * 2 ^ 59
def prefixEnd_6960691 : Nat := 4983230072969 + 3 ^ 40 * 6960691 * 2
def baseEnd_6960691 : Nat := 397131130047236777572319

theorem tailTrace_6960691 : CollatzResearch.WordTrace tailWord_6960691 prefixEnd_6960691 397131130047236777572319 := by
  unfold tailWord_6960691
  simp only [CollatzResearch.WordTrace]
  refine ⟨253877257625612773223393927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169251505083741848815595951 253877257625612773223393927)
  ·
    refine ⟨380815886438419159835090891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253877257625612773223393927 380815886438419159835090891)
    ·
      refine ⟨571223829657628739752636337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380815886438419159835090891 571223829657628739752636337)
      ·
        refine ⟨428417872243221554814477253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571223829657628739752636337 428417872243221554814477253)
        ·
          refine ⟨80328351045604041527714485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428417872243221554814477253 80328351045604041527714485)
          ·
            refine ⟨7530782910525378893223233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80328351045604041527714485 7530782910525378893223233)
            ·
              refine ⟨5648087182894034169917425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7530782910525378893223233 5648087182894034169917425)
              ·
                refine ⟨4236065387170525627438069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648087182894034169917425 4236065387170525627438069)
                ·
                  refine ⟨397131130047236777572319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4236065387170525627438069 397131130047236777572319)
                  ·
                    rfl

theorem cell23_6960691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 5].length) (baseStart_6960691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960691 prefixEnd_6960691 := by exact prefixLift 6960691
  have htrace : WordTrace (prefixWord ++ tailWord_6960691) baseStart_6960691 baseEnd_6960691 := by
    simpa [prefixWord, tailWord_6960691, baseEnd_6960691] using wordTrace_append hprefix tailTrace_6960691
  have hstable : (prefixWord ++ tailWord_6960691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960691).length < 2 ^ (prefixWord ++ tailWord_6960691).sum := by decide
  have hdescent : baseEnd_6960691 < baseStart_6960691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960697 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6960697 : Nat := 118140960795 + 6960697 * 2 ^ 59
def prefixEnd_6960697 : Nat := 4983230072969 + 3 ^ 40 * 6960697 * 2
def baseEnd_6960697 : Nat := 3574183251309057974675843

theorem tailTrace_6960697 : CollatzResearch.WordTrace tailWord_6960697 prefixEnd_6960697 3574183251309057974675843 := by
  unfold tailWord_6960697
  simp only [CollatzResearch.WordTrace]
  refine ⟨253877476463591036248112345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169251650975727357498741563 253877476463591036248112345)
  ·
    refine ⟨190408107347693277186084259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253877476463591036248112345 190408107347693277186084259)
    ·
      refine ⟨285612161021539915779126389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190408107347693277186084259 285612161021539915779126389)
      ·
        refine ⟨26776140095769367104293099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285612161021539915779126389 26776140095769367104293099)
        ·
          refine ⟨40164210143654050656439649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26776140095769367104293099 40164210143654050656439649)
          ·
            refine ⟨30123157607740537992329737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40164210143654050656439649 30123157607740537992329737)
            ·
              refine ⟨22592368205805403494247303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30123157607740537992329737 22592368205805403494247303)
              ·
                refine ⟨33888552308708105241370955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22592368205805403494247303 33888552308708105241370955)
                ·
                  refine ⟨50832828463062157862056433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33888552308708105241370955 50832828463062157862056433)
                  ·
                    refine ⟨38124621347296618396542325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50832828463062157862056433 38124621347296618396542325)
                    ·
                      refine ⟨3574183251309057974675843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38124621347296618396542325 3574183251309057974675843)
                      ·
                        rfl

theorem cell23_6960697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6960697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960697 prefixEnd_6960697 := by exact prefixLift 6960697
  have htrace : WordTrace (prefixWord ++ tailWord_6960697) baseStart_6960697 baseEnd_6960697 := by
    simpa [prefixWord, tailWord_6960697, baseEnd_6960697] using wordTrace_append hprefix tailTrace_6960697
  have hstable : (prefixWord ++ tailWord_6960697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960697).length < 2 ^ (prefixWord ++ tailWord_6960697).sum := by decide
  have hdescent : baseEnd_6960697 < baseStart_6960697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960724 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_6960724 : Nat := 118140960795 + 6960724 * 2 ^ 59
def prefixEnd_6960724 : Nat := 4983230072969 + 3 ^ 40 * 6960724 * 2
def baseEnd_6960724 : Nat := 3574197115286729369038219

theorem tailTrace_6960724 : CollatzResearch.WordTrace tailWord_6960724 prefixEnd_6960724 3574197115286729369038219 := by
  unfold tailWord_6960724
  simp only [CollatzResearch.WordTrace]
  refine ⟨126939230617246609929672613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169252307489662146572896817 126939230617246609929672613)
  ·
    refine ⟨23801105740733739361813615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126939230617246609929672613 23801105740733739361813615)
    ·
      refine ⟨35701658611100609042720423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23801105740733739361813615 35701658611100609042720423)
      ·
        refine ⟨53552487916650913564080635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35701658611100609042720423 53552487916650913564080635)
        ·
          refine ⟨80328731874976370346120953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53552487916650913564080635 80328731874976370346120953)
          ·
            refine ⟨60246548906232277759590715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80328731874976370346120953 60246548906232277759590715)
            ·
              refine ⟨90369823359348416639386073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60246548906232277759590715 90369823359348416639386073)
              ·
                refine ⟨67777367519511312479539555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90369823359348416639386073 67777367519511312479539555)
                ·
                  refine ⟨101666051279266968719309333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67777367519511312479539555 101666051279266968719309333)
                  ·
                    refine ⟨4765596153715639158717625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101666051279266968719309333 4765596153715639158717625)
                    ·
                      refine ⟨3574197115286729369038219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765596153715639158717625 3574197115286729369038219)
                      ·
                        rfl

theorem cell23_6960724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_6960724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960724 prefixEnd_6960724 := by exact prefixLift 6960724
  have htrace : WordTrace (prefixWord ++ tailWord_6960724) baseStart_6960724 baseEnd_6960724 := by
    simpa [prefixWord, tailWord_6960724, baseEnd_6960724] using wordTrace_append hprefix tailTrace_6960724
  have hstable : (prefixWord ++ tailWord_6960724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960724).length < 2 ^ (prefixWord ++ tailWord_6960724).sum := by decide
  have hdescent : baseEnd_6960724 < baseStart_6960724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960777 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 3, 5]
def baseStart_6960777 : Nat := 118140960795 + 6960777 * 2 ^ 59
def prefixEnd_6960777 : Nat := 4983230072969 + 3 ^ 40 * 6960777 * 2
def baseEnd_6960777 : Nat := 1191408109920472553891825

theorem tailTrace_6960777 : CollatzResearch.WordTrace tailWord_6960777 prefixEnd_6960777 1191408109920472553891825 := by
  unfold tailWord_6960777
  simp only [CollatzResearch.WordTrace]
  refine ⟨253880394303301209911024585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169253596202200806607349723 253880394303301209911024585)
  ·
    refine ⟨190410295727475907433268439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253880394303301209911024585 190410295727475907433268439)
    ·
      refine ⟨285615443591213861149902659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190410295727475907433268439 285615443591213861149902659)
      ·
        refine ⟨428423165386820791724853989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285615443591213861149902659 428423165386820791724853989)
        ·
          refine ⟨80329343510028898448410123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428423165386820791724853989 80329343510028898448410123)
          ·
            refine ⟨120494015265043347672615185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80329343510028898448410123 120494015265043347672615185)
            ·
              refine ⟨90370511448782510754461389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120494015265043347672615185 90370511448782510754461389)
              ·
                refine ⟨33888941793293441532923021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90370511448782510754461389 33888941793293441532923021)
                ·
                  refine ⟨12708353172485040574846133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33888941793293441532923021 12708353172485040574846133)
                  ·
                    refine ⟨1191408109920472553891825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12708353172485040574846133 1191408109920472553891825)
                    ·
                      rfl

theorem cell23_6960777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_6960777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960777 prefixEnd_6960777 := by exact prefixLift 6960777
  have htrace : WordTrace (prefixWord ++ tailWord_6960777) baseStart_6960777 baseEnd_6960777 := by
    simpa [prefixWord, tailWord_6960777, baseEnd_6960777] using wordTrace_append hprefix tailTrace_6960777
  have hstable : (prefixWord ++ tailWord_6960777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960777).length < 2 ^ (prefixWord ++ tailWord_6960777).sum := by decide
  have hdescent : baseEnd_6960777 < baseStart_6960777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960784 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 6, 3, 2]
def baseStart_6960784 : Nat := 118140960795 + 6960784 * 2 ^ 59
def prefixEnd_6960784 : Nat := 4983230072969 + 3 ^ 40 * 6960784 * 2
def baseEnd_6960784 : Nat := 3574227924125999134287943

theorem tailTrace_6960784 : CollatzResearch.WordTrace tailWord_6960784 prefixEnd_6960784 3574227924125999134287943 := by
  unfold tailWord_6960784
  simp only [CollatzResearch.WordTrace]
  refine ⟨126940324807137925053264703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169253766409517233404352937 126940324807137925053264703)
  ·
    refine ⟨190410487210706887579897055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126940324807137925053264703 190410487210706887579897055)
    ·
      refine ⟨285615730816060331369845583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190410487210706887579897055 285615730816060331369845583)
      ·
        refine ⟨428423596224090497054768375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285615730816060331369845583 428423596224090497054768375)
        ·
          refine ⟨642635394336135745582152563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428423596224090497054768375 642635394336135745582152563)
          ·
            refine ⟨963953091504203618373228845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642635394336135745582152563 963953091504203618373228845)
            ·
              refine ⟨361482409314076356889960817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 963953091504203618373228845 361482409314076356889960817)
              ·
                refine ⟨271111806985557267667470613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361482409314076356889960817 271111806985557267667470613)
                ·
                  refine ⟨12708365952447996921912685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 271111806985557267667470613 12708365952447996921912685)
                  ·
                    refine ⟨4765637232167998845717257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12708365952447996921912685 4765637232167998845717257)
                    ·
                      refine ⟨3574227924125999134287943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765637232167998845717257 3574227924125999134287943)
                      ·
                        rfl

theorem cell23_6960784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 3, 2].length) (baseStart_6960784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960784 prefixEnd_6960784 := by exact prefixLift 6960784
  have htrace : WordTrace (prefixWord ++ tailWord_6960784) baseStart_6960784 baseEnd_6960784 := by
    simpa [prefixWord, tailWord_6960784, baseEnd_6960784] using wordTrace_append hprefix tailTrace_6960784
  have hstable : (prefixWord ++ tailWord_6960784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960784).length < 2 ^ (prefixWord ++ tailWord_6960784).sum := by decide
  have hdescent : baseEnd_6960784 < baseStart_6960784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960801 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6960801 : Nat := 118140960795 + 6960801 * 2 ^ 59
def prefixEnd_6960801 : Nat := 4983230072969 + 3 ^ 40 * 6960801 * 2
def baseEnd_6960801 : Nat := 3574236653297125567775365

theorem tailTrace_6960801 : CollatzResearch.WordTrace tailWord_6960801 prefixEnd_6960801 3574236653297125567775365 := by
  unfold tailWord_6960801
  simp only [CollatzResearch.WordTrace]
  refine ⟨253881269655214262009898257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169254179770142841339932171 253881269655214262009898257)
  ·
    refine ⟨190410952241410696507423693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253881269655214262009898257 190410952241410696507423693)
    ·
      refine ⟨71404107090529011190283885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190410952241410696507423693 71404107090529011190283885)
      ·
        refine ⟨26776540158948379196356457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71404107090529011190283885 26776540158948379196356457)
        ·
          refine ⟨20082405119211284397267343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26776540158948379196356457 20082405119211284397267343)
          ·
            refine ⟨30123607678816926595901015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20082405119211284397267343 30123607678816926595901015)
            ·
              refine ⟨45185411518225389893851523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30123607678816926595901015 45185411518225389893851523)
              ·
                refine ⟨67778117277338084840777285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45185411518225389893851523 67778117277338084840777285)
                ·
                  refine ⟨12708396989500890907645741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67778117277338084840777285 12708396989500890907645741)
                  ·
                    refine ⟨4765648871062834090367153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12708396989500890907645741 4765648871062834090367153)
                    ·
                      refine ⟨3574236653297125567775365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765648871062834090367153 3574236653297125567775365)
                      ·
                        rfl

theorem cell23_6960801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6960801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960801 prefixEnd_6960801 := by exact prefixLift 6960801
  have htrace : WordTrace (prefixWord ++ tailWord_6960801) baseStart_6960801 baseEnd_6960801 := by
    simpa [prefixWord, tailWord_6960801, baseEnd_6960801] using wordTrace_append hprefix tailTrace_6960801
  have hstable : (prefixWord ++ tailWord_6960801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960801).length < 2 ^ (prefixWord ++ tailWord_6960801).sum := by decide
  have hdescent : baseEnd_6960801 < baseStart_6960801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960802 : List Nat := [3, 3, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_6960802 : Nat := 118140960795 + 6960802 * 2 ^ 59
def prefixEnd_6960802 : Nat := 4983230072969 + 3 ^ 40 * 6960802 * 2
def baseEnd_6960802 : Nat := 1191412388925926687954287

theorem tailTrace_6960802 : CollatzResearch.WordTrace tailWord_6960802 prefixEnd_6960802 1191412388925926687954287 := by
  unfold tailWord_6960802
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470326532052659795171165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169254204085473759453789773 63470326532052659795171165)
  ·
    refine ⟨23801372449519747423189187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63470326532052659795171165 23801372449519747423189187)
    ·
      refine ⟨35702058674279621134783781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23801372449519747423189187 35702058674279621134783781)
      ·
        refine ⟨6694136001427428962771959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35702058674279621134783781 6694136001427428962771959)
        ·
          refine ⟨10041204002141143444157939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6694136001427428962771959 10041204002141143444157939)
          ·
            refine ⟨15061806003211715166236909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10041204002141143444157939 15061806003211715166236909)
            ·
              refine ⟨5648177251204393187338841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15061806003211715166236909 5648177251204393187338841)
              ·
                refine ⟨4236132938403294890504131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648177251204393187338841 4236132938403294890504131)
                ·
                  refine ⟨6354199407604942335756197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236132938403294890504131 6354199407604942335756197)
                  ·
                    refine ⟨1191412388925926687954287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6354199407604942335756197 1191412388925926687954287)
                    ·
                      rfl

theorem cell23_6960802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_6960802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960802 prefixEnd_6960802 := by exact prefixLift 6960802
  have htrace : WordTrace (prefixWord ++ tailWord_6960802) baseStart_6960802 baseEnd_6960802 := by
    simpa [prefixWord, tailWord_6960802, baseEnd_6960802] using wordTrace_append hprefix tailTrace_6960802
  have hstable : (prefixWord ++ tailWord_6960802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960802).length < 2 ^ (prefixWord ++ tailWord_6960802).sum := by decide
  have hdescent : baseEnd_6960802 < baseStart_6960802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960827 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4]
def baseStart_6960827 : Nat := 118140960795 + 6960827 * 2 ^ 59
def prefixEnd_6960827 : Nat := 4983230072969 + 3 ^ 40 * 6960827 * 2
def baseEnd_6960827 : Nat := 3574250003794142466050245

theorem tailTrace_6960827 : CollatzResearch.WordTrace tailWord_6960827 prefixEnd_6960827 3574250003794142466050245 := by
  unfold tailWord_6960827
  simp only [CollatzResearch.WordTrace]
  refine ⟨253882217953120068450344735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169254811968746712300229823 253882217953120068450344735)
  ·
    refine ⟨380823326929680102675517103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253882217953120068450344735 380823326929680102675517103)
    ·
      refine ⟨571234990394520154013275655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380823326929680102675517103 571234990394520154013275655)
      ·
        refine ⟨856852485591780231019913483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571234990394520154013275655 856852485591780231019913483)
        ·
          refine ⟨1285278728387670346529870225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856852485591780231019913483 1285278728387670346529870225)
          ·
            refine ⟨963959046290752759897402669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285278728387670346529870225 963959046290752759897402669)
            ·
              refine ⟨361484642359032284961526001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 963959046290752759897402669 361484642359032284961526001)
              ·
                refine ⟨271113481769274213721144501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361484642359032284961526001 271113481769274213721144501)
                ·
                  refine ⟨25416888915869457536357297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271113481769274213721144501 25416888915869457536357297)
                  ·
                    refine ⟨19062666686902093152267973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25416888915869457536357297 19062666686902093152267973)
                    ·
                      refine ⟨3574250003794142466050245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19062666686902093152267973 3574250003794142466050245)
                      ·
                        rfl

theorem cell23_6960827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 4].length) (baseStart_6960827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960827 prefixEnd_6960827 := by exact prefixLift 6960827
  have htrace : WordTrace (prefixWord ++ tailWord_6960827) baseStart_6960827 baseEnd_6960827 := by
    simpa [prefixWord, tailWord_6960827, baseEnd_6960827] using wordTrace_append hprefix tailTrace_6960827
  have hstable : (prefixWord ++ tailWord_6960827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960827).length < 2 ^ (prefixWord ++ tailWord_6960827).sum := by decide
  have hdescent : baseEnd_6960827 < baseStart_6960827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960831 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 5, 2, 2]
def baseStart_6960831 : Nat := 118140960795 + 6960831 * 2 ^ 59
def prefixEnd_6960831 : Nat := 4983230072969 + 3 ^ 40 * 6960831 * 2
def baseEnd_6960831 : Nat := 3574252057716760450400227

theorem tailTrace_6960831 : CollatzResearch.WordTrace tailWord_6960831 prefixEnd_6960831 3574252057716760450400227 := by
  unfold tailWord_6960831
  simp only [CollatzResearch.WordTrace]
  refine ⟨253882363845105577133490347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169254909230070384755660231 253882363845105577133490347)
  ·
    refine ⟨380823545767658365700235521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253882363845105577133490347 380823545767658365700235521)
    ·
      refine ⟨285617659325743774275176641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380823545767658365700235521 285617659325743774275176641)
      ·
        refine ⟨214213244494307830706382481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285617659325743774275176641 214213244494307830706382481)
        ·
          refine ⟨160659933370730873029786861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214213244494307830706382481 160659933370730873029786861)
          ·
            refine ⟨60247475014024077386170073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160659933370730873029786861 60247475014024077386170073)
            ·
              refine ⟨45185606260518058039627555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60247475014024077386170073 45185606260518058039627555)
              ·
                refine ⟨67778409390777087059441333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45185606260518058039627555 67778409390777087059441333)
                ·
                  refine ⟨6354225880385351911822625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67778409390777087059441333 6354225880385351911822625)
                  ·
                    refine ⟨4765669410289013933866969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6354225880385351911822625 4765669410289013933866969)
                    ·
                      refine ⟨3574252057716760450400227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765669410289013933866969 3574252057716760450400227)
                      ·
                        rfl

theorem cell23_6960831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_6960831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960831 prefixEnd_6960831 := by exact prefixLift 6960831
  have htrace : WordTrace (prefixWord ++ tailWord_6960831) baseStart_6960831 baseEnd_6960831 := by
    simpa [prefixWord, tailWord_6960831, baseEnd_6960831] using wordTrace_append hprefix tailTrace_6960831
  have hstable : (prefixWord ++ tailWord_6960831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960831).length < 2 ^ (prefixWord ++ tailWord_6960831).sum := by decide
  have hdescent : baseEnd_6960831 < baseStart_6960831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960845 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6960845 : Nat := 118140960795 + 6960845 * 2 ^ 59
def prefixEnd_6960845 : Nat := 4983230072969 + 3 ^ 40 * 6960845 * 2
def baseEnd_6960845 : Nat := 1191419748815307798541721

theorem tailTrace_6960845 : CollatzResearch.WordTrace tailWord_6960845 prefixEnd_6960845 1191419748815307798541721 := by
  unfold tailWord_6960845
  simp only [CollatzResearch.WordTrace]
  refine ⟨253882874467054857524499989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169255249644703238349666659 253882874467054857524499989)
  ·
    refine ⟨11900759740643196446460937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 253882874467054857524499989 11900759740643196446460937)
    ·
      refine ⟨8925569805482397334845703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11900759740643196446460937 8925569805482397334845703)
      ·
        refine ⟨13388354708223596002268555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8925569805482397334845703 13388354708223596002268555)
        ·
          refine ⟨20082532062335394003402833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388354708223596002268555 20082532062335394003402833)
          ·
            refine ⟨15061899046751545502552125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20082532062335394003402833 15061899046751545502552125)
            ·
              refine ⟨5648212142531829563457047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15061899046751545502552125 5648212142531829563457047)
              ·
                refine ⟨8472318213797744345185571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648212142531829563457047 8472318213797744345185571)
                ·
                  refine ⟨12708477320696616517778357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8472318213797744345185571 12708477320696616517778357)
                  ·
                    refine ⟨1191419748815307798541721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12708477320696616517778357 1191419748815307798541721)
                    ·
                      rfl

theorem cell23_6960845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6960845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960845 prefixEnd_6960845 := by exact prefixLift 6960845
  have htrace : WordTrace (prefixWord ++ tailWord_6960845) baseStart_6960845 baseEnd_6960845 := by
    simpa [prefixWord, tailWord_6960845, baseEnd_6960845] using wordTrace_append hprefix tailTrace_6960845
  have hstable : (prefixWord ++ tailWord_6960845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960845).length < 2 ^ (prefixWord ++ tailWord_6960845).sum := by decide
  have hdescent : baseEnd_6960845 < baseStart_6960845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960881 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_6960881 : Nat := 118140960795 + 6960881 * 2 ^ 59
def prefixEnd_6960881 : Nat := 4983230072969 + 3 ^ 40 * 6960881 * 2
def baseEnd_6960881 : Nat := 3574277731749485254774997

theorem tailTrace_6960881 : CollatzResearch.WordTrace tailWord_6960881 prefixEnd_6960881 3574277731749485254774997 := by
  unfold tailWord_6960881
  simp only [CollatzResearch.WordTrace]
  refine ⟨253884187494924435672810497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169256124996616290448540331 253884187494924435672810497)
  ·
    refine ⟨190413140621193326754607873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253884187494924435672810497 190413140621193326754607873)
    ·
      refine ⟨142809855465894995065955905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190413140621193326754607873 142809855465894995065955905)
      ·
        refine ⟨107107391599421246299466929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142809855465894995065955905 107107391599421246299466929)
        ·
          refine ⟨80330543699565934724600197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107107391599421246299466929 80330543699565934724600197)
          ·
            refine ⟨15061976943668612760862537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80330543699565934724600197 15061976943668612760862537)
            ·
              refine ⟨11296482707751459570646903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15061976943668612760862537 11296482707751459570646903)
              ·
                refine ⟨16944724061627189355970355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11296482707751459570646903 16944724061627189355970355)
                ·
                  refine ⟨25417086092440784033955533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16944724061627189355970355 25417086092440784033955533)
                  ·
                    refine ⟨9531407284665294012733325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25417086092440784033955533 9531407284665294012733325)
                    ·
                      refine ⟨3574277731749485254774997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9531407284665294012733325 3574277731749485254774997)
                      ·
                        rfl

theorem cell23_6960881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_6960881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960881 prefixEnd_6960881 := by exact prefixLift 6960881
  have htrace : WordTrace (prefixWord ++ tailWord_6960881) baseStart_6960881 baseEnd_6960881 := by
    simpa [prefixWord, tailWord_6960881, baseEnd_6960881] using wordTrace_append hprefix tailTrace_6960881
  have hstable : (prefixWord ++ tailWord_6960881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960881).length < 2 ^ (prefixWord ++ tailWord_6960881).sum := by decide
  have hdescent : baseEnd_6960881 < baseStart_6960881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960898 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_6960898 : Nat := 118140960795 + 6960898 * 2 ^ 59
def prefixEnd_6960898 : Nat := 4983230072969 + 3 ^ 40 * 6960898 * 2
def baseEnd_6960898 : Nat := 3574286460920611688262419

theorem tailTrace_6960898 : CollatzResearch.WordTrace tailWord_6960898 prefixEnd_6960898 3574286460920611688262419 := by
  unfold tailWord_6960898
  simp only [CollatzResearch.WordTrace]
  refine ⟨63471201883965711894044837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169256538357241898384119565 63471201883965711894044837)
  ·
    refine ⟨11900850353243570980133407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63471201883965711894044837 11900850353243570980133407)
    ·
      refine ⟨17851275529865356470200111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11900850353243570980133407 17851275529865356470200111)
      ·
        refine ⟨26776913294798034705300167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17851275529865356470200111 26776913294798034705300167)
        ·
          refine ⟨40165369942197052057950251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26776913294798034705300167 40165369942197052057950251)
          ·
            refine ⟨60248054913295578086925377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40165369942197052057950251 60248054913295578086925377)
            ·
              refine ⟨45186041184971683565194033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60248054913295578086925377 45186041184971683565194033)
              ·
                refine ⟨33889530888728762673895525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45186041184971683565194033 33889530888728762673895525)
                ·
                  refine ⟨6354287041636643001355411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33889530888728762673895525 6354287041636643001355411)
                  ·
                    refine ⟨9531430562454964502033117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6354287041636643001355411 9531430562454964502033117)
                    ·
                      refine ⟨3574286460920611688262419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9531430562454964502033117 3574286460920611688262419)
                      ·
                        rfl

theorem cell23_6960898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_6960898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960898 prefixEnd_6960898 := by exact prefixLift 6960898
  have htrace : WordTrace (prefixWord ++ tailWord_6960898) baseStart_6960898 baseEnd_6960898 := by
    simpa [prefixWord, tailWord_6960898, baseEnd_6960898] using wordTrace_append hprefix tailTrace_6960898
  have hstable : (prefixWord ++ tailWord_6960898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960898).length < 2 ^ (prefixWord ++ tailWord_6960898).sum := by decide
  have hdescent : baseEnd_6960898 < baseStart_6960898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6960942 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_6960942 : Nat := 118140960795 + 6960942 * 2 ^ 59
def prefixEnd_6960942 : Nat := 4983230072969 + 3 ^ 40 * 6960942 * 2
def baseEnd_6960942 : Nat := 3574309054069409516112217

theorem tailTrace_6960942 : CollatzResearch.WordTrace tailWord_6960942 prefixEnd_6960942 3574309054069409516112217 := by
  unfold tailWord_6960942
  simp only [CollatzResearch.WordTrace]
  refine ⟨31735801543462930386347635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169257608231802295393854053 31735801543462930386347635)
  ·
    refine ⟨47603702315194395579521453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31735801543462930386347635 47603702315194395579521453)
    ·
      refine ⟨17851388368197898342320545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47603702315194395579521453 17851388368197898342320545)
      ·
        refine ⟨13388541276148423756740409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17851388368197898342320545 13388541276148423756740409)
        ·
          refine ⟨10041405957111317817555307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13388541276148423756740409 10041405957111317817555307)
          ·
            refine ⟨15062108935666976726332961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10041405957111317817555307 15062108935666976726332961)
            ·
              refine ⟨11296581701750232544749721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15062108935666976726332961 11296581701750232544749721)
              ·
                refine ⟨8472436276312674408562291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11296581701750232544749721 8472436276312674408562291)
                ·
                  refine ⟨12708654414469011612843437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8472436276312674408562291 12708654414469011612843437)
                  ·
                    refine ⟨4765745405425879354816289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12708654414469011612843437 4765745405425879354816289)
                    ·
                      refine ⟨3574309054069409516112217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765745405425879354816289 3574309054069409516112217)
                      ·
                        rfl

theorem cell23_6960942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_6960942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6960942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6960942 prefixEnd_6960942 := by exact prefixLift 6960942
  have htrace : WordTrace (prefixWord ++ tailWord_6960942) baseStart_6960942 baseEnd_6960942 := by
    simpa [prefixWord, tailWord_6960942, baseEnd_6960942] using wordTrace_append hprefix tailTrace_6960942
  have hstable : (prefixWord ++ tailWord_6960942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6960942).length < 2 ^ (prefixWord ++ tailWord_6960942).sum := by decide
  have hdescent : baseEnd_6960942 < baseStart_6960942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6960942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961011 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 4, 4, 2]
def baseStart_6961011 : Nat := 118140960795 + 6961011 * 2 ^ 59
def prefixEnd_6961011 : Nat := 4983230072969 + 3 ^ 40 * 6961011 * 2
def baseEnd_6961011 : Nat := 3574344484234569746149399

theorem tailTrace_6961011 : CollatzResearch.WordTrace tailWord_6961011 prefixEnd_6961011 3574344484234569746149399 := by
  unfold tailWord_6961011
  simp only [CollatzResearch.WordTrace]
  refine ⟨253888928984453467875042887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169259285989635645250028591 253888928984453467875042887)
  ·
    refine ⟨380833393476680201812564331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253888928984453467875042887 380833393476680201812564331)
    ·
      refine ⟨571250090215020302718846497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380833393476680201812564331 571250090215020302718846497)
      ·
        refine ⟨428437567661265227039134873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571250090215020302718846497 428437567661265227039134873)
        ·
          refine ⟨321328175745948920279351155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428437567661265227039134873 321328175745948920279351155)
          ·
            refine ⟨481992263618923380419026733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321328175745948920279351155 481992263618923380419026733)
            ·
              refine ⟨180747098857096267657135025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481992263618923380419026733 180747098857096267657135025)
              ·
                refine ⟨135560324142822200742851269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180747098857096267657135025 135560324142822200742851269)
                ·
                  refine ⟨25417560776779162639284613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135560324142822200742851269 25417560776779162639284613)
                  ·
                    refine ⟨4765792645646092994865865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25417560776779162639284613 4765792645646092994865865)
                    ·
                      refine ⟨3574344484234569746149399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765792645646092994865865 3574344484234569746149399)
                      ·
                        rfl

theorem cell23_6961011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 4, 2].length) (baseStart_6961011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961011 prefixEnd_6961011 := by exact prefixLift 6961011
  have htrace : WordTrace (prefixWord ++ tailWord_6961011) baseStart_6961011 baseEnd_6961011 := by
    simpa [prefixWord, tailWord_6961011, baseEnd_6961011] using wordTrace_append hprefix tailTrace_6961011
  have hstable : (prefixWord ++ tailWord_6961011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961011).length < 2 ^ (prefixWord ++ tailWord_6961011).sum := by decide
  have hdescent : baseEnd_6961011 < baseStart_6961011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961024 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_6961024 : Nat := 118140960795 + 6961024 * 2 ^ 59
def prefixEnd_6961024 : Nat := 4983230072969 + 3 ^ 40 * 6961024 * 2
def baseEnd_6961024 : Nat := 3574351159483078195286839

theorem tailTrace_6961024 : CollatzResearch.WordTrace tailWord_6961024 prefixEnd_6961024 3574351159483078195286839 := by
  unfold tailWord_6961024
  simp only [CollatzResearch.WordTrace]
  refine ⟨126944701566703185547633063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169259602088937580730177417 126944701566703185547633063)
  ·
    refine ⟨190417052350054778321449595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126944701566703185547633063 190417052350054778321449595)
    ·
      refine ⟨285625578525082167482174393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190417052350054778321449595 285625578525082167482174393)
      ·
        refine ⟨214219183893811625611630795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285625578525082167482174393 214219183893811625611630795)
        ·
          refine ⟨321328775840717438417446193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214219183893811625611630795 321328775840717438417446193)
          ·
            refine ⟨240996581880538078813084645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321328775840717438417446193 240996581880538078813084645)
            ·
              refine ⟨45186859102600889777453371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240996581880538078813084645 45186859102600889777453371)
              ·
                refine ⟨67780288653901334666180057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45186859102600889777453371 67780288653901334666180057)
                ·
                  refine ⟨50835216490426000999635043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67780288653901334666180057 50835216490426000999635043)
                  ·
                    refine ⟨76252824735639001499452565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50835216490426000999635043 76252824735639001499452565)
                    ·
                      refine ⟨3574351159483078195286839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76252824735639001499452565 3574351159483078195286839)
                      ·
                        rfl

theorem cell23_6961024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_6961024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961024 prefixEnd_6961024 := by exact prefixLift 6961024
  have htrace : WordTrace (prefixWord ++ tailWord_6961024) baseStart_6961024 baseEnd_6961024 := by
    simpa [prefixWord, tailWord_6961024, baseEnd_6961024] using wordTrace_append hprefix tailTrace_6961024
  have hstable : (prefixWord ++ tailWord_6961024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961024).length < 2 ^ (prefixWord ++ tailWord_6961024).sum := by decide
  have hdescent : baseEnd_6961024 < baseStart_6961024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961088 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 4, 3, 2]
def baseStart_6961088 : Nat := 118140960795 + 6961088 * 2 ^ 59
def prefixEnd_6961088 : Nat := 4983230072969 + 3 ^ 40 * 6961088 * 2
def baseEnd_6961088 : Nat := 3574384022244965944886545

theorem tailTrace_6961088 : CollatzResearch.WordTrace tailWord_6961088 prefixEnd_6961088 3574384022244965944886545 := by
  unfold tailWord_6961088
  simp only [CollatzResearch.WordTrace]
  refine ⟨126945868702587255012797959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169261158270116340017063945 126945868702587255012797959)
  ·
    refine ⟨190418803053880882519196939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126945868702587255012797959 190418803053880882519196939)
    ·
      refine ⟨285628204580821323778795409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190418803053880882519196939 285628204580821323778795409)
      ·
        refine ⟨214221153435615992834096557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285628204580821323778795409 214221153435615992834096557)
        ·
          refine ⟨80332932538355997312786209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214221153435615992834096557 80332932538355997312786209)
          ·
            refine ⟨60249699403766997984589657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80332932538355997312786209 60249699403766997984589657)
            ·
              refine ⟨45187274552825248488442243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60249699403766997984589657 45187274552825248488442243)
              ·
                refine ⟨67780911829237872732663365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45187274552825248488442243 67780911829237872732663365)
                ·
                  refine ⟨12708920967982101137374381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67780911829237872732663365 12708920967982101137374381)
                  ·
                    refine ⟨4765845362993287926515393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12708920967982101137374381 4765845362993287926515393)
                    ·
                      refine ⟨3574384022244965944886545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765845362993287926515393 3574384022244965944886545)
                      ·
                        rfl

theorem cell23_6961088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_6961088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961088 prefixEnd_6961088 := by exact prefixLift 6961088
  have htrace : WordTrace (prefixWord ++ tailWord_6961088) baseStart_6961088 baseEnd_6961088 := by
    simpa [prefixWord, tailWord_6961088, baseEnd_6961088] using wordTrace_append hprefix tailTrace_6961088
  have hstable : (prefixWord ++ tailWord_6961088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961088).length < 2 ^ (prefixWord ++ tailWord_6961088).sum := by decide
  have hdescent : baseEnd_6961088 < baseStart_6961088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961131 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4]
def baseStart_6961131 : Nat := 118140960795 + 6961131 * 2 ^ 59
def prefixEnd_6961131 : Nat := 4983230072969 + 3 ^ 40 * 6961131 * 2
def baseEnd_6961131 : Nat := 3574406101913109276648847

theorem tailTrace_6961131 : CollatzResearch.WordTrace tailWord_6961131 prefixEnd_6961131 3574406101913109276648847 := by
  unfold tailWord_6961131
  simp only [CollatzResearch.WordTrace]
  refine ⟨253893305744018728369411247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169262203829345818912940831 253893305744018728369411247)
  ·
    refine ⟨380839958616028092554116871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253893305744018728369411247 380839958616028092554116871)
    ·
      refine ⟨571259937924042138831175307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380839958616028092554116871 571259937924042138831175307)
      ·
        refine ⟨856889906886063208246762961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571259937924042138831175307 856889906886063208246762961)
        ·
          refine ⟨642667430164547406185072221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856889906886063208246762961 642667430164547406185072221)
          ·
            refine ⟨241000286311705277319402083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642667430164547406185072221 241000286311705277319402083)
            ·
              refine ⟨361500429467557915979103125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241000286311705277319402083 361500429467557915979103125)
              ·
                refine ⟨16945332631291777311520459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361500429467557915979103125 16945332631291777311520459)
                ·
                  refine ⟨25417998946937665967280689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16945332631291777311520459 25417998946937665967280689)
                  ·
                    refine ⟨19063499210203249475460517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25417998946937665967280689 19063499210203249475460517)
                    ·
                      refine ⟨3574406101913109276648847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19063499210203249475460517 3574406101913109276648847)
                      ·
                        rfl

theorem cell23_6961131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 4].length) (baseStart_6961131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961131 prefixEnd_6961131 := by exact prefixLift 6961131
  have htrace : WordTrace (prefixWord ++ tailWord_6961131) baseStart_6961131 baseEnd_6961131 := by
    simpa [prefixWord, tailWord_6961131, baseEnd_6961131] using wordTrace_append hprefix tailTrace_6961131
  have hstable : (prefixWord ++ tailWord_6961131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961131).length < 2 ^ (prefixWord ++ tailWord_6961131).sum := by decide
  have hdescent : baseEnd_6961131 < baseStart_6961131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961185 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6961185 : Nat := 118140960795 + 6961185 * 2 ^ 59
def prefixEnd_6961185 : Nat := 4983230072969 + 3 ^ 40 * 6961185 * 2
def baseEnd_6961185 : Nat := 3574433829868452065373599

theorem tailTrace_6961185 : CollatzResearch.WordTrace tailWord_6961185 prefixEnd_6961185 3574433829868452065373599 := by
  unfold tailWord_6961185
  simp only [CollatzResearch.WordTrace]
  refine ⟨253895275285823095591877009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169263516857215397061251339 253895275285823095591877009)
  ·
    refine ⟨190421456464367321693907757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253895275285823095591877009 190421456464367321693907757)
    ·
      refine ⟨71408046174137745635215409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190421456464367321693907757 71408046174137745635215409)
      ·
        refine ⟨53556034630603309226411557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71408046174137745635215409 53556034630603309226411557)
        ·
          refine ⟨10041756493238120479952167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53556034630603309226411557 10041756493238120479952167)
          ·
            refine ⟨15062634739857180719928251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10041756493238120479952167 15062634739857180719928251)
            ·
              refine ⟨22593952109785771079892377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15062634739857180719928251 22593952109785771079892377)
              ·
                refine ⟨16945464082339328309919283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22593952109785771079892377 16945464082339328309919283)
                ·
                  refine ⟨25418196123508992464878925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16945464082339328309919283 25418196123508992464878925)
                  ·
                    refine ⟨9531823546315872174329597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25418196123508992464878925 9531823546315872174329597)
                    ·
                      refine ⟨3574433829868452065373599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9531823546315872174329597 3574433829868452065373599)
                      ·
                        rfl

theorem cell23_6961185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6961185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961185 prefixEnd_6961185 := by exact prefixLift 6961185
  have htrace : WordTrace (prefixWord ++ tailWord_6961185) baseStart_6961185 baseEnd_6961185 := by
    simpa [prefixWord, tailWord_6961185, baseEnd_6961185] using wordTrace_append hprefix tailTrace_6961185
  have hstable : (prefixWord ++ tailWord_6961185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961185).length < 2 ^ (prefixWord ++ tailWord_6961185).sum := by decide
  have hdescent : baseEnd_6961185 < baseStart_6961185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961202 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_6961202 : Nat := 118140960795 + 6961202 * 2 ^ 59
def prefixEnd_6961202 : Nat := 4983230072969 + 3 ^ 40 * 6961202 * 2
def baseEnd_6961202 : Nat := 3574442559039578498861021

theorem tailTrace_6961202 : CollatzResearch.WordTrace tailWord_6961202 prefixEnd_6961202 3574442559039578498861021 := by
  unfold tailWord_6961202
  simp only [CollatzResearch.WordTrace]
  refine ⟨63473973831690376873811465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169263930217841004996830573 63473973831690376873811465)
  ·
    refine ⟨47605480373767782655358599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63473973831690376873811465 47605480373767782655358599)
    ·
      refine ⟨71408220560651673983037899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47605480373767782655358599 71408220560651673983037899)
      ·
        refine ⟨107112330840977510974556849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71408220560651673983037899 107112330840977510974556849)
        ·
          refine ⟨80334248130733133230917637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107112330840977510974556849 80334248130733133230917637)
          ·
            refine ⟨15062671524512462480797057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80334248130733133230917637 15062671524512462480797057)
            ·
              refine ⟨11297003643384346860597793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15062671524512462480797057 11297003643384346860597793)
              ·
                refine ⟨8472752732538260145448345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11297003643384346860597793 8472752732538260145448345)
                ·
                  refine ⟨6354564549403695109086259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8472752732538260145448345 6354564549403695109086259)
                  ·
                    refine ⟨9531846824105542663629389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6354564549403695109086259 9531846824105542663629389)
                    ·
                      refine ⟨3574442559039578498861021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9531846824105542663629389 3574442559039578498861021)
                      ·
                        rfl

theorem cell23_6961202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_6961202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961202 prefixEnd_6961202 := by exact prefixLift 6961202
  have htrace : WordTrace (prefixWord ++ tailWord_6961202) baseStart_6961202 baseEnd_6961202 := by
    simpa [prefixWord, tailWord_6961202, baseEnd_6961202] using wordTrace_append hprefix tailTrace_6961202
  have hstable : (prefixWord ++ tailWord_6961202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961202).length < 2 ^ (prefixWord ++ tailWord_6961202).sum := by decide
  have hdescent : baseEnd_6961202 < baseStart_6961202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961225 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 1, 4, 2]
def baseStart_6961225 : Nat := 118140960795 + 6961225 * 2 ^ 59
def prefixEnd_6961225 : Nat := 4983230072969 + 3 ^ 40 * 6961225 * 2
def baseEnd_6961225 : Nat := 3574454369094631908873415

theorem tailTrace_6961225 : CollatzResearch.WordTrace tailWord_6961225 prefixEnd_6961225 3574454369094631908873415 := by
  unfold tailWord_6961225
  simp only [CollatzResearch.WordTrace]
  refine ⟨253896734205678182423333129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169264489470452121615555419 253896734205678182423333129)
  ·
    refine ⟨190422550654258636817499847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253896734205678182423333129 190422550654258636817499847)
    ·
      refine ⟨285633825981387955226249771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190422550654258636817499847 285633825981387955226249771)
      ·
        refine ⟨428450738972081932839374657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285633825981387955226249771 428450738972081932839374657)
        ·
          refine ⟨321338054229061449629530993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428450738972081932839374657 321338054229061449629530993)
          ·
            refine ⟨241003540671796087222148245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321338054229061449629530993 241003540671796087222148245)
            ·
              refine ⟨11297040968990441588538199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241003540671796087222148245 11297040968990441588538199)
              ·
                refine ⟨16945561453485662382807299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11297040968990441588538199 16945561453485662382807299)
                ·
                  refine ⟨25418342180228493574210949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16945561453485662382807299 25418342180228493574210949)
                  ·
                    refine ⟨4765939158792842545164553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25418342180228493574210949 4765939158792842545164553)
                    ·
                      refine ⟨3574454369094631908873415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4765939158792842545164553 3574454369094631908873415)
                      ·
                        rfl

theorem cell23_6961225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 4, 2].length) (baseStart_6961225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961225 prefixEnd_6961225 := by exact prefixLift 6961225
  have htrace : WordTrace (prefixWord ++ tailWord_6961225) baseStart_6961225 baseEnd_6961225 := by
    simpa [prefixWord, tailWord_6961225, baseEnd_6961225] using wordTrace_append hprefix tailTrace_6961225
  have hstable : (prefixWord ++ tailWord_6961225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961225).length < 2 ^ (prefixWord ++ tailWord_6961225).sum := by decide
  have hdescent : baseEnd_6961225 < baseStart_6961225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961231 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 7]
def baseStart_6961231 : Nat := 118140960795 + 6961231 * 2 ^ 59
def prefixEnd_6961231 : Nat := 4983230072969 + 3 ^ 40 * 6961231 * 2
def baseEnd_6961231 : Nat := 397161938886506542822043

theorem tailTrace_6961231 : CollatzResearch.WordTrace tailWord_6961231 prefixEnd_6961231 397161938886506542822043 := by
  unfold tailWord_6961231
  simp only [CollatzResearch.WordTrace]
  refine ⟨253896953043656445448051547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169264635362437630298701031 253896953043656445448051547)
  ·
    refine ⟨380845429565484668172077321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253896953043656445448051547 380845429565484668172077321)
    ·
      refine ⟨285634072174113501129057991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380845429565484668172077321 285634072174113501129057991)
      ·
        refine ⟨428451108261170251693586987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285634072174113501129057991 428451108261170251693586987)
        ·
          refine ⟨642676662391755377540380481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428451108261170251693586987 642676662391755377540380481)
          ·
            refine ⟨482007496793816533155285361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642676662391755377540380481 482007496793816533155285361)
            ·
              refine ⟨361505622595362399866464021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482007496793816533155285361 361505622595362399866464021)
              ·
                refine ⟨16945576059157612493740501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361505622595362399866464021 16945576059157612493740501)
                ·
                  refine ⟨397161938886506542822043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16945576059157612493740501 397161938886506542822043)
                  ·
                    rfl

theorem cell23_6961231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 7].length) (baseStart_6961231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961231 prefixEnd_6961231 := by exact prefixLift 6961231
  have htrace : WordTrace (prefixWord ++ tailWord_6961231) baseStart_6961231 baseEnd_6961231 := by
    simpa [prefixWord, tailWord_6961231, baseEnd_6961231] using wordTrace_append hprefix tailTrace_6961231
  have hstable : (prefixWord ++ tailWord_6961231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961231).length < 2 ^ (prefixWord ++ tailWord_6961231).sum := by decide
  have hdescent : baseEnd_6961231 < baseStart_6961231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961322 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6961322 : Nat := 118140960795 + 6961322 * 2 ^ 59
def prefixEnd_6961322 : Nat := 4983230072969 + 3 ^ 40 * 6961322 * 2
def baseEnd_6961322 : Nat := 3574504176718118029360469

theorem tailTrace_6961322 : CollatzResearch.WordTrace tailWord_6961322 prefixEnd_6961322 3574504176718118029360469 := by
  unfold tailWord_6961322
  simp only [CollatzResearch.WordTrace]
  refine ⟨63475068021581691997403555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169266848057551178659742813 63475068021581691997403555)
  ·
    refine ⟨95212602032372537996105333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63475068021581691997403555 95212602032372537996105333)
    ·
      refine ⟨8926181440534925437134875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95212602032372537996105333 8926181440534925437134875)
      ·
        refine ⟨13389272160802388155702313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8926181440534925437134875 13389272160802388155702313)
        ·
          refine ⟨10041954120601791116776735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13389272160802388155702313 10041954120601791116776735)
          ·
            refine ⟨15062931180902686675165103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10041954120601791116776735 15062931180902686675165103)
            ·
              refine ⟨22594396771354030012747655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15062931180902686675165103 22594396771354030012747655)
              ·
                refine ⟨33891595157031045019121483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22594396771354030012747655 33891595157031045019121483)
                ·
                  refine ⟨50837392735546567528682225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33891595157031045019121483 50837392735546567528682225)
                  ·
                    refine ⟨38128044551659925646511669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50837392735546567528682225 38128044551659925646511669)
                    ·
                      refine ⟨3574504176718118029360469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38128044551659925646511669 3574504176718118029360469)
                      ·
                        rfl

theorem cell23_6961322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6961322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961322 prefixEnd_6961322 := by exact prefixLift 6961322
  have htrace : WordTrace (prefixWord ++ tailWord_6961322) baseStart_6961322 baseEnd_6961322 := by
    simpa [prefixWord, tailWord_6961322, baseEnd_6961322] using wordTrace_append hprefix tailTrace_6961322
  have hstable : (prefixWord ++ tailWord_6961322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961322).length < 2 ^ (prefixWord ++ tailWord_6961322).sum := by decide
  have hdescent : baseEnd_6961322 < baseStart_6961322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961375 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 3, 5, 2]
def baseStart_6961375 : Nat := 118140960795 + 6961375 * 2 ^ 59
def prefixEnd_6961375 : Nat := 4983230072969 + 3 ^ 40 * 6961375 * 2
def baseEnd_6961375 : Nat := 3574531391192806321997725

theorem tailTrace_6961375 : CollatzResearch.WordTrace tailWord_6961375 prefixEnd_6961375 3574531391192806321997725 := by
  unfold tailWord_6961375
  simp only [CollatzResearch.WordTrace]
  refine ⟨253902205155134758041293579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169268136770089838694195719 253902205155134758041293579)
  ·
    refine ⟨380853307732702137061940369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253902205155134758041293579 380853307732702137061940369)
    ·
      refine ⟨285639980799526602796455277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380853307732702137061940369 285639980799526602796455277)
      ·
        refine ⟨107114992799822476048670729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285639980799526602796455277 107114992799822476048670729)
        ·
          refine ⟨80336244599866857036503047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107114992799822476048670729 80336244599866857036503047)
          ·
            refine ⟨120504366899800285554754571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80336244599866857036503047 120504366899800285554754571)
            ·
              refine ⟨180756550349700428332131857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120504366899800285554754571 180756550349700428332131857)
              ·
                refine ⟨135567412762275321249098893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180756550349700428332131857 135567412762275321249098893)
                ·
                  refine ⟨50837779785853245468412085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135567412762275321249098893 50837779785853245468412085)
                  ·
                    refine ⟨4766041854923741762663633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50837779785853245468412085 4766041854923741762663633)
                    ·
                      refine ⟨3574531391192806321997725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766041854923741762663633 3574531391192806321997725)
                      ·
                        rfl

theorem cell23_6961375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_6961375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961375 prefixEnd_6961375 := by exact prefixLift 6961375
  have htrace : WordTrace (prefixWord ++ tailWord_6961375) baseStart_6961375 baseEnd_6961375 := by
    simpa [prefixWord, tailWord_6961375, baseEnd_6961375] using wordTrace_append hprefix tailTrace_6961375
  have hstable : (prefixWord ++ tailWord_6961375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961375).length < 2 ^ (prefixWord ++ tailWord_6961375).sum := by decide
  have hdescent : baseEnd_6961375 < baseStart_6961375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961416 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_6961416 : Nat := 118140960795 + 6961416 * 2 ^ 59
def prefixEnd_6961416 : Nat := 4983230072969 + 3 ^ 40 * 6961416 * 2
def baseEnd_6961416 : Nat := 3574552443899640661585037

theorem tailTrace_6961416 : CollatzResearch.WordTrace tailWord_6961416 prefixEnd_6961416 3574552443899640661585037 := by
  unfold tailWord_6961416
  simp only [CollatzResearch.WordTrace]
  refine ⟨126951850273993111021768051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169269133698657481362357401 126951850273993111021768051)
  ·
    refine ⟨190427775410989666532652077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126951850273993111021768051 190427775410989666532652077)
    ·
      refine ⟨71410415779121124949744529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190427775410989666532652077 71410415779121124949744529)
      ·
        refine ⟨53557811834340843712308397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71410415779121124949744529 53557811834340843712308397)
        ·
          refine ⟨20084179437877816392115649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53557811834340843712308397 20084179437877816392115649)
          ·
            refine ⟨15063134578408362294086737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20084179437877816392115649 15063134578408362294086737)
            ·
              refine ⟨11297350933806271720565053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15063134578408362294086737 11297350933806271720565053)
              ·
                refine ⟨4236506600177351895211895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11297350933806271720565053 4236506600177351895211895)
                ·
                  refine ⟨6354759900266027842817843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4236506600177351895211895 6354759900266027842817843)
                  ·
                    refine ⟨9532139850399041764226765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6354759900266027842817843 9532139850399041764226765)
                    ·
                      refine ⟨3574552443899640661585037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532139850399041764226765 3574552443899640661585037)
                      ·
                        rfl

theorem cell23_6961416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_6961416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961416 prefixEnd_6961416 := by exact prefixLift 6961416
  have htrace : WordTrace (prefixWord ++ tailWord_6961416) baseStart_6961416 baseEnd_6961416 := by
    simpa [prefixWord, tailWord_6961416, baseEnd_6961416] using wordTrace_append hprefix tailTrace_6961416
  have hstable : (prefixWord ++ tailWord_6961416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961416).length < 2 ^ (prefixWord ++ tailWord_6961416).sum := by decide
  have hdescent : baseEnd_6961416 < baseStart_6961416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961422 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_6961422 : Nat := 118140960795 + 6961422 * 2 ^ 59
def prefixEnd_6961422 : Nat := 4983230072969 + 3 ^ 40 * 6961422 * 2
def baseEnd_6961422 : Nat := 3574555524783567638110009

theorem tailTrace_6961422 : CollatzResearch.WordTrace tailWord_6961422 prefixEnd_6961422 3574555524783567638110009 := by
  unfold tailWord_6961422
  simp only [CollatzResearch.WordTrace]
  refine ⟨31737989923245560633531815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169269279590642990045503013 31737989923245560633531815)
  ·
    refine ⟨47606984884868340950297723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31737989923245560633531815 47606984884868340950297723)
    ·
      refine ⟨71410477327302511425446585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47606984884868340950297723 71410477327302511425446585)
      ·
        refine ⟨53557857995476883569084939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71410477327302511425446585 53557857995476883569084939)
        ·
          refine ⟨80336786993215325353627409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53557857995476883569084939 80336786993215325353627409)
          ·
            refine ⟨60252590244911494015220557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80336786993215325353627409 60252590244911494015220557)
            ·
              refine ⟨22594721341841810255707709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60252590244911494015220557 22594721341841810255707709)
              ·
                refine ⟨8473020503190678845890391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22594721341841810255707709 8473020503190678845890391)
                ·
                  refine ⟨12709530754786018268835587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8473020503190678845890391 12709530754786018268835587)
                  ·
                    refine ⟨19064296132179027403253381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12709530754786018268835587 19064296132179027403253381)
                    ·
                      refine ⟨3574555524783567638110009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19064296132179027403253381 3574555524783567638110009)
                      ·
                        rfl

theorem cell23_6961422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_6961422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961422 prefixEnd_6961422 := by exact prefixLift 6961422
  have htrace : WordTrace (prefixWord ++ tailWord_6961422) baseStart_6961422 baseEnd_6961422 := by
    simpa [prefixWord, tailWord_6961422, baseEnd_6961422] using wordTrace_append hprefix tailTrace_6961422
  have hstable : (prefixWord ++ tailWord_6961422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961422).length < 2 ^ (prefixWord ++ tailWord_6961422).sum := by decide
  have hdescent : baseEnd_6961422 < baseStart_6961422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961439 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 3, 2, 2]
def baseStart_6961439 : Nat := 118140960795 + 6961439 * 2 ^ 59
def prefixEnd_6961439 : Nat := 4983230072969 + 3 ^ 40 * 6961439 * 2
def baseEnd_6961439 : Nat := 3574564253954694071597431

theorem tailTrace_6961439 : CollatzResearch.WordTrace tailWord_6961439 prefixEnd_6961439 3574564253954694071597431 := by
  unfold tailWord_6961439
  simp only [CollatzResearch.WordTrace]
  refine ⟨253904539426902896971623371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169269692951268597981082247 253904539426902896971623371)
  ·
    refine ⟨380856809140354345457435057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253904539426902896971623371 380856809140354345457435057)
    ·
      refine ⟨285642606855265759093076293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380856809140354345457435057 285642606855265759093076293)
      ·
        refine ⟨53557988785362329829951805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285642606855265759093076293 53557988785362329829951805)
        ·
          refine ⟨20084245794510873686231927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53557988785362329829951805 20084245794510873686231927)
          ·
            refine ⟨30126368691766310529347891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20084245794510873686231927 30126368691766310529347891)
            ·
              refine ⟨45189553037649465794021837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30126368691766310529347891 45189553037649465794021837)
              ·
                refine ⟨16946082389118549672758189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45189553037649465794021837 16946082389118549672758189)
                ·
                  refine ⟨6354780895919456127284321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16946082389118549672758189 6354780895919456127284321)
                  ·
                    refine ⟨4766085671939592095463241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6354780895919456127284321 4766085671939592095463241)
                    ·
                      refine ⟨3574564253954694071597431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766085671939592095463241 3574564253954694071597431)
                      ·
                        rfl

theorem cell23_6961439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_6961439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961439 prefixEnd_6961439 := by exact prefixLift 6961439
  have htrace : WordTrace (prefixWord ++ tailWord_6961439) baseStart_6961439 baseEnd_6961439 := by
    simpa [prefixWord, tailWord_6961439, baseEnd_6961439] using wordTrace_append hprefix tailTrace_6961439
  have hstable : (prefixWord ++ tailWord_6961439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961439).length < 2 ^ (prefixWord ++ tailWord_6961439).sum := by decide
  have hdescent : baseEnd_6961439 < baseStart_6961439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961442 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6961442 : Nat := 118140960795 + 6961442 * 2 ^ 59
def prefixEnd_6961442 : Nat := 4983230072969 + 3 ^ 40 * 6961442 * 2
def baseEnd_6961442 : Nat := 3574565794396657559859917

theorem tailTrace_6961442 : CollatzResearch.WordTrace tailWord_6961442 prefixEnd_6961442 3574565794396657559859917 := by
  unfold tailWord_6961442
  simp only [CollatzResearch.WordTrace]
  refine ⟨63476162211473007120995645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169269765897261352322655053 63476162211473007120995645)
  ·
    refine ⟨23803560829302377670373367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63476162211473007120995645 23803560829302377670373367)
    ·
      refine ⟨35705341243953566505560051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23803560829302377670373367 35705341243953566505560051)
      ·
        refine ⟨53558011865930349758340077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35705341243953566505560051 53558011865930349758340077)
        ·
          refine ⟨20084254449723881159377529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53558011865930349758340077 20084254449723881159377529)
          ·
            refine ⟨15063190837292910869533147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20084254449723881159377529 15063190837292910869533147)
            ·
              refine ⟨22594786255939366304299721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15063190837292910869533147 22594786255939366304299721)
              ·
                refine ⟨16946089691954524728224791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22594786255939366304299721 16946089691954524728224791)
                ·
                  refine ⟨25419134537931787092337187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16946089691954524728224791 25419134537931787092337187)
                  ·
                    refine ⟨38128701806897680638505781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25419134537931787092337187 38128701806897680638505781)
                    ·
                      refine ⟨3574565794396657559859917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38128701806897680638505781 3574565794396657559859917)
                      ·
                        rfl

theorem cell23_6961442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6961442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961442 prefixEnd_6961442 := by exact prefixLift 6961442
  have htrace : WordTrace (prefixWord ++ tailWord_6961442) baseStart_6961442 baseEnd_6961442 := by
    simpa [prefixWord, tailWord_6961442, baseEnd_6961442] using wordTrace_append hprefix tailTrace_6961442
  have hstable : (prefixWord ++ tailWord_6961442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961442).length < 2 ^ (prefixWord ++ tailWord_6961442).sum := by decide
  have hdescent : baseEnd_6961442 < baseStart_6961442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961482 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_6961482 : Nat := 118140960795 + 6961482 * 2 ^ 59
def prefixEnd_6961482 : Nat := 4983230072969 + 3 ^ 40 * 6961482 * 2
def baseEnd_6961482 : Nat := 3574586333622837403359733

theorem tailTrace_6961482 : CollatzResearch.WordTrace tailWord_6961482 prefixEnd_6961482 3574586333622837403359733 := by
  unfold tailWord_6961482
  simp only [CollatzResearch.WordTrace]
  refine ⟨63476526941436778828859675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169270738510498076876959133 63476526941436778828859675)
  ·
    refine ⟨95214790412155168243289513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63476526941436778828859675 95214790412155168243289513)
    ·
      refine ⟨71411092809116376182467135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95214790412155168243289513 71411092809116376182467135)
      ·
        refine ⟨107116639213674564273700703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71411092809116376182467135 107116639213674564273700703)
        ·
          refine ⟨160674958820511846410551055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107116639213674564273700703 160674958820511846410551055)
          ·
            refine ⟨241012438230767769615826583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160674958820511846410551055 241012438230767769615826583)
            ·
              refine ⟨361518657346151654423739875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241012438230767769615826583 361518657346151654423739875)
              ·
                refine ⟨542277986019227481635609813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361518657346151654423739875 542277986019227481635609813)
                ·
                  refine ⟨12709640297325644100834605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 542277986019227481635609813 12709640297325644100834605)
                  ·
                    refine ⟨4766115111497116537812977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12709640297325644100834605 4766115111497116537812977)
                    ·
                      refine ⟨3574586333622837403359733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4766115111497116537812977 3574586333622837403359733)
                      ·
                        rfl

theorem cell23_6961482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_6961482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961482 prefixEnd_6961482 := by exact prefixLift 6961482
  have htrace : WordTrace (prefixWord ++ tailWord_6961482) baseStart_6961482 baseEnd_6961482 := by
    simpa [prefixWord, tailWord_6961482, baseEnd_6961482] using wordTrace_append hprefix tailTrace_6961482
  have hstable : (prefixWord ++ tailWord_6961482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961482).length < 2 ^ (prefixWord ++ tailWord_6961482).sum := by decide
  have hdescent : baseEnd_6961482 < baseStart_6961482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961495 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_6961495 : Nat := 118140960795 + 6961495 * 2 ^ 59
def prefixEnd_6961495 : Nat := 4983230072969 + 3 ^ 40 * 6961495 * 2
def baseEnd_6961495 : Nat := 3574593008871345852497173

theorem tailTrace_6961495 : CollatzResearch.WordTrace tailWord_6961495 prefixEnd_6961495 3574593008871345852497173 := by
  unfold tailWord_6961495
  simp only [CollatzResearch.WordTrace]
  refine ⟨253906581914700018535661939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169271054609800012357107959 253906581914700018535661939)
  ·
    refine ⟨380859872872050027803492909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253906581914700018535661939 380859872872050027803492909)
    ·
      refine ⟨142822452327018760426309841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380859872872050027803492909 142822452327018760426309841)
      ·
        refine ⟨107116839245264070319732381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142822452327018760426309841 107116839245264070319732381)
        ·
          refine ⟨40168814716974026369899643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107116839245264070319732381 40168814716974026369899643)
          ·
            refine ⟨60253222075461039554849465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40168814716974026369899643 60253222075461039554849465)
            ·
              refine ⟨45189916556595779666137099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60253222075461039554849465 45189916556595779666137099)
              ·
                refine ⟨67784874834893669499205649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45189916556595779666137099 67784874834893669499205649)
                ·
                  refine ⟨50838656126170252124404237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67784874834893669499205649 50838656126170252124404237)
                  ·
                    refine ⟨19064496047313844546651589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50838656126170252124404237 19064496047313844546651589)
                    ·
                      refine ⟨3574593008871345852497173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19064496047313844546651589 3574593008871345852497173)
                      ·
                        rfl

theorem cell23_6961495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_6961495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961495 prefixEnd_6961495 := by exact prefixLift 6961495
  have htrace : WordTrace (prefixWord ++ tailWord_6961495) baseStart_6961495 baseEnd_6961495 := by
    simpa [prefixWord, tailWord_6961495, baseEnd_6961495] using wordTrace_append hprefix tailTrace_6961495
  have hstable : (prefixWord ++ tailWord_6961495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961495).length < 2 ^ (prefixWord ++ tailWord_6961495).sum := by decide
  have hdescent : baseEnd_6961495 < baseStart_6961495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961500 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6961500 : Nat := 118140960795 + 6961500 * 2 ^ 59
def prefixEnd_6961500 : Nat := 4983230072969 + 3 ^ 40 * 6961500 * 2
def baseEnd_6961500 : Nat := 1191531858758206110978217

theorem tailTrace_6961500 : CollatzResearch.WordTrace tailWord_6961500 prefixEnd_6961500 1191531858758206110978217 := by
  unfold tailWord_6961500
  simp only [CollatzResearch.WordTrace]
  refine ⟨126953382139840952194796977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169271176186454602926395969 126953382139840952194796977)
  ·
    refine ⟨95215036604880714146097733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126953382139840952194796977 95215036604880714146097733)
    ·
      refine ⟨17852819363415133902393325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95215036604880714146097733 17852819363415133902393325)
      ·
        refine ⟨6694807261280675213397497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17852819363415133902393325 6694807261280675213397497)
        ·
          refine ⟨5021105445960506410048123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6694807261280675213397497 5021105445960506410048123)
          ·
            refine ⟨7531658168940759615072185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5021105445960506410048123 7531658168940759615072185)
            ·
              refine ⟨5648743626705569711304139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7531658168940759615072185 5648743626705569711304139)
              ·
                refine ⟨8473115440058354566956209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648743626705569711304139 8473115440058354566956209)
                ·
                  refine ⟨6354836580043765925217157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8473115440058354566956209 6354836580043765925217157)
                  ·
                    refine ⟨1191531858758206110978217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6354836580043765925217157 1191531858758206110978217)
                    ·
                      rfl

theorem cell23_6961500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6961500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961500 prefixEnd_6961500 := by exact prefixLift 6961500
  have htrace : WordTrace (prefixWord ++ tailWord_6961500) baseStart_6961500 baseEnd_6961500 := by
    simpa [prefixWord, tailWord_6961500, baseEnd_6961500] using wordTrace_append hprefix tailTrace_6961500
  have hstable : (prefixWord ++ tailWord_6961500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961500).length < 2 ^ (prefixWord ++ tailWord_6961500).sum := by decide
  have hdescent : baseEnd_6961500 < baseStart_6961500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6961506 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_6961506 : Nat := 118140960795 + 6961506 * 2 ^ 59
def prefixEnd_6961506 : Nat := 4983230072969 + 3 ^ 40 * 6961506 * 2
def baseEnd_6961506 : Nat := 3574598657158545309459623

theorem tailTrace_6961506 : CollatzResearch.WordTrace tailWord_6961506 prefixEnd_6961506 3574598657158545309459623 := by
  unfold tailWord_6961506
  simp only [CollatzResearch.WordTrace]
  refine ⟨63476745779415041853578093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169271322078440111609541581 63476745779415041853578093)
  ·
    refine ⟨23803779667280640695091785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63476745779415041853578093 23803779667280640695091785)
    ·
      refine ⟨17852834750460480521318839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23803779667280640695091785 17852834750460480521318839)
      ·
        refine ⟨26779252125690720781978259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17852834750460480521318839 26779252125690720781978259)
        ·
          refine ⟨40168878188536081172967389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26779252125690720781978259 40168878188536081172967389)
          ·
            refine ⟨15063329320701030439862771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40168878188536081172967389 15063329320701030439862771)
            ·
              refine ⟨22594993981051545659794157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15063329320701030439862771 22594993981051545659794157)
              ·
                refine ⟨8473122742894329622422809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22594993981051545659794157 8473122742894329622422809)
                ·
                  refine ⟨6354842057170747216817107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8473122742894329622422809 6354842057170747216817107)
                  ·
                    refine ⟨9532263085756120825225661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6354842057170747216817107 9532263085756120825225661)
                    ·
                      refine ⟨3574598657158545309459623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9532263085756120825225661 3574598657158545309459623)
                      ·
                        rfl

theorem cell23_6961506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_6961506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6961506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6961506 prefixEnd_6961506 := by exact prefixLift 6961506
  have htrace : WordTrace (prefixWord ++ tailWord_6961506) baseStart_6961506 baseEnd_6961506 := by
    simpa [prefixWord, tailWord_6961506, baseEnd_6961506] using wordTrace_append hprefix tailTrace_6961506
  have hstable : (prefixWord ++ tailWord_6961506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6961506).length < 2 ^ (prefixWord ++ tailWord_6961506).sum := by decide
  have hdescent : baseEnd_6961506 < baseStart_6961506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6961506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
