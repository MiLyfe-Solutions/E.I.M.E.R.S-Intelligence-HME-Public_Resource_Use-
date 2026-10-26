import V185TrunkScan22Chunk348

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3112922 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_3112922 : Nat := 118140960795 + 3112922 * 2 ^ 59
def prefixEnd_3112922 : Nat := 4983230072969 + 3 ^ 40 * 3112922 * 2
def baseEnd_3112922 : Nat := 355205605767861091568653

theorem tailTrace_3112922 : CollatzResearch.WordTrace tailWord_3112922 prefixEnd_3112922 355205605767861091568653 := by
  unfold tailWord_3112922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28384398207105678399077255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75691728552281809064206013 28384398207105678399077255)
  ·
    refine ⟨42576597310658517598615883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28384398207105678399077255 42576597310658517598615883)
    ·
      refine ⟨63864895965987776397923825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42576597310658517598615883 63864895965987776397923825)
      ·
        refine ⟨47898671974490832298442869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63864895965987776397923825 47898671974490832298442869)
        ·
          refine ⟨4490500497608515527979019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47898671974490832298442869 4490500497608515527979019)
          ·
            refine ⟨6735750746412773291968529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490500497608515527979019 6735750746412773291968529)
            ·
              refine ⟨5051813059809579968976397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6735750746412773291968529 5051813059809579968976397)
              ·
                refine ⟨1894429897428592488366149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5051813059809579968976397 1894429897428592488366149)
                ·
                  refine ⟨355205605767861091568653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894429897428592488366149 355205605767861091568653)
                  ·
                    rfl

theorem cell22_3112922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_3112922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112922 prefixEnd_3112922 := by exact prefixLift 3112922
  have htrace : WordTrace (prefixWord ++ tailWord_3112922) baseStart_3112922 baseEnd_3112922 := by
    simpa [prefixWord, tailWord_3112922, baseEnd_3112922] using wordTrace_append hprefix tailTrace_3112922
  have hstable : (prefixWord ++ tailWord_3112922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112922).length < 2 ^ (prefixWord ++ tailWord_3112922).sum := by decide
  have hdescent : baseEnd_3112922 < baseStart_3112922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112965 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_3112965 : Nat := 118140960795 + 3112965 * 2 ^ 59
def prefixEnd_3112965 : Nat := 4983230072969 + 3 ^ 40 * 3112965 * 2
def baseEnd_3112965 : Nat := 1065631537082345495880827

theorem tailTrace_3112965 : CollatzResearch.WordTrace tailWord_3112965 prefixEnd_3112965 1065631537082345495880827 := by
  unfold tailWord_3112965
  simp only [CollatzResearch.WordTrace]
  refine ⟨113539161167266931940124349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75692774111511287960082899 113539161167266931940124349)
  ·
    refine ⟨42577185437725099477546631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113539161167266931940124349 42577185437725099477546631)
    ·
      refine ⟨63865778156587649216319947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42577185437725099477546631 63865778156587649216319947)
      ·
        refine ⟨95798667234881473824479921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63865778156587649216319947 95798667234881473824479921)
        ·
          refine ⟨71849000426161105368359941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95798667234881473824479921 71849000426161105368359941)
          ·
            refine ⟨13471687579905207256567489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71849000426161105368359941 13471687579905207256567489)
            ·
              refine ⟨10103765684928905442425617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13471687579905207256567489 10103765684928905442425617)
              ·
                refine ⟨7577824263696679081819213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10103765684928905442425617 7577824263696679081819213)
                ·
                  refine ⟨2841684098886254655682205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7577824263696679081819213 2841684098886254655682205)
                  ·
                    refine ⟨1065631537082345495880827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841684098886254655682205 1065631537082345495880827)
                    ·
                      rfl

theorem cell22_3112965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_3112965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112965 prefixEnd_3112965 := by exact prefixLift 3112965
  have htrace : WordTrace (prefixWord ++ tailWord_3112965) baseStart_3112965 baseEnd_3112965 := by
    simpa [prefixWord, tailWord_3112965, baseEnd_3112965] using wordTrace_append hprefix tailTrace_3112965
  have hstable : (prefixWord ++ tailWord_3112965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112965).length < 2 ^ (prefixWord ++ tailWord_3112965).sum := by decide
  have hdescent : baseEnd_3112965 < baseStart_3112965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3112973 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3112973 : Nat := 118140960795 + 3112973 * 2 ^ 59
def prefixEnd_3112973 : Nat := 4983230072969 + 3 ^ 40 * 3112973 * 2
def baseEnd_3112973 : Nat := 355211425215278713893601

theorem tailTrace_3112973 : CollatzResearch.WordTrace tailWord_3112973 prefixEnd_3112973 355211425215278713893601 := by
  unfold tailWord_3112973
  simp only [CollatzResearch.WordTrace]
  refine ⟨113539452951237949306415573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75692968634158632870943715 113539452951237949306415573)
  ·
    refine ⟨2661080928544639436869115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 113539452951237949306415573 2661080928544639436869115)
    ·
      refine ⟨3991621392816959155303673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661080928544639436869115 3991621392816959155303673)
      ·
        refine ⟨2993716044612719366477755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3991621392816959155303673 2993716044612719366477755)
        ·
          refine ⟨4490574066919079049716633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2993716044612719366477755 4490574066919079049716633)
          ·
            refine ⟨3367930550189309287287475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490574066919079049716633 3367930550189309287287475)
            ·
              refine ⟨5051895825283963930931213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3367930550189309287287475 5051895825283963930931213)
              ·
                refine ⟨1894460934481486474099205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5051895825283963930931213 1894460934481486474099205)
                ·
                  refine ⟨355211425215278713893601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894460934481486474099205 355211425215278713893601)
                  ·
                    rfl

theorem cell22_3112973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3112973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3112973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3112973 prefixEnd_3112973 := by exact prefixLift 3112973
  have htrace : WordTrace (prefixWord ++ tailWord_3112973) baseStart_3112973 baseEnd_3112973 := by
    simpa [prefixWord, tailWord_3112973, baseEnd_3112973] using wordTrace_append hprefix tailTrace_3112973
  have hstable : (prefixWord ++ tailWord_3112973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3112973).length < 2 ^ (prefixWord ++ tailWord_3112973).sum := by decide
  have hdescent : baseEnd_3112973 < baseStart_3112973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3112973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113023 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 6]
def baseStart_3113023 : Nat := 118140960795 + 3113023 * 2 ^ 59
def prefixEnd_3113023 : Nat := 4983230072969 + 3 ^ 40 * 3113023 * 2
def baseEnd_3113023 : Nat := 355217130555884225976883

theorem tailTrace_3113023 : CollatzResearch.WordTrace tailWord_3113023 prefixEnd_3113023 355217130555884225976883 := by
  unfold tailWord_3113023
  simp only [CollatzResearch.WordTrace]
  refine ⟨113541276601056807845735723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75694184400704538563823815 113541276601056807845735723)
  ·
    refine ⟨170311914901585211768603585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113541276601056807845735723 170311914901585211768603585)
    ·
      refine ⟨127733936176188908826452689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170311914901585211768603585 127733936176188908826452689)
      ·
        refine ⟨95800452132141681619839517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127733936176188908826452689 95800452132141681619839517)
        ·
          refine ⟨35925169549553130607439819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95800452132141681619839517 35925169549553130607439819)
          ·
            refine ⟨53887754324329695911159729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35925169549553130607439819 53887754324329695911159729)
            ·
              refine ⟨40415815743247271933369797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53887754324329695911159729 40415815743247271933369797)
              ·
                refine ⟨7577965451858863487506837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40415815743247271933369797 7577965451858863487506837)
                ·
                  refine ⟨355217130555884225976883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7577965451858863487506837 355217130555884225976883)
                  ·
                    rfl

theorem cell22_3113023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 6].length) (baseStart_3113023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113023 prefixEnd_3113023 := by exact prefixLift 3113023
  have htrace : WordTrace (prefixWord ++ tailWord_3113023) baseStart_3113023 baseEnd_3113023 := by
    simpa [prefixWord, tailWord_3113023, baseEnd_3113023] using wordTrace_append hprefix tailTrace_3113023
  have hstable : (prefixWord ++ tailWord_3113023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113023).length < 2 ^ (prefixWord ++ tailWord_3113023).sum := by decide
  have hdescent : baseEnd_3113023 < baseStart_3113023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113070 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3113070 : Nat := 118140960795 + 3113070 * 2 ^ 59
def prefixEnd_3113070 : Nat := 4983230072969 + 3 ^ 40 * 3113070 * 2
def baseEnd_3113070 : Nat := 1065667480728160222005505

theorem tailTrace_3113070 : CollatzResearch.WordTrace tailWord_3113070 prefixEnd_3113070 1065667480728160222005505 := by
  unfold tailWord_3113070
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192873853985816859087083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75695327221257689915131109 14192873853985816859087083)
  ·
    refine ⟨21289310780978725288630625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14192873853985816859087083 21289310780978725288630625)
    ·
      refine ⟨15966983085734043966472969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21289310780978725288630625 15966983085734043966472969)
      ·
        refine ⟨11975237314300532974854727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15966983085734043966472969 11975237314300532974854727)
        ·
          refine ⟨17962855971450799462282091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11975237314300532974854727 17962855971450799462282091)
          ·
            refine ⟨26944283957176199193423137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17962855971450799462282091 26944283957176199193423137)
            ·
              refine ⟨20208212967882149395067353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26944283957176199193423137 20208212967882149395067353)
              ·
                refine ⟨15156159725911612046300515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20208212967882149395067353 15156159725911612046300515)
                ·
                  refine ⟨22734239588867418069450773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15156159725911612046300515 22734239588867418069450773)
                  ·
                    refine ⟨1065667480728160222005505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22734239588867418069450773 1065667480728160222005505)
                    ·
                      rfl

theorem cell22_3113070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3113070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113070 prefixEnd_3113070 := by exact prefixLift 3113070
  have htrace : WordTrace (prefixWord ++ tailWord_3113070) baseStart_3113070 baseEnd_3113070 := by
    simpa [prefixWord, tailWord_3113070, baseEnd_3113070] using wordTrace_append hprefix tailTrace_3113070
  have hstable : (prefixWord ++ tailWord_3113070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113070).length < 2 ^ (prefixWord ++ tailWord_3113070).sum := by decide
  have hdescent : baseEnd_3113070 < baseStart_3113070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113072 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_3113072 : Nat := 118140960795 + 3113072 * 2 ^ 59
def prefixEnd_3113072 : Nat := 4983230072969 + 3 ^ 40 * 3113072 * 2
def baseEnd_3113072 : Nat := 1065668165369032883455499

theorem tailTrace_3113072 : CollatzResearch.WordTrace tailWord_3113072 prefixEnd_3113072 1065668165369032883455499 := by
  unfold tailWord_3113072
  simp only [CollatzResearch.WordTrace]
  refine ⟨56771531888939644607134735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75695375851919526142846313 56771531888939644607134735)
  ·
    refine ⟨85157297833409466910702103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56771531888939644607134735 85157297833409466910702103)
    ·
      refine ⟨127735946750114200366053155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85157297833409466910702103 127735946750114200366053155)
      ·
        refine ⟨191603920125171300549079733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127735946750114200366053155 191603920125171300549079733)
        ·
          refine ⟨17962867511734809426476225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191603920125171300549079733 17962867511734809426476225)
          ·
            refine ⟨13472150633801107069857169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17962867511734809426476225 13472150633801107069857169)
            ·
              refine ⟨10104112975350830302392877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13472150633801107069857169 10104112975350830302392877)
              ·
                refine ⟨3789042365756561363397329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10104112975350830302392877 3789042365756561363397329)
                ·
                  refine ⟨2841781774317421022547997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789042365756561363397329 2841781774317421022547997)
                  ·
                    refine ⟨1065668165369032883455499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841781774317421022547997 1065668165369032883455499)
                    ·
                      rfl

theorem cell22_3113072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_3113072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113072 prefixEnd_3113072 := by exact prefixLift 3113072
  have htrace : WordTrace (prefixWord ++ tailWord_3113072) baseStart_3113072 baseEnd_3113072 := by
    simpa [prefixWord, tailWord_3113072, baseEnd_3113072] using wordTrace_append hprefix tailTrace_3113072
  have hstable : (prefixWord ++ tailWord_3113072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113072).length < 2 ^ (prefixWord ++ tailWord_3113072).sum := by decide
  have hdescent : baseEnd_3113072 < baseStart_3113072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113117 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3113117 : Nat := 118140960795 + 3113117 * 2 ^ 59
def prefixEnd_3113117 : Nat := 4983230072969 + 3 ^ 40 * 3113117 * 2
def baseEnd_3113117 : Nat := 1065683569788667766080361

theorem tailTrace_3113117 : CollatzResearch.WordTrace tailWord_3113117 prefixEnd_3113117 1065683569788667766080361 := by
  unfold tailWord_3113117
  simp only [CollatzResearch.WordTrace]
  refine ⟨113544705062716261899657605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75696470041810841266438403 113544705062716261899657605)
  ·
    refine ⟨21289632199259299106185801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113544705062716261899657605 21289632199259299106185801)
    ·
      refine ⟨15967224149444474329639351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21289632199259299106185801 15967224149444474329639351)
      ·
        refine ⟨23950836224166711494459027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15967224149444474329639351 23950836224166711494459027)
        ·
          refine ⟨35926254336250067241688541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23950836224166711494459027 35926254336250067241688541)
          ·
            refine ⟨13472345376093775215633203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35926254336250067241688541 13472345376093775215633203)
            ·
              refine ⟨20208518064140662823449805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13472345376093775215633203 20208518064140662823449805)
              ·
                refine ⟨7578194274052748558793677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20208518064140662823449805 7578194274052748558793677)
                ·
                  refine ⟨2841822852769780709547629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7578194274052748558793677 2841822852769780709547629)
                  ·
                    refine ⟨1065683569788667766080361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841822852769780709547629 1065683569788667766080361)
                    ·
                      rfl

theorem cell22_3113117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3113117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113117 prefixEnd_3113117 := by exact prefixLift 3113117
  have htrace : WordTrace (prefixWord ++ tailWord_3113117) baseStart_3113117 baseEnd_3113117 := by
    simpa [prefixWord, tailWord_3113117, baseEnd_3113117] using wordTrace_append hprefix tailTrace_3113117
  have hstable : (prefixWord ++ tailWord_3113117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113117).length < 2 ^ (prefixWord ++ tailWord_3113117).sum := by decide
  have hdescent : baseEnd_3113117 < baseStart_3113117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113160 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3113160 : Nat := 118140960795 + 3113160 * 2 ^ 59
def prefixEnd_3113160 : Nat := 4983230072969 + 3 ^ 40 * 3113160 * 2
def baseEnd_3113160 : Nat := 1065698289567429987255229

theorem tailTrace_3113160 : CollatzResearch.WordTrace tailWord_3113160 prefixEnd_3113160 1065698289567429987255229 := by
  unfold tailWord_3113160
  simp only [CollatzResearch.WordTrace]
  refine ⟨56773136700780240121736467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75697515601040320162315289 56773136700780240121736467)
  ·
    refine ⟨85159705051170360182604701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56773136700780240121736467 85159705051170360182604701)
    ·
      refine ⟨31934889394188885068476763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85159705051170360182604701 31934889394188885068476763)
      ·
        refine ⟨47902334091283327602715145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31934889394188885068476763 47902334091283327602715145)
        ·
          refine ⟨35926750568462495702036359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47902334091283327602715145 35926750568462495702036359)
          ·
            refine ⟨53890125852693743553054539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35926750568462495702036359 53890125852693743553054539)
            ·
              refine ⟨80835188779040615329581809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53890125852693743553054539 80835188779040615329581809)
              ·
                refine ⟨60626391584280461497186357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80835188779040615329581809 60626391584280461497186357)
                ·
                  refine ⟨5683724211026293265361221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60626391584280461497186357 5683724211026293265361221)
                  ·
                    refine ⟨1065698289567429987255229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683724211026293265361221 1065698289567429987255229)
                    ·
                      rfl

theorem cell22_3113160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3113160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113160 prefixEnd_3113160 := by exact prefixLift 3113160
  have htrace : WordTrace (prefixWord ++ tailWord_3113160) baseStart_3113160 baseEnd_3113160 := by
    simpa [prefixWord, tailWord_3113160, baseEnd_3113160] using wordTrace_append hprefix tailTrace_3113160
  have hstable : (prefixWord ++ tailWord_3113160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113160).length < 2 ^ (prefixWord ++ tailWord_3113160).sum := by decide
  have hdescent : baseEnd_3113160 < baseStart_3113160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113181 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 5]
def baseStart_3113181 : Nat := 118140960795 + 3113181 * 2 ^ 59
def prefixEnd_3113181 : Nat := 4983230072969 + 3 ^ 40 * 3113181 * 2
def baseEnd_3113181 : Nat := 355235159432197644160055

theorem tailTrace_3113181 : CollatzResearch.WordTrace tailWord_3113181 prefixEnd_3113181 355235159432197644160055 := by
  unfold tailWord_3113181
  simp only [CollatzResearch.WordTrace]
  refine ⟨113547039334484400829987397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75698026222989600553324931 113547039334484400829987397)
  ·
    refine ⟨21290069875215825155622637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113547039334484400829987397 21290069875215825155622637)
    ·
      refine ⟨7983776203205934433358489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21290069875215825155622637 7983776203205934433358489)
      ·
        refine ⟨5987832152404450825018867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7983776203205934433358489 5987832152404450825018867)
        ·
          refine ⟨8981748228606676237528301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5987832152404450825018867 8981748228606676237528301)
          ·
            refine ⟨3368155585727503589073113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8981748228606676237528301 3368155585727503589073113)
            ·
              refine ⟨2526116689295627691804835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368155585727503589073113 2526116689295627691804835)
              ·
                refine ⟨3789175033943441537707253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526116689295627691804835 3789175033943441537707253)
                ·
                  refine ⟨355235159432197644160055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789175033943441537707253 355235159432197644160055)
                  ·
                    rfl

theorem cell22_3113181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_3113181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113181 prefixEnd_3113181 := by exact prefixLift 3113181
  have htrace : WordTrace (prefixWord ++ tailWord_3113181) baseStart_3113181 baseEnd_3113181 := by
    simpa [prefixWord, tailWord_3113181, baseEnd_3113181] using wordTrace_append hprefix tailTrace_3113181
  have hstable : (prefixWord ++ tailWord_3113181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113181).length < 2 ^ (prefixWord ++ tailWord_3113181).sum := by decide
  have hdescent : baseEnd_3113181 < baseStart_3113181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113220 : List Nat := [2, 3, 2, 2, 13]
def baseStart_3113220 : Nat := 118140960795 + 3113220 * 2 ^ 59
def prefixEnd_3113220 : Nat := 4983230072969 + 3 ^ 40 * 3113220 * 2
def baseEnd_3113220 : Nat := 4385674192566295599815

theorem tailTrace_3113220 : CollatzResearch.WordTrace tailWord_3113220 prefixEnd_3113220 4385674192566295599815 := by
  unfold tailWord_3113220
  simp only [CollatzResearch.WordTrace]
  refine ⟨56774230890671555245328557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75698974520895406993771409 56774230890671555245328557)
  ·
    refine ⟨21290336584001833216998209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56774230890671555245328557 21290336584001833216998209)
    ·
      refine ⟨15967752438001374912748657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21290336584001833216998209 15967752438001374912748657)
      ·
        refine ⟨11975814328501031184561493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15967752438001374912748657 11975814328501031184561493)
        ·
          refine ⟨4385674192566295599815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11975814328501031184561493 4385674192566295599815)
          ·
            rfl

theorem cell22_3113220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 13].length) (baseStart_3113220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113220 prefixEnd_3113220 := by exact prefixLift 3113220
  have htrace : WordTrace (prefixWord ++ tailWord_3113220) baseStart_3113220 baseEnd_3113220 := by
    simpa [prefixWord, tailWord_3113220, baseEnd_3113220] using wordTrace_append hprefix tailTrace_3113220
  have hstable : (prefixWord ++ tailWord_3113220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113220).length < 2 ^ (prefixWord ++ tailWord_3113220).sum := by decide
  have hdescent : baseEnd_3113220 < baseStart_3113220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113224 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_3113224 : Nat := 118140960795 + 3113224 * 2 ^ 59
def prefixEnd_3113224 : Nat := 4983230072969 + 3 ^ 40 * 3113224 * 2
def baseEnd_3113224 : Nat := 1065720198075355153655033

theorem tailTrace_3113224 : CollatzResearch.WordTrace tailWord_3113224 prefixEnd_3113224 1065720198075355153655033 := by
  unfold tailWord_3113224
  simp only [CollatzResearch.WordTrace]
  refine ⟨56774303836664309586901363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75699071782219079449201817 56774303836664309586901363)
  ·
    refine ⟨85161455754996464380352045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56774303836664309586901363 85161455754996464380352045)
    ·
      refine ⟨31935545908123674142632017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85161455754996464380352045 31935545908123674142632017)
      ·
        refine ⟨23951659431092755606974013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31935545908123674142632017 23951659431092755606974013)
        ·
          refine ⟨8981872286659783352615255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23951659431092755606974013 8981872286659783352615255)
          ·
            refine ⟨13472808429989675028922883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8981872286659783352615255 13472808429989675028922883)
            ·
              refine ⟨20209212644984512543384325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13472808429989675028922883 20209212644984512543384325)
              ·
                refine ⟨3789227370934596101884561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20209212644984512543384325 3789227370934596101884561)
                ·
                  refine ⟨2841920528200947076413421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789227370934596101884561 2841920528200947076413421)
                  ·
                    refine ⟨1065720198075355153655033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2841920528200947076413421 1065720198075355153655033)
                    ·
                      rfl

theorem cell22_3113224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_3113224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113224 prefixEnd_3113224 := by exact prefixLift 3113224
  have htrace : WordTrace (prefixWord ++ tailWord_3113224) baseStart_3113224 baseEnd_3113224 := by
    simpa [prefixWord, tailWord_3113224, baseEnd_3113224] using wordTrace_append hprefix tailTrace_3113224
  have hstable : (prefixWord ++ tailWord_3113224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113224).length < 2 ^ (prefixWord ++ tailWord_3113224).sum := by decide
  have hdescent : baseEnd_3113224 < baseStart_3113224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113256 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3113256 : Nat := 118140960795 + 3113256 * 2 ^ 59
def prefixEnd_3113256 : Nat := 4983230072969 + 3 ^ 40 * 3113256 * 2
def baseEnd_3113256 : Nat := 1065731152329317736854935

theorem tailTrace_3113256 : CollatzResearch.WordTrace tailWord_3113256 prefixEnd_3113256 1065731152329317736854935 := by
  unfold tailWord_3113256
  simp only [CollatzResearch.WordTrace]
  refine ⟨56774887404606344319483811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75699849872808459092645081 56774887404606344319483811)
  ·
    refine ⟨85162331106909516479225717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56774887404606344319483811 85162331106909516479225717)
    ·
      refine ⟨7983968541272767169927411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85162331106909516479225717 7983968541272767169927411)
      ·
        refine ⟨11975952811909150754891117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7983968541272767169927411 11975952811909150754891117)
        ·
          refine ⟨4490982304465931533084169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11975952811909150754891117 4490982304465931533084169)
          ·
            refine ⟨3368236728349448649813127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4490982304465931533084169 3368236728349448649813127)
            ·
              refine ⟨5052355092524172974719691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368236728349448649813127 5052355092524172974719691)
              ·
                refine ⟨7578532638786259462079537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5052355092524172974719691 7578532638786259462079537)
                ·
                  refine ⟨5683899479089694596559653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7578532638786259462079537 5683899479089694596559653)
                  ·
                    refine ⟨1065731152329317736854935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5683899479089694596559653 1065731152329317736854935)
                    ·
                      rfl

theorem cell22_3113256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3113256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113256 prefixEnd_3113256 := by exact prefixLift 3113256
  have htrace : WordTrace (prefixWord ++ tailWord_3113256) baseStart_3113256 baseEnd_3113256 := by
    simpa [prefixWord, tailWord_3113256, baseEnd_3113256] using wordTrace_append hprefix tailTrace_3113256
  have hstable : (prefixWord ++ tailWord_3113256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113256).length < 2 ^ (prefixWord ++ tailWord_3113256).sum := by decide
  have hdescent : baseEnd_3113256 < baseStart_3113256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113295 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3113295 : Nat := 118140960795 + 3113295 * 2 ^ 59
def prefixEnd_3113295 : Nat := 4983230072969 + 3 ^ 40 * 3113295 * 2
def baseEnd_3113295 : Nat := 1065744502826334635129815

theorem tailTrace_3113295 : CollatzResearch.WordTrace tailWord_3113295 prefixEnd_3113295 1065744502826334635129815 := by
  unfold tailWord_3113295
  simp only [CollatzResearch.WordTrace]
  refine ⟨113551197256071398299637339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75700798170714265533091559 113551197256071398299637339)
  ·
    refine ⟨170326795884107097449456009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113551197256071398299637339 170326795884107097449456009)
    ·
      refine ⟨127745096913080323087092007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170326795884107097449456009 127745096913080323087092007)
      ·
        refine ⟨191617645369620484630638011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127745096913080323087092007 191617645369620484630638011)
        ·
          refine ⟨287426468054430726945957017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191617645369620484630638011 287426468054430726945957017)
          ·
            refine ⟨215569851040823045209467763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287426468054430726945957017 215569851040823045209467763)
            ·
              refine ⟨323354776561234567814201645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215569851040823045209467763 323354776561234567814201645)
              ·
                refine ⟨121258041210462962930325617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323354776561234567814201645 121258041210462962930325617)
                ·
                  refine ⟨90943530907847222197744213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121258041210462962930325617 90943530907847222197744213)
                  ·
                    refine ⟨1065744502826334635129815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90943530907847222197744213 1065744502826334635129815)
                    ·
                      rfl

theorem cell22_3113295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3113295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113295 prefixEnd_3113295 := by exact prefixLift 3113295
  have htrace : WordTrace (prefixWord ++ tailWord_3113295) baseStart_3113295 baseEnd_3113295 := by
    simpa [prefixWord, tailWord_3113295, baseEnd_3113295] using wordTrace_append hprefix tailTrace_3113295
  have hstable : (prefixWord ++ tailWord_3113295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113295).length < 2 ^ (prefixWord ++ tailWord_3113295).sum := by decide
  have hdescent : baseEnd_3113295 < baseStart_3113295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113297 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3113297 : Nat := 118140960795 + 3113297 * 2 ^ 59
def prefixEnd_3113297 : Nat := 4983230072969 + 3 ^ 40 * 3113297 * 2
def baseEnd_3113297 : Nat := 1065745187467207296579809

theorem tailTrace_3113297 : CollatzResearch.WordTrace tailWord_3113297 prefixEnd_3113297 1065745187467207296579809 := by
  unfold tailWord_3113297
  simp only [CollatzResearch.WordTrace]
  refine ⟨113551270202064152641210145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75700846801376101760806763 113551270202064152641210145)
  ·
    refine ⟨85163452651548114480907609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113551270202064152641210145 85163452651548114480907609)
    ·
      refine ⟨63872589488661085860680707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85163452651548114480907609 63872589488661085860680707)
      ·
        refine ⟨95808884232991628791021061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63872589488661085860680707 95808884232991628791021061)
        ·
          refine ⟨17964165793685930398316449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95808884232991628791021061 17964165793685930398316449)
          ·
            refine ⟨13473124345264447798737337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17964165793685930398316449 13473124345264447798737337)
            ·
              refine ⟨10104843258948335849053003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13473124345264447798737337 10104843258948335849053003)
              ·
                refine ⟨15157264888422503773579505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10104843258948335849053003 15157264888422503773579505)
                ·
                  refine ⟨11367948666316877830184629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15157264888422503773579505 11367948666316877830184629)
                  ·
                    refine ⟨1065745187467207296579809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11367948666316877830184629 1065745187467207296579809)
                    ·
                      rfl

theorem cell22_3113297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3113297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113297 prefixEnd_3113297 := by exact prefixLift 3113297
  have htrace : WordTrace (prefixWord ++ tailWord_3113297) baseStart_3113297 baseEnd_3113297 := by
    simpa [prefixWord, tailWord_3113297, baseEnd_3113297] using wordTrace_append hprefix tailTrace_3113297
  have hstable : (prefixWord ++ tailWord_3113297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113297).length < 2 ^ (prefixWord ++ tailWord_3113297).sum := by decide
  have hdescent : baseEnd_3113297 < baseStart_3113297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113389 : List Nat := [1, 5, 2, 2, 2, 10]
def baseStart_3113389 : Nat := 118140960795 + 3113389 * 2 ^ 59
def prefixEnd_3113389 : Nat := 4983230072969 + 3 ^ 40 * 3113389 * 2
def baseEnd_3113389 : Nat := 13157736801819132386167

theorem tailTrace_3113389 : CollatzResearch.WordTrace tailWord_3113389 prefixEnd_3113389 13157736801819132386167 := by
  unfold tailWord_3113389
  simp only [CollatzResearch.WordTrace]
  refine ⟨113554625717730852353559221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75703083811820568235706147 113554625717730852353559221)
  ·
    refine ⟨10645746161037267408146177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113554625717730852353559221 10645746161037267408146177)
    ·
      refine ⟨7984309620777950556109633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10645746161037267408146177 7984309620777950556109633)
      ·
        refine ⟨5988232215583462917082225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7984309620777950556109633 5988232215583462917082225)
        ·
          refine ⟨4491174161687597187811669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5988232215583462917082225 4491174161687597187811669)
          ·
            refine ⟨13157736801819132386167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4491174161687597187811669 13157736801819132386167)
            ·
              rfl

theorem cell22_3113389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 10].length) (baseStart_3113389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113389 prefixEnd_3113389 := by exact prefixLift 3113389
  have htrace : WordTrace (prefixWord ++ tailWord_3113389) baseStart_3113389 baseEnd_3113389 := by
    simpa [prefixWord, tailWord_3113389, baseEnd_3113389] using wordTrace_append hprefix tailTrace_3113389
  have hstable : (prefixWord ++ tailWord_3113389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113389).length < 2 ^ (prefixWord ++ tailWord_3113389).sum := by decide
  have hdescent : baseEnd_3113389 < baseStart_3113389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113432 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3113432 : Nat := 118140960795 + 3113432 * 2 ^ 59
def prefixEnd_3113432 : Nat := 4983230072969 + 3 ^ 40 * 3113432 * 2
def baseEnd_3113432 : Nat := 1065791400726111944454395

theorem tailTrace_3113432 : CollatzResearch.WordTrace tailWord_3113432 prefixEnd_3113432 1065791400726111944454395 := by
  unfold tailWord_3113432
  simp only [CollatzResearch.WordTrace]
  refine ⟨56778097028287535348687275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75704129371050047131583033 56778097028287535348687275)
  ·
    refine ⟨85167145542431303023030913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56778097028287535348687275 85167145542431303023030913)
    ·
      refine ⟨63875359156823477267273185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85167145542431303023030913 63875359156823477267273185)
      ·
        refine ⟨47906519367617607950454889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63875359156823477267273185 47906519367617607950454889)
        ·
          refine ⟨35929889525713205962841167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47906519367617607950454889 35929889525713205962841167)
          ·
            refine ⟨53894834288569808944261751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35929889525713205962841167 53894834288569808944261751)
            ·
              refine ⟨80842251432854713416392627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53894834288569808944261751 80842251432854713416392627)
              ·
                refine ⟨121263377149282070124588941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80842251432854713416392627 121263377149282070124588941)
                ·
                  refine ⟨45473766430980776296720853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121263377149282070124588941 45473766430980776296720853)
                  ·
                    refine ⟨1065791400726111944454395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45473766430980776296720853 1065791400726111944454395)
                    ·
                      rfl

theorem cell22_3113432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3113432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113432 prefixEnd_3113432 := by exact prefixLift 3113432
  have htrace : WordTrace (prefixWord ++ tailWord_3113432) baseStart_3113432 baseEnd_3113432 := by
    simpa [prefixWord, tailWord_3113432, baseEnd_3113432] using wordTrace_append hprefix tailTrace_3113432
  have hstable : (prefixWord ++ tailWord_3113432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113432).length < 2 ^ (prefixWord ++ tailWord_3113432).sum := by decide
  have hdescent : baseEnd_3113432 < baseStart_3113432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113509 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_3113509 : Nat := 118140960795 + 3113509 * 2 ^ 59
def prefixEnd_3113509 : Nat := 4983230072969 + 3 ^ 40 * 3113509 * 2
def baseEnd_3113509 : Nat := 1065817759399709410279159

theorem tailTrace_3113509 : CollatzResearch.WordTrace tailWord_3113509 prefixEnd_3113509 1065817759399709410279159 := by
  unfold tailWord_3113509
  simp only [CollatzResearch.WordTrace]
  refine ⟨113559002477296112847927581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75706001651530741898618387 113559002477296112847927581)
  ·
    refine ⟨42584625928986042317972843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113559002477296112847927581 42584625928986042317972843)
    ·
      refine ⟨63876938893479063476959265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42584625928986042317972843 63876938893479063476959265)
      ·
        refine ⟨47907704170109297607719449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63876938893479063476959265 47907704170109297607719449)
        ·
          refine ⟨35930778127581973205789587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47907704170109297607719449 35930778127581973205789587)
          ·
            refine ⟨53896167191372959808684381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35930778127581973205789587 53896167191372959808684381)
            ·
              refine ⟨20211062696764859928256643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53896167191372959808684381 20211062696764859928256643)
              ·
                refine ⟨30316594045147289892384965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20211062696764859928256643 30316594045147289892384965)
                ·
                  refine ⟨5684361383465116854822181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30316594045147289892384965 5684361383465116854822181)
                  ·
                    refine ⟨1065817759399709410279159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5684361383465116854822181 1065817759399709410279159)
                    ·
                      rfl

theorem cell22_3113509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_3113509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113509 prefixEnd_3113509 := by exact prefixLift 3113509
  have htrace : WordTrace (prefixWord ++ tailWord_3113509) baseStart_3113509 baseEnd_3113509 := by
    simpa [prefixWord, tailWord_3113509, baseEnd_3113509] using wordTrace_append hprefix tailTrace_3113509
  have hstable : (prefixWord ++ tailWord_3113509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113509).length < 2 ^ (prefixWord ++ tailWord_3113509).sum := by decide
  have hdescent : baseEnd_3113509 < baseStart_3113509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113590 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_3113590 : Nat := 118140960795 + 3113590 * 2 ^ 59
def prefixEnd_3113590 : Nat := 4983230072969 + 3 ^ 40 * 3113590 * 2
def baseEnd_3113590 : Nat := 1065845487355052199003911

theorem tailTrace_3113590 : CollatzResearch.WordTrace tailWord_3113590 prefixEnd_3113590 1065845487355052199003911 := by
  unfold tailWord_3113590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097622299375166480101639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75707971193335109121084149 7097622299375166480101639)
  ·
    refine ⟨10646433449062749720152459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7097622299375166480101639 10646433449062749720152459)
    ·
      refine ⟨15969650173594124580228689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10646433449062749720152459 15969650173594124580228689)
      ·
        refine ⟨11977237630195593435171517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15969650173594124580228689 11977237630195593435171517)
        ·
          refine ⟨4491464111323347538189319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11977237630195593435171517 4491464111323347538189319)
          ·
            refine ⟨6737196166985021307283979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491464111323347538189319 6737196166985021307283979)
            ·
              refine ⟨10105794250477531960925969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737196166985021307283979 10105794250477531960925969)
              ·
                refine ⟨7579345687858148970694477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10105794250477531960925969 7579345687858148970694477)
                ·
                  refine ⟨2842254632946805864010429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7579345687858148970694477 2842254632946805864010429)
                  ·
                    refine ⟨1065845487355052199003911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842254632946805864010429 1065845487355052199003911)
                    ·
                      rfl

theorem cell22_3113590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_3113590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113590 prefixEnd_3113590 := by exact prefixLift 3113590
  have htrace : WordTrace (prefixWord ++ tailWord_3113590) baseStart_3113590 baseEnd_3113590 := by
    simpa [prefixWord, tailWord_3113590, baseEnd_3113590] using wordTrace_append hprefix tailTrace_3113590
  have hstable : (prefixWord ++ tailWord_3113590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113590).length < 2 ^ (prefixWord ++ tailWord_3113590).sum := by decide
  have hdescent : baseEnd_3113590 < baseStart_3113590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113620 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3113620 : Nat := 118140960795 + 3113620 * 2 ^ 59
def prefixEnd_3113620 : Nat := 4983230072969 + 3 ^ 40 * 3113620 * 2
def baseEnd_3113620 : Nat := 355285252322714040251273

theorem tailTrace_3113620 : CollatzResearch.WordTrace tailWord_3113620 prefixEnd_3113620 355285252322714040251273 := by
  unfold tailWord_3113620
  simp only [CollatzResearch.WordTrace]
  refine ⟨56781525489946989402609157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75708700653262652536812209 56781525489946989402609157)
  ·
    refine ⟨10646536029365060512989217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56781525489946989402609157 10646536029365060512989217)
    ·
      refine ⟨7984902022023795384741913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10646536029365060512989217 7984902022023795384741913)
      ·
        refine ⟨5988676516517846538556435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7984902022023795384741913 5988676516517846538556435)
        ·
          refine ⟨8983014774776769807834653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988676516517846538556435 8983014774776769807834653)
          ·
            refine ⟨3368630540541288677937995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8983014774776769807834653 3368630540541288677937995)
            ·
              refine ⟨5052945810811933016906993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368630540541288677937995 5052945810811933016906993)
              ·
                refine ⟨3789709358108949762680245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5052945810811933016906993 3789709358108949762680245)
                ·
                  refine ⟨355285252322714040251273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789709358108949762680245 355285252322714040251273)
                  ·
                    rfl

theorem cell22_3113620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3113620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113620 prefixEnd_3113620 := by exact prefixLift 3113620
  have htrace : WordTrace (prefixWord ++ tailWord_3113620) baseStart_3113620 baseEnd_3113620 := by
    simpa [prefixWord, tailWord_3113620, baseEnd_3113620] using wordTrace_append hprefix tailTrace_3113620
  have hstable : (prefixWord ++ tailWord_3113620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113620).length < 2 ^ (prefixWord ++ tailWord_3113620).sum := by decide
  have hdescent : baseEnd_3113620 < baseStart_3113620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113661 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3113661 : Nat := 118140960795 + 3113661 * 2 ^ 59
def prefixEnd_3113661 : Nat := 4983230072969 + 3 ^ 40 * 3113661 * 2
def baseEnd_3113661 : Nat := 1065869792106031680478693

theorem tailTrace_3113661 : CollatzResearch.WordTrace tailWord_3113661 prefixEnd_3113661 1065869792106031680478693 := by
  unfold tailWord_3113661
  simp only [CollatzResearch.WordTrace]
  refine ⟨113564546372745442807460837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75709697581830295204973891 113564546372745442807460837)
  ·
    refine ⟨21293352444889770526398907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113564546372745442807460837 21293352444889770526398907)
    ·
      refine ⟨31940028667334655789598361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293352444889770526398907 31940028667334655789598361)
      ·
        refine ⟨23955021500500991842198771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31940028667334655789598361 23955021500500991842198771)
        ·
          refine ⟨35932532250751487763298157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23955021500500991842198771 35932532250751487763298157)
          ·
            refine ⟨13474699594031807911236809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35932532250751487763298157 13474699594031807911236809)
            ·
              refine ⟨10106024695523855933427607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13474699594031807911236809 10106024695523855933427607)
              ·
                refine ⟨15159037043285783900141411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10106024695523855933427607 15159037043285783900141411)
                ·
                  refine ⟨22738555564928675850212117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15159037043285783900141411 22738555564928675850212117)
                  ·
                    refine ⟨1065869792106031680478693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22738555564928675850212117 1065869792106031680478693)
                    ·
                      rfl

theorem cell22_3113661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3113661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113661 prefixEnd_3113661 := by exact prefixLift 3113661
  have htrace : WordTrace (prefixWord ++ tailWord_3113661) baseStart_3113661 baseEnd_3113661 := by
    simpa [prefixWord, tailWord_3113661, baseEnd_3113661] using wordTrace_append hprefix tailTrace_3113661
  have hstable : (prefixWord ++ tailWord_3113661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113661).length < 2 ^ (prefixWord ++ tailWord_3113661).sum := by decide
  have hdescent : baseEnd_3113661 < baseStart_3113661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113676 : List Nat := [2, 2, 1, 5, 1, 1, 10]
def baseStart_3113676 : Nat := 118140960795 + 3113676 * 2 ^ 59
def prefixEnd_3113676 : Nat := 4983230072969 + 3 ^ 40 * 3113676 * 2
def baseEnd_3113676 : Nat := 39476849144910245976061

theorem tailTrace_3113676 : CollatzResearch.WordTrace tailWord_3113676 prefixEnd_3113676 39476849144910245976061 := by
  unfold tailWord_3113676
  simp only [CollatzResearch.WordTrace]
  refine ⟨56782546733845550184628441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75710062311794066912837921 56782546733845550184628441)
  ·
    refine ⟨42586910050384162638471331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56782546733845550184628441 42586910050384162638471331)
    ·
      refine ⟨63880365075576243957706997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42586910050384162638471331 63880365075576243957706997)
      ·
        refine ⟨5988784225835272871035031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63880365075576243957706997 5988784225835272871035031)
        ·
          refine ⟨8983176338752909306552547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5988784225835272871035031 8983176338752909306552547)
          ·
            refine ⟨13474764508129363959828821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8983176338752909306552547 13474764508129363959828821)
            ·
              refine ⟨39476849144910245976061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13474764508129363959828821 39476849144910245976061)
              ·
                rfl

theorem cell22_3113676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 10].length) (baseStart_3113676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113676 prefixEnd_3113676 := by exact prefixLift 3113676
  have htrace : WordTrace (prefixWord ++ tailWord_3113676) baseStart_3113676 baseEnd_3113676 := by
    simpa [prefixWord, tailWord_3113676, baseEnd_3113676] using wordTrace_append hprefix tailTrace_3113676
  have hstable : (prefixWord ++ tailWord_3113676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113676).length < 2 ^ (prefixWord ++ tailWord_3113676).sum := by decide
  have hdescent : baseEnd_3113676 < baseStart_3113676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113678 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3113678 : Nat := 118140960795 + 3113678 * 2 ^ 59
def prefixEnd_3113678 : Nat := 4983230072969 + 3 ^ 40 * 3113678 * 2
def baseEnd_3113678 : Nat := 1065875611553449302803641

theorem tailTrace_3113678 : CollatzResearch.WordTrace tailWord_3113678 prefixEnd_3113678 1065875611553449302803641 := by
  unfold tailWord_3113678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14195645801710481838853711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75710110942455903140553125 14195645801710481838853711)
  ·
    refine ⟨21293468702565722758280567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14195645801710481838853711 21293468702565722758280567)
    ·
      refine ⟨31940203053848584137420851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293468702565722758280567 31940203053848584137420851)
      ·
        refine ⟨47910304580772876206131277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31940203053848584137420851 47910304580772876206131277)
        ·
          refine ⟨17966364217789828577299229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47910304580772876206131277 17966364217789828577299229)
          ·
            refine ⟨6737386581671185716487211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17966364217789828577299229 6737386581671185716487211)
            ·
              refine ⟨10106079872506778574730817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737386581671185716487211 10106079872506778574730817)
              ·
                refine ⟨7579559904380083931048113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10106079872506778574730817 7579559904380083931048113)
                ·
                  refine ⟨5684669928285062948286085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7579559904380083931048113 5684669928285062948286085)
                  ·
                    refine ⟨1065875611553449302803641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5684669928285062948286085 1065875611553449302803641)
                    ·
                      rfl

theorem cell22_3113678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3113678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113678 prefixEnd_3113678 := by exact prefixLift 3113678
  have htrace : WordTrace (prefixWord ++ tailWord_3113678) baseStart_3113678 baseEnd_3113678 := by
    simpa [prefixWord, tailWord_3113678, baseEnd_3113678] using wordTrace_append hprefix tailTrace_3113678
  have hstable : (prefixWord ++ tailWord_3113678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113678).length < 2 ^ (prefixWord ++ tailWord_3113678).sum := by decide
  have hdescent : baseEnd_3113678 < baseStart_3113678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113682 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_3113682 : Nat := 118140960795 + 3113682 * 2 ^ 59
def prefixEnd_3113682 : Nat := 4983230072969 + 3 ^ 40 * 3113682 * 2
def baseEnd_3113682 : Nat := 355292326945064875234543

theorem tailTrace_3113682 : CollatzResearch.WordTrace tailWord_3113682 prefixEnd_3113682 355292326945064875234543 := by
  unfold tailWord_3113682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28391328076417340848493825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75710208203779575595983533 28391328076417340848493825)
  ·
    refine ⟨21293496057313005636370369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28391328076417340848493825 21293496057313005636370369)
    ·
      refine ⟨15970122042984754227277777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21293496057313005636370369 15970122042984754227277777)
      ·
        refine ⟨11977591532238565670458333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15970122042984754227277777 11977591532238565670458333)
        ·
          refine ⟨4491596824589462126421875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11977591532238565670458333 4491596824589462126421875)
          ·
            refine ⟨6737395236884193189632813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4491596824589462126421875 6737395236884193189632813)
            ·
              refine ⟨2526523213831572446112305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6737395236884193189632813 2526523213831572446112305)
              ·
                refine ⟨1894892410373679334584229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2526523213831572446112305 1894892410373679334584229)
                ·
                  refine ⟨355292326945064875234543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1894892410373679334584229 355292326945064875234543)
                  ·
                    rfl

theorem cell22_3113682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_3113682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113682 prefixEnd_3113682 := by exact prefixLift 3113682
  have htrace : WordTrace (prefixWord ++ tailWord_3113682) baseStart_3113682 baseEnd_3113682 := by
    simpa [prefixWord, tailWord_3113682, baseEnd_3113682] using wordTrace_append hprefix tailTrace_3113682
  have hstable : (prefixWord ++ tailWord_3113682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113682).length < 2 ^ (prefixWord ++ tailWord_3113682).sum := by decide
  have hdescent : baseEnd_3113682 < baseStart_3113682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113691 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 9, 3]
def baseStart_3113691 : Nat := 118140960795 + 3113691 * 2 ^ 59
def prefixEnd_3113691 : Nat := 4983230072969 + 3 ^ 40 * 3113691 * 2
def baseEnd_3113691 : Nat := 1065880061719121602228601

theorem tailTrace_3113691 : CollatzResearch.WordTrace tailWord_3113691 prefixEnd_3113691 1065880061719121602228601 := by
  unfold tailWord_3113691
  simp only [CollatzResearch.WordTrace]
  refine ⟨113565640562636757931052927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75710427041757838620701951 113565640562636757931052927)
  ·
    refine ⟨170348460843955136896579391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113565640562636757931052927 170348460843955136896579391)
    ·
      refine ⟨255522691265932705344869087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170348460843955136896579391 255522691265932705344869087)
      ·
        refine ⟨383284036898899058017303631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255522691265932705344869087 383284036898899058017303631)
        ·
          refine ⟨574926055348348587025955447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383284036898899058017303631 574926055348348587025955447)
          ·
            refine ⟨862389083022522880538933171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574926055348348587025955447 862389083022522880538933171)
            ·
              refine ⟨1293583624533784320808399757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862389083022522880538933171 1293583624533784320808399757)
              ·
                refine ⟨485093859200169120303149909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293583624533784320808399757 485093859200169120303149909)
                ·
                  refine ⟨2842346831250990939276269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 485093859200169120303149909 2842346831250990939276269)
                  ·
                    refine ⟨1065880061719121602228601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842346831250990939276269 1065880061719121602228601)
                    ·
                      rfl

theorem cell22_3113691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9, 3].length) (baseStart_3113691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113691 prefixEnd_3113691 := by exact prefixLift 3113691
  have htrace : WordTrace (prefixWord ++ tailWord_3113691) baseStart_3113691 baseEnd_3113691 := by
    simpa [prefixWord, tailWord_3113691, baseEnd_3113691] using wordTrace_append hprefix tailTrace_3113691
  have hstable : (prefixWord ++ tailWord_3113691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113691).length < 2 ^ (prefixWord ++ tailWord_3113691).sum := by decide
  have hdescent : baseEnd_3113691 < baseStart_3113691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113697 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3113697 : Nat := 118140960795 + 3113697 * 2 ^ 59
def prefixEnd_3113697 : Nat := 4983230072969 + 3 ^ 40 * 3113697 * 2
def baseEnd_3113697 : Nat := 1065882115641739586578583

theorem tailTrace_3113697 : CollatzResearch.WordTrace tailWord_3113697 prefixEnd_3113697 1065882115641739586578583 := by
  unfold tailWord_3113697
  simp only [CollatzResearch.WordTrace]
  refine ⟨113565859400615020955771345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75710572933743347303847563 113565859400615020955771345)
  ·
    refine ⟨85174394550461265716828509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113565859400615020955771345 85174394550461265716828509)
    ·
      refine ⟨31940397956422974643810691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85174394550461265716828509 31940397956422974643810691)
      ·
        refine ⟨47910596934634461965716037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31940397956422974643810691 47910596934634461965716037)
        ·
          refine ⟨8983236925243961618571757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47910596934634461965716037 8983236925243961618571757)
          ·
            refine ⟨3368713846966485606964409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8983236925243961618571757 3368713846966485606964409)
            ·
              refine ⟨2526535385224864205223307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368713846966485606964409 2526535385224864205223307)
              ·
                refine ⟨3789803077837296307834961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526535385224864205223307 3789803077837296307834961)
                ·
                  refine ⟨2842352308377972230876221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3789803077837296307834961 2842352308377972230876221)
                  ·
                    refine ⟨1065882115641739586578583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842352308377972230876221 1065882115641739586578583)
                    ·
                      rfl

theorem cell22_3113697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3113697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113697 prefixEnd_3113697 := by exact prefixLift 3113697
  have htrace : WordTrace (prefixWord ++ tailWord_3113697) baseStart_3113697 baseEnd_3113697 := by
    simpa [prefixWord, tailWord_3113697, baseEnd_3113697] using wordTrace_append hprefix tailTrace_3113697
  have hstable : (prefixWord ++ tailWord_3113697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113697).length < 2 ^ (prefixWord ++ tailWord_3113697).sum := by decide
  have hdescent : baseEnd_3113697 < baseStart_3113697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113725 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_3113725 : Nat := 118140960795 + 3113725 * 2 ^ 59
def prefixEnd_3113725 : Nat := 4983230072969 + 3 ^ 40 * 3113725 * 2
def baseEnd_3113725 : Nat := 1065891700613956846878497

theorem tailTrace_3113725 : CollatzResearch.WordTrace tailWord_3113725 prefixEnd_3113725 1065891700613956846878497 := by
  unfold tailWord_3113725
  simp only [CollatzResearch.WordTrace]
  refine ⟨113566880644513581737790629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75711253763009054491860419 113566880644513581737790629)
  ·
    refine ⟨21293790120846296575835743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113566880644513581737790629 21293790120846296575835743)
    ·
      refine ⟨31940685181269444863753615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21293790120846296575835743 31940685181269444863753615)
      ·
        refine ⟨47911027771904167295630423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31940685181269444863753615 47911027771904167295630423)
        ·
          refine ⟨71866541657856250943445635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47911027771904167295630423 71866541657856250943445635)
          ·
            refine ⟨107799812486784376415168453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71866541657856250943445635 107799812486784376415168453)
            ·
              refine ⟨20212464841272070577844085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107799812486784376415168453 20212464841272070577844085)
              ·
                refine ⟨1894918578869256616672883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20212464841272070577844085 1894918578869256616672883)
                ·
                  refine ⟨2842377868303884925009325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894918578869256616672883 2842377868303884925009325)
                  ·
                    refine ⟨1065891700613956846878497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842377868303884925009325 1065891700613956846878497)
                    ·
                      rfl

theorem cell22_3113725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_3113725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113725 prefixEnd_3113725 := by exact prefixLift 3113725
  have htrace : WordTrace (prefixWord ++ tailWord_3113725) baseStart_3113725 baseEnd_3113725 := by
    simpa [prefixWord, tailWord_3113725, baseEnd_3113725] using wordTrace_append hprefix tailTrace_3113725
  have hstable : (prefixWord ++ tailWord_3113725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113725).length < 2 ^ (prefixWord ++ tailWord_3113725).sum := by decide
  have hdescent : baseEnd_3113725 < baseStart_3113725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113738 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_3113738 : Nat := 118140960795 + 3113738 * 2 ^ 59
def prefixEnd_3113738 : Nat := 4983230072969 + 3 ^ 40 * 3113738 * 2
def baseEnd_3113738 : Nat := 355298716926543048767819

theorem tailTrace_3113738 : CollatzResearch.WordTrace tailWord_3113738 prefixEnd_3113738 355298716926543048767819 := by
  unfold tailWord_3113738
  simp only [CollatzResearch.WordTrace]
  refine ⟨28391838698366621239503467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75711569862310989972009245 28391838698366621239503467)
  ·
    refine ⟨42587758047549931859255201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28391838698366621239503467 42587758047549931859255201)
    ·
      refine ⟨31940818535662448894441401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42587758047549931859255201 31940818535662448894441401)
      ·
        refine ⟨23955613901746836670831051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31940818535662448894441401 23955613901746836670831051)
        ·
          refine ⟨35933420852620255006246577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23955613901746836670831051 35933420852620255006246577)
          ·
            refine ⟨26950065639465191254684933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35933420852620255006246577 26950065639465191254684933)
            ·
              refine ⟨5053137307399723360253425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26950065639465191254684933 5053137307399723360253425)
              ·
                refine ⟨3789852980549792520190069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053137307399723360253425 3789852980549792520190069)
                ·
                  refine ⟨355298716926543048767819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3789852980549792520190069 355298716926543048767819)
                  ·
                    rfl

theorem cell22_3113738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_3113738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113738 prefixEnd_3113738 := by exact prefixLift 3113738
  have htrace : WordTrace (prefixWord ++ tailWord_3113738) baseStart_3113738 baseEnd_3113738 := by
    simpa [prefixWord, tailWord_3113738, baseEnd_3113738] using wordTrace_append hprefix tailTrace_3113738
  have hstable : (prefixWord ++ tailWord_3113738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113738).length < 2 ^ (prefixWord ++ tailWord_3113738).sum := by decide
  have hdescent : baseEnd_3113738 < baseStart_3113738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113768 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3113768 : Nat := 118140960795 + 3113768 * 2 ^ 59
def prefixEnd_3113768 : Nat := 4983230072969 + 3 ^ 40 * 3113768 * 2
def baseEnd_3113768 : Nat := 1065906420392719068053365

theorem tailTrace_3113768 : CollatzResearch.WordTrace tailWord_3113768 prefixEnd_3113768 1065906420392719068053365 := by
  unfold tailWord_3113768
  simp only [CollatzResearch.WordTrace]
  refine ⟨56784224491678900040802979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75712299322238533387737305 56784224491678900040802979)
  ·
    refine ⟨85176336737518350061204469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56784224491678900040802979 85176336737518350061204469)
    ·
      refine ⟨7985281569142345318237919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85176336737518350061204469 7985281569142345318237919)
      ·
        refine ⟨11977922353713517977356879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7985281569142345318237919 11977922353713517977356879)
        ·
          refine ⟨17966883530570276966035319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11977922353713517977356879 17966883530570276966035319)
          ·
            refine ⟨26950325295855415449052979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17966883530570276966035319 26950325295855415449052979)
            ·
              refine ⟨40425487943783123173579469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26950325295855415449052979 40425487943783123173579469)
              ·
                refine ⟨15159557978918671190092301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40425487943783123173579469 15159557978918671190092301)
                ·
                  refine ⟨5684834242094501696284613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15159557978918671190092301 5684834242094501696284613)
                  ·
                    refine ⟨1065906420392719068053365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5684834242094501696284613 1065906420392719068053365)
                    ·
                      rfl

theorem cell22_3113768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3113768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113768 prefixEnd_3113768 := by exact prefixLift 3113768
  have htrace : WordTrace (prefixWord ++ tailWord_3113768) baseStart_3113768 baseEnd_3113768 := by
    simpa [prefixWord, tailWord_3113768, baseEnd_3113768] using wordTrace_append hprefix tailTrace_3113768
  have hstable : (prefixWord ++ tailWord_3113768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113768).length < 2 ^ (prefixWord ++ tailWord_3113768).sum := by decide
  have hdescent : baseEnd_3113768 < baseStart_3113768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113815 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 1, 5]
def baseStart_3113815 : Nat := 118140960795 + 3113815 * 2 ^ 59
def prefixEnd_3113815 : Nat := 4983230072969 + 3 ^ 40 * 3113815 * 2
def baseEnd_3113815 : Nat := 1065922509453226612128221

theorem tailTrace_3113815 : CollatzResearch.WordTrace tailWord_3113815 prefixEnd_3113815 1065922509453226612128221 := by
  unfold tailWord_3113815
  simp only [CollatzResearch.WordTrace]
  refine ⟨113570163214187527108566899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75713442142791684739044599 113570163214187527108566899)
  ·
    refine ⟨170355244821281290662850349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113570163214187527108566899 170355244821281290662850349)
    ·
      refine ⟨63883216807980483998568881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170355244821281290662850349 63883216807980483998568881)
      ·
        refine ⟨47912412605985362998926661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63883216807980483998568881 47912412605985362998926661)
        ·
          refine ⟨8983577363622255562298749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47912412605985362998926661 8983577363622255562298749)
          ·
            refine ⟨3368841511358345835862031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8983577363622255562298749 3368841511358345835862031)
            ·
              refine ⟨5053262267037518753793047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3368841511358345835862031 5053262267037518753793047)
              ·
                refine ⟨7579893400556278130689571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5053262267037518753793047 7579893400556278130689571)
                ·
                  refine ⟨11369840100834417196034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7579893400556278130689571 11369840100834417196034357)
                  ·
                    refine ⟨1065922509453226612128221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11369840100834417196034357 1065922509453226612128221)
                    ·
                      rfl

theorem cell22_3113815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_3113815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113815 prefixEnd_3113815 := by exact prefixLift 3113815
  have htrace : WordTrace (prefixWord ++ tailWord_3113815) baseStart_3113815 baseEnd_3113815 := by
    simpa [prefixWord, tailWord_3113815, baseEnd_3113815] using wordTrace_append hprefix tailTrace_3113815
  have hstable : (prefixWord ++ tailWord_3113815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113815).length < 2 ^ (prefixWord ++ tailWord_3113815).sum := by decide
  have hdescent : baseEnd_3113815 < baseStart_3113815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113828 : List Nat := [2, 3, 1, 1, 4, 2, 1, 8]
def baseStart_3113828 : Nat := 118140960795 + 3113828 * 2 ^ 59
def prefixEnd_3113828 : Nat := 4983230072969 + 3 ^ 40 * 3113828 * 2
def baseEnd_3113828 : Nat := 118436328846544323505909

theorem tailTrace_3113828 : CollatzResearch.WordTrace tailWord_3113828 prefixEnd_3113828 118436328846544323505909 := by
  unfold tailWord_3113828
  simp only [CollatzResearch.WordTrace]
  refine ⟨56785318681570215164395069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75713758242093620219193425 56785318681570215164395069)
  ·
    refine ⟨21294494505588830686648151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56785318681570215164395069 21294494505588830686648151)
    ·
      refine ⟨31941741758383246029972227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21294494505588830686648151 31941741758383246029972227)
      ·
        refine ⟨47912612637574869044958341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31941741758383246029972227 47912612637574869044958341)
        ·
          refine ⟨8983614869545287945929689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47912612637574869044958341 8983614869545287945929689)
          ·
            refine ⟨6737711152158965959447267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8983614869545287945929689 6737711152158965959447267)
            ·
              refine ⟨10106566728238448939170901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737711152158965959447267 10106566728238448939170901)
              ·
                refine ⟨118436328846544323505909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10106566728238448939170901 118436328846544323505909)
                ·
                  rfl

theorem cell22_3113828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_3113828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113828 prefixEnd_3113828 := by exact prefixLift 3113828
  have htrace : WordTrace (prefixWord ++ tailWord_3113828) baseStart_3113828 baseEnd_3113828 := by
    simpa [prefixWord, tailWord_3113828, baseEnd_3113828] using wordTrace_append hprefix tailTrace_3113828
  have hstable : (prefixWord ++ tailWord_3113828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113828).length < 2 ^ (prefixWord ++ tailWord_3113828).sum := by decide
  have hdescent : baseEnd_3113828 < baseStart_3113828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113843 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 5, 3]
def baseStart_3113843 : Nat := 118140960795 + 3113843 * 2 ^ 59
def prefixEnd_3113843 : Nat := 4983230072969 + 3 ^ 40 * 3113843 * 2
def baseEnd_3113843 : Nat := 1065932094425443872428135

theorem tailTrace_3113843 : CollatzResearch.WordTrace tailWord_3113843 prefixEnd_3113843 1065932094425443872428135 := by
  unfold tailWord_3113843
  simp only [CollatzResearch.WordTrace]
  refine ⟨113571184458086087890586183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75714122972057391927057455 113571184458086087890586183)
  ·
    refine ⟨170356776687129131835879275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113571184458086087890586183 170356776687129131835879275)
    ·
      refine ⟨255535165030693697753818913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170356776687129131835879275 255535165030693697753818913)
      ·
        refine ⟨191651373773020273315364185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255535165030693697753818913 191651373773020273315364185)
        ·
          refine ⟨143738530329765204986523139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191651373773020273315364185 143738530329765204986523139)
          ·
            refine ⟨215607795494647807479784709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143738530329765204986523139 215607795494647807479784709)
            ·
              refine ⟨40426461655246463902459633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215607795494647807479784709 40426461655246463902459633)
              ·
                refine ⟨30319846241434847926844725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40426461655246463902459633 30319846241434847926844725)
                ·
                  refine ⟨2842485585134516993141693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30319846241434847926844725 2842485585134516993141693)
                  ·
                    refine ⟨1065932094425443872428135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842485585134516993141693 1065932094425443872428135)
                    ·
                      rfl

theorem cell22_3113843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 3].length) (baseStart_3113843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113843 prefixEnd_3113843 := by exact prefixLift 3113843
  have htrace : WordTrace (prefixWord ++ tailWord_3113843) baseStart_3113843 baseEnd_3113843 := by
    simpa [prefixWord, tailWord_3113843, baseEnd_3113843] using wordTrace_append hprefix tailTrace_3113843
  have hstable : (prefixWord ++ tailWord_3113843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113843).length < 2 ^ (prefixWord ++ tailWord_3113843).sum := by decide
  have hdescent : baseEnd_3113843 < baseStart_3113843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113954 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3113954 : Nat := 118140960795 + 3113954 * 2 ^ 59
def prefixEnd_3113954 : Nat := 4983230072969 + 3 ^ 40 * 3113954 * 2
def baseEnd_3113954 : Nat := 1065970091993876582902795

theorem tailTrace_3113954 : CollatzResearch.WordTrace tailWord_3113954 prefixEnd_3113954 1065970091993876582902795 := by
  unfold tailWord_3113954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393808240170988461969229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75716821973789302565251277 28393808240170988461969229)
  ·
    refine ⟨10647678090064120673238461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28393808240170988461969229 10647678090064120673238461)
    ·
      refine ⟨3992879283774045252464423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10647678090064120673238461 3992879283774045252464423)
      ·
        refine ⟨5989318925661067878696635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3992879283774045252464423 5989318925661067878696635)
        ·
          refine ⟨8983978388491601818044953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989318925661067878696635 8983978388491601818044953)
          ·
            refine ⟨6737983791368701363533715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8983978388491601818044953 6737983791368701363533715)
            ·
              refine ⟨10106975687053052045300573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6737983791368701363533715 10106975687053052045300573)
              ·
                refine ⟨3790115882644894516987715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10106975687053052045300573 3790115882644894516987715)
                ·
                  refine ⟨5685173823967341775481573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790115882644894516987715 5685173823967341775481573)
                  ·
                    refine ⟨1065970091993876582902795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5685173823967341775481573 1065970091993876582902795)
                    ·
                      rfl

theorem cell22_3113954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3113954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113954 prefixEnd_3113954 := by exact prefixLift 3113954
  have htrace : WordTrace (prefixWord ++ tailWord_3113954) baseStart_3113954 baseEnd_3113954 := by
    simpa [prefixWord, tailWord_3113954, baseEnd_3113954] using wordTrace_append hprefix tailTrace_3113954
  have hstable : (prefixWord ++ tailWord_3113954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113954).length < 2 ^ (prefixWord ++ tailWord_3113954).sum := by decide
  have hdescent : baseEnd_3113954 < baseStart_3113954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113967 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 2, 3]
def baseStart_3113967 : Nat := 118140960795 + 3113967 * 2 ^ 59
def prefixEnd_3113967 : Nat := 4983230072969 + 3 ^ 40 * 3113967 * 2
def baseEnd_3113967 : Nat := 1065974542159548882327755

theorem tailTrace_3113967 : CollatzResearch.WordTrace tailWord_3113967 prefixEnd_3113967 1065974542159548882327755 := by
  unfold tailWord_3113967
  simp only [CollatzResearch.WordTrace]
  refine ⟨113575707109636857068100155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75717138073091238045400103 113575707109636857068100155)
  ·
    refine ⟨170363560664455285602150233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113575707109636857068100155 170363560664455285602150233)
    ·
      refine ⟨127772670498341464201612675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170363560664455285602150233 127772670498341464201612675)
      ·
        refine ⟨191659005747512196302419013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127772670498341464201612675 191659005747512196302419013)
        ·
          refine ⟨35936063577658536806703565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191659005747512196302419013 35936063577658536806703565)
          ·
            refine ⟨13476023841621951302513837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35936063577658536806703565 13476023841621951302513837)
            ·
              refine ⟨5053508940608231738442689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13476023841621951302513837 5053508940608231738442689)
              ·
                refine ⟨3790131705456173803832017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053508940608231738442689 3790131705456173803832017)
                ·
                  refine ⟨2842598779092130352874013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3790131705456173803832017 2842598779092130352874013)
                  ·
                    refine ⟨1065974542159548882327755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842598779092130352874013 1065974542159548882327755)
                    ·
                      rfl

theorem cell22_3113967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_3113967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113967 prefixEnd_3113967 := by exact prefixLift 3113967
  have htrace : WordTrace (prefixWord ++ tailWord_3113967) baseStart_3113967 baseEnd_3113967 := by
    simpa [prefixWord, tailWord_3113967, baseEnd_3113967] using wordTrace_append hprefix tailTrace_3113967
  have hstable : (prefixWord ++ tailWord_3113967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113967).length < 2 ^ (prefixWord ++ tailWord_3113967).sum := by decide
  have hdescent : baseEnd_3113967 < baseStart_3113967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3113993 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_3113993 : Nat := 118140960795 + 3113993 * 2 ^ 59
def prefixEnd_3113993 : Nat := 4983230072969 + 3 ^ 40 * 3113993 * 2
def baseEnd_3113993 : Nat := 1065983442490893481177675

theorem tailTrace_3113993 : CollatzResearch.WordTrace tailWord_3113993 prefixEnd_3113993 1065983442490893481177675 := by
  unfold tailWord_3113993
  simp only [CollatzResearch.WordTrace]
  refine ⟨113576655407542663508546633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75717770271695109005697755 113576655407542663508546633)
  ·
    refine ⟨85182491555656997631409975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113576655407542663508546633 85182491555656997631409975)
    ·
      refine ⟨127773737333485496447114963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85182491555656997631409975 127773737333485496447114963)
      ·
        refine ⟨191660606000228244670672445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127773737333485496447114963 191660606000228244670672445)
        ·
          refine ⟨71872727250085591751502167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191660606000228244670672445 71872727250085591751502167)
          ·
            refine ⟨107809090875128387627253251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71872727250085591751502167 107809090875128387627253251)
            ·
              refine ⟨161713636312692581440879877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107809090875128387627253251 161713636312692581440879877)
              ·
                refine ⟨30321306808629859020164977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161713636312692581440879877 30321306808629859020164977)
                ·
                  refine ⟨22740980106472394265123733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30321306808629859020164977 22740980106472394265123733)
                  ·
                    refine ⟨1065983442490893481177675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22740980106472394265123733 1065983442490893481177675)
                    ·
                      rfl

theorem cell22_3113993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_3113993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3113993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3113993 prefixEnd_3113993 := by exact prefixLift 3113993
  have htrace : WordTrace (prefixWord ++ tailWord_3113993) baseStart_3113993 baseEnd_3113993 := by
    simpa [prefixWord, tailWord_3113993, baseEnd_3113993] using wordTrace_append hprefix tailTrace_3113993
  have hstable : (prefixWord ++ tailWord_3113993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3113993).length < 2 ^ (prefixWord ++ tailWord_3113993).sum := by decide
  have hdescent : baseEnd_3113993 < baseStart_3113993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3113993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114042 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_3114042 : Nat := 118140960795 + 3114042 * 2 ^ 59
def prefixEnd_3114042 : Nat := 4983230072969 + 3 ^ 40 * 3114042 * 2
def baseEnd_3114042 : Nat := 355333405397424562234175

theorem tailTrace_3114042 : CollatzResearch.WordTrace tailWord_3114042 prefixEnd_3114042 355333405397424562234175 := by
  unfold tailWord_3114042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28394610646091286219270095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75718961722910096584720253 28394610646091286219270095)
  ·
    refine ⟨42591915969136929328905143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28394610646091286219270095 42591915969136929328905143)
    ·
      refine ⟨63887873953705393993357715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42591915969136929328905143 63887873953705393993357715)
      ·
        refine ⟨95831810930558090990036573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63887873953705393993357715 95831810930558090990036573)
        ·
          refine ⟨35936929098959284121263715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95831810930558090990036573 35936929098959284121263715)
          ·
            refine ⟨53905393648438926181895573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35936929098959284121263715 53905393648438926181895573)
            ·
              refine ⟨2526815327270574664776355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53905393648438926181895573 2526815327270574664776355)
              ·
                refine ⟨3790222990905861997164533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526815327270574664776355 3790222990905861997164533)
                ·
                  refine ⟨355333405397424562234175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3790222990905861997164533 355333405397424562234175)
                  ·
                    rfl

theorem cell22_3114042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_3114042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114042 prefixEnd_3114042 := by exact prefixLift 3114042
  have htrace : WordTrace (prefixWord ++ tailWord_3114042) baseStart_3114042 baseEnd_3114042 := by
    simpa [prefixWord, tailWord_3114042, baseEnd_3114042] using wordTrace_append hprefix tailTrace_3114042
  have hstable : (prefixWord ++ tailWord_3114042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114042).length < 2 ^ (prefixWord ++ tailWord_3114042).sum := by decide
  have hdescent : baseEnd_3114042 < baseStart_3114042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114085 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_3114085 : Nat := 118140960795 + 3114085 * 2 ^ 59
def prefixEnd_3114085 : Nat := 4983230072969 + 3 ^ 40 * 3114085 * 2
def baseEnd_3114085 : Nat := 1066014935971035907877393

theorem tailTrace_3114085 : CollatzResearch.WordTrace tailWord_3114085 prefixEnd_3114085 1066014935971035907877393 := by
  unfold tailWord_3114085
  simp only [CollatzResearch.WordTrace]
  refine ⟨113580010923209363220895709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75720007282139575480597139 113580010923209363220895709)
  ·
    refine ⟨42592504096203511207835891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113580010923209363220895709 42592504096203511207835891)
    ·
      refine ⟨63888756144305266811753837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42592504096203511207835891 63888756144305266811753837)
      ·
        refine ⟨23958283554114475054407689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63888756144305266811753837 23958283554114475054407689)
        ·
          refine ⟨17968712665585856290805767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23958283554114475054407689 17968712665585856290805767)
          ·
            refine ⟨26953068998378784436208651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17968712665585856290805767 26953068998378784436208651)
            ·
              refine ⟨40429603497568176654312977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26953068998378784436208651 40429603497568176654312977)
              ·
                refine ⟨30322202623176132490734733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40429603497568176654312977 30322202623176132490734733)
                ·
                  refine ⟨11370825983691049684025525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30322202623176132490734733 11370825983691049684025525)
                  ·
                    refine ⟨1066014935971035907877393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11370825983691049684025525 1066014935971035907877393)
                    ·
                      rfl

theorem cell22_3114085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_3114085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114085 prefixEnd_3114085 := by exact prefixLift 3114085
  have htrace : WordTrace (prefixWord ++ tailWord_3114085) baseStart_3114085 baseEnd_3114085 := by
    simpa [prefixWord, tailWord_3114085, baseEnd_3114085] using wordTrace_append hprefix tailTrace_3114085
  have hstable : (prefixWord ++ tailWord_3114085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114085).length < 2 ^ (prefixWord ++ tailWord_3114085).sum := by decide
  have hdescent : baseEnd_3114085 < baseStart_3114085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114117 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_3114117 : Nat := 118140960795 + 3114117 * 2 ^ 59
def prefixEnd_3114117 : Nat := 4983230072969 + 3 ^ 40 * 3114117 * 2
def baseEnd_3114117 : Nat := 1066025890224998491077295

theorem tailTrace_3114117 : CollatzResearch.WordTrace tailWord_3114117 prefixEnd_3114117 1066025890224998491077295 := by
  unfold tailWord_3114117
  simp only [CollatzResearch.WordTrace]
  refine ⟨113581178059093432686060605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75720785372728955124040403 113581178059093432686060605)
  ·
    refine ⟨42592941772160037257272727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113581178059093432686060605 42592941772160037257272727)
    ·
      refine ⟨63889412658240055885909091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42592941772160037257272727 63889412658240055885909091)
      ·
        refine ⟨95834118987360083828863637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63889412658240055885909091 95834118987360083828863637)
        ·
          refine ⟨4492224327532503929477983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95834118987360083828863637 4492224327532503929477983)
          ·
            refine ⟨6738336491298755894216975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492224327532503929477983 6738336491298755894216975)
            ·
              refine ⟨10107504736948133841325463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738336491298755894216975 10107504736948133841325463)
              ·
                refine ⟨15161257105422200761988195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10107504736948133841325463 15161257105422200761988195)
                ·
                  refine ⟨22741885658133301142982293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15161257105422200761988195 22741885658133301142982293)
                  ·
                    refine ⟨1066025890224998491077295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22741885658133301142982293 1066025890224998491077295)
                    ·
                      rfl

theorem cell22_3114117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_3114117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114117 prefixEnd_3114117 := by exact prefixLift 3114117
  have htrace : WordTrace (prefixWord ++ tailWord_3114117) baseStart_3114117 baseEnd_3114117 := by
    simpa [prefixWord, tailWord_3114117, baseEnd_3114117] using wordTrace_append hprefix tailTrace_3114117
  have hstable : (prefixWord ++ tailWord_3114117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114117).length < 2 ^ (prefixWord ++ tailWord_3114117).sum := by decide
  have hdescent : baseEnd_3114117 < baseStart_3114117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114136 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_3114136 : Nat := 118140960795 + 3114136 * 2 ^ 59
def prefixEnd_3114136 : Nat := 4983230072969 + 3 ^ 40 * 3114136 * 2
def baseEnd_3114136 : Nat := 1066032394313288774852237

theorem tailTrace_3114136 : CollatzResearch.WordTrace tailWord_3114136 prefixEnd_3114136 1066032394313288774852237 := by
  unfold tailWord_3114136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56790935523012299465501131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75721247364016399287334841 56790935523012299465501131)
  ·
    refine ⟨85186403284518449198251697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56790935523012299465501131 85186403284518449198251697)
    ·
      refine ⟨63889802463388836898688773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85186403284518449198251697 63889802463388836898688773)
      ·
        refine ⟨11979337961885406918504145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63889802463388836898688773 11979337961885406918504145)
        ·
          refine ⟨8984503471414055188878109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11979337961885406918504145 8984503471414055188878109)
          ·
            refine ⟨3369188801780270695829291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8984503471414055188878109 3369188801780270695829291)
            ·
              refine ⟨5053783202670406043743937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369188801780270695829291 5053783202670406043743937)
              ·
                refine ⟨3790337402002804532807953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053783202670406043743937 3790337402002804532807953)
                ·
                  refine ⟨2842753051502103399605965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3790337402002804532807953 2842753051502103399605965)
                  ·
                    refine ⟨1066032394313288774852237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842753051502103399605965 1066032394313288774852237)
                    ·
                      rfl

theorem cell22_3114136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_3114136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114136 prefixEnd_3114136 := by exact prefixLift 3114136
  have htrace : WordTrace (prefixWord ++ tailWord_3114136) baseStart_3114136 baseEnd_3114136 := by
    simpa [prefixWord, tailWord_3114136, baseEnd_3114136] using wordTrace_append hprefix tailTrace_3114136
  have hstable : (prefixWord ++ tailWord_3114136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114136).length < 2 ^ (prefixWord ++ tailWord_3114136).sum := by decide
  have hdescent : baseEnd_3114136 < baseStart_3114136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114166 : List Nat := [5, 1, 3, 2, 1, 1, 1, 8]
def baseStart_3114166 : Nat := 118140960795 + 3114166 * 2 ^ 59
def prefixEnd_3114166 : Nat := 4983230072969 + 3 ^ 40 * 3114166 * 2
def baseEnd_3114166 : Nat := 118449184880708744066905

theorem tailTrace_3114166 : CollatzResearch.WordTrace tailWord_3114166 prefixEnd_3114166 118449184880708744066905 := by
  unfold tailWord_3114166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7098935327244744628412147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75721976823943942703062901 7098935327244744628412147)
  ·
    refine ⟨10648402990867116942618221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7098935327244744628412147 10648402990867116942618221)
    ·
      refine ⟨3993151121575168853481833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10648402990867116942618221 3993151121575168853481833)
      ·
        refine ⟨2994863341181376640111375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3993151121575168853481833 2994863341181376640111375)
        ·
          refine ⟨4492295011772064960167063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994863341181376640111375 4492295011772064960167063)
          ·
            refine ⟨6738442517658097440250595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4492295011772064960167063 6738442517658097440250595)
            ·
              refine ⟨10107663776487146160375893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738442517658097440250595 10107663776487146160375893)
              ·
                refine ⟨118449184880708744066905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10107663776487146160375893 118449184880708744066905)
                ·
                  rfl

theorem cell22_3114166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_3114166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114166 prefixEnd_3114166 := by exact prefixLift 3114166
  have htrace : WordTrace (prefixWord ++ tailWord_3114166) baseStart_3114166 baseEnd_3114166 := by
    simpa [prefixWord, tailWord_3114166, baseEnd_3114166] using wordTrace_append hprefix tailTrace_3114166
  have hstable : (prefixWord ++ tailWord_3114166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114166).length < 2 ^ (prefixWord ++ tailWord_3114166).sum := by decide
  have hdescent : baseEnd_3114166 < baseStart_3114166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114175 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3114175 : Nat := 118140960795 + 3114175 * 2 ^ 59
def prefixEnd_3114175 : Nat := 4983230072969 + 3 ^ 40 * 3114175 * 2
def baseEnd_3114175 : Nat := 1066045744810305673127117

theorem tailTrace_3114175 : CollatzResearch.WordTrace tailWord_3114175 prefixEnd_3114175 1066045744810305673127117 := by
  unfold tailWord_3114175
  simp only [CollatzResearch.WordTrace]
  refine ⟨113583293492883308591671979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75722195661922205727781319 113583293492883308591671979)
  ·
    refine ⟨170374940239324962887507969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113583293492883308591671979 170374940239324962887507969)
    ·
      refine ⟨127781205179493722165630977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170374940239324962887507969 127781205179493722165630977)
      ·
        refine ⟨95835903884620291624223233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127781205179493722165630977 95835903884620291624223233)
        ·
          refine ⟨71876927913465218718167425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95835903884620291624223233 71876927913465218718167425)
          ·
            refine ⟨53907695935098914038625569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71876927913465218718167425 53907695935098914038625569)
            ·
              refine ⟨40430771951324185528969177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53907695935098914038625569 40430771951324185528969177)
              ·
                refine ⟨30323078963493139146726883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40430771951324185528969177 30323078963493139146726883)
                ·
                  refine ⟨45484618445239708720090325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30323078963493139146726883 45484618445239708720090325)
                  ·
                    refine ⟨1066045744810305673127117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45484618445239708720090325 1066045744810305673127117)
                    ·
                      rfl

theorem cell22_3114175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3114175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114175 prefixEnd_3114175 := by exact prefixLift 3114175
  have htrace : WordTrace (prefixWord ++ tailWord_3114175) baseStart_3114175 baseEnd_3114175 := by
    simpa [prefixWord, tailWord_3114175, baseEnd_3114175] using wordTrace_append hprefix tailTrace_3114175
  have hstable : (prefixWord ++ tailWord_3114175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114175).length < 2 ^ (prefixWord ++ tailWord_3114175).sum := by decide
  have hdescent : baseEnd_3114175 < baseStart_3114175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114222 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_3114222 : Nat := 118140960795 + 3114222 * 2 ^ 59
def prefixEnd_3114222 : Nat := 4983230072969 + 3 ^ 40 * 3114222 * 2
def baseEnd_3114222 : Nat := 355353944623604405733991

theorem tailTrace_3114222 : CollatzResearch.WordTrace tailWord_3114222 prefixEnd_3114222 355353944623604405733991 := by
  unfold tailWord_3114222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198125965464129452329115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75723338482475357079088613 14198125965464129452329115)
  ·
    refine ⟨21297188948196194178493673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14198125965464129452329115 21297188948196194178493673)
    ·
      refine ⟨15972891711147145633870255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21297188948196194178493673 15972891711147145633870255)
      ·
        refine ⟨23959337566720718450805383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15972891711147145633870255 23959337566720718450805383)
        ·
          refine ⟨35939006350081077676208075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23959337566720718450805383 35939006350081077676208075)
          ·
            refine ⟨53908509525121616514312113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35939006350081077676208075 53908509525121616514312113)
            ·
              refine ⟨40431382143841212385734085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53908509525121616514312113 40431382143841212385734085)
              ·
                refine ⟨7580884151970227322325141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40431382143841212385734085 7580884151970227322325141)
                ·
                  refine ⟨355353944623604405733991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7580884151970227322325141 355353944623604405733991)
                  ·
                    rfl

theorem cell22_3114222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_3114222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114222 prefixEnd_3114222 := by exact prefixLift 3114222
  have htrace : WordTrace (prefixWord ++ tailWord_3114222) baseStart_3114222 baseEnd_3114222 := by
    simpa [prefixWord, tailWord_3114222, baseEnd_3114222] using wordTrace_append hprefix tailTrace_3114222
  have hstable : (prefixWord ++ tailWord_3114222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114222).length < 2 ^ (prefixWord ++ tailWord_3114222).sum := by decide
  have hdescent : baseEnd_3114222 < baseStart_3114222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114241 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3114241 : Nat := 118140960795 + 3114241 * 2 ^ 59
def prefixEnd_3114241 : Nat := 4983230072969 + 3 ^ 40 * 3114241 * 2
def baseEnd_3114241 : Nat := 1066068337959103500976915

theorem tailTrace_3114241 : CollatzResearch.WordTrace tailWord_3114241 prefixEnd_3114241 1066068337959103500976915 := by
  unfold tailWord_3114241
  simp only [CollatzResearch.WordTrace]
  refine ⟨113585700710644201863574577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75723800473762801242383051 113585700710644201863574577)
  ·
    refine ⟨85189275532983151397680933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113585700710644201863574577 85189275532983151397680933)
    ·
      refine ⟨15972989162434340887065175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85189275532983151397680933 15972989162434340887065175)
      ·
        refine ⟨23959483743651511330597763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15972989162434340887065175 23959483743651511330597763)
        ·
          refine ⟨35939225615477266995896645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23959483743651511330597763 35939225615477266995896645)
          ·
            refine ⟨6738604802901987561730621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35939225615477266995896645 6738604802901987561730621)
            ·
              refine ⟨2526976801088245335648983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6738604802901987561730621 2526976801088245335648983)
              ·
                refine ⟨3790465201632368003473475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526976801088245335648983 3790465201632368003473475)
                ·
                  refine ⟨5685697802448552005210213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790465201632368003473475 5685697802448552005210213)
                  ·
                    refine ⟨1066068337959103500976915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5685697802448552005210213 1066068337959103500976915)
                    ·
                      rfl

theorem cell22_3114241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3114241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114241 prefixEnd_3114241 := by exact prefixLift 3114241
  have htrace : WordTrace (prefixWord ++ tailWord_3114241) baseStart_3114241 baseEnd_3114241 := by
    simpa [prefixWord, tailWord_3114241, baseEnd_3114241] using wordTrace_append hprefix tailTrace_3114241
  have hstable : (prefixWord ++ tailWord_3114241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114241).length < 2 ^ (prefixWord ++ tailWord_3114241).sum := by decide
  have hdescent : baseEnd_3114241 < baseStart_3114241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114316 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_3114316 : Nat := 118140960795 + 3114316 * 2 ^ 59
def prefixEnd_3114316 : Nat := 4983230072969 + 3 ^ 40 * 3114316 * 2
def baseEnd_3114316 : Nat := 1066094011991828305351685

theorem tailTrace_3114316 : CollatzResearch.WordTrace tailWord_3114316 prefixEnd_3114316 1066094011991828305351685 := by
  unfold tailWord_3114316
  simp only [CollatzResearch.WordTrace]
  refine ⟨56794218092686244836277401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75725624123581659781703201 56794218092686244836277401)
  ·
    refine ⟨42595663569514683627208051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56794218092686244836277401 42595663569514683627208051)
    ·
      refine ⟨63893495354272025440812077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42595663569514683627208051 63893495354272025440812077)
      ·
        refine ⟨23960060757852009540304529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63893495354272025440812077 23960060757852009540304529)
        ·
          refine ⟨17970045568389007155228397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23960060757852009540304529 17970045568389007155228397)
          ·
            refine ⟨6738767088145877683210649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17970045568389007155228397 6738767088145877683210649)
            ·
              refine ⟨5054075316109408262407987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6738767088145877683210649 5054075316109408262407987)
              ·
                refine ⟨7581112974164112393611981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054075316109408262407987 7581112974164112393611981)
                ·
                  refine ⟨2842917365311542147604493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7581112974164112393611981 2842917365311542147604493)
                  ·
                    refine ⟨1066094011991828305351685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842917365311542147604493 1066094011991828305351685)
                    ·
                      rfl

theorem cell22_3114316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_3114316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114316 prefixEnd_3114316 := by exact prefixLift 3114316
  have htrace : WordTrace (prefixWord ++ tailWord_3114316) baseStart_3114316 baseEnd_3114316 := by
    simpa [prefixWord, tailWord_3114316, baseEnd_3114316] using wordTrace_append hprefix tailTrace_3114316
  have hstable : (prefixWord ++ tailWord_3114316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114316).length < 2 ^ (prefixWord ++ tailWord_3114316).sum := by decide
  have hdescent : baseEnd_3114316 < baseStart_3114316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114359 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 1, 4]
def baseStart_3114359 : Nat := 118140960795 + 3114359 * 2 ^ 59
def prefixEnd_3114359 : Nat := 4983230072969 + 3 ^ 40 * 3114359 * 2
def baseEnd_3114359 : Nat := 1066108731770590526526553

theorem tailTrace_3114359 : CollatzResearch.WordTrace tailWord_3114359 prefixEnd_3114359 1066108731770590526526553 := by
  unfold tailWord_3114359
  simp only [CollatzResearch.WordTrace]
  refine ⟨113590004524216708016370131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75726669682811138677580087 113590004524216708016370131)
  ·
    refine ⟨170385006786325062024555197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113590004524216708016370131 170385006786325062024555197)
    ·
      refine ⟨63894377544871898259208199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170385006786325062024555197 63894377544871898259208199)
      ·
        refine ⟨95841566317307847388812299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63894377544871898259208199 95841566317307847388812299)
        ·
          refine ⟨143762349475961771083218449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95841566317307847388812299 143762349475961771083218449)
          ·
            refine ⟨107821762106971328312413837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143762349475961771083218449 107821762106971328312413837)
            ·
              refine ⟨40433160790114248117155189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107821762106971328312413837 40433160790114248117155189)
              ·
                refine ⟨3790608824073210760983299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40433160790114248117155189 3790608824073210760983299)
                ·
                  refine ⟨5685913236109816141474949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790608824073210760983299 5685913236109816141474949)
                  ·
                    refine ⟨1066108731770590526526553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5685913236109816141474949 1066108731770590526526553)
                    ·
                      rfl

theorem cell22_3114359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_3114359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114359 prefixEnd_3114359 := by exact prefixLift 3114359
  have htrace : WordTrace (prefixWord ++ tailWord_3114359) baseStart_3114359 baseEnd_3114359 := by
    simpa [prefixWord, tailWord_3114359, baseEnd_3114359] using wordTrace_append hprefix tailTrace_3114359
  have hstable : (prefixWord ++ tailWord_3114359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114359).length < 2 ^ (prefixWord ++ tailWord_3114359).sum := by decide
  have hdescent : baseEnd_3114359 < baseStart_3114359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114421 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3114421 : Nat := 118140960795 + 3114421 * 2 ^ 59
def prefixEnd_3114421 : Nat := 4983230072969 + 3 ^ 40 * 3114421 * 2
def baseEnd_3114421 : Nat := 1066129955637643031476363

theorem tailTrace_3114421 : CollatzResearch.WordTrace tailWord_3114421 prefixEnd_3114421 1066129955637643031476363 := by
  unfold tailWord_3114421
  simp only [CollatzResearch.WordTrace]
  refine ⟨113592265849992092605127117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75728177233328061736751411 113592265849992092605127117)
  ·
    refine ⟨42597099693747034726922669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113592265849992092605127117 42597099693747034726922669)
    ·
      refine ⟨15973912385155138022596001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42597099693747034726922669 15973912385155138022596001)
      ·
        refine ⟨11980434288866353516947001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15973912385155138022596001 11980434288866353516947001)
        ·
          refine ⟨8985325716649765137710251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11980434288866353516947001 8985325716649765137710251)
          ·
            refine ⟨13477988574974647706565377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8985325716649765137710251 13477988574974647706565377)
            ·
              refine ⟨10108491431230985779924033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13477988574974647706565377 10108491431230985779924033)
              ·
                refine ⟨7581368573423239334943025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10108491431230985779924033 7581368573423239334943025)
                ·
                  refine ⟨5686026430067429501207269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7581368573423239334943025 5686026430067429501207269)
                  ·
                    refine ⟨1066129955637643031476363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5686026430067429501207269 1066129955637643031476363)
                    ·
                      rfl

theorem cell22_3114421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3114421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114421 prefixEnd_3114421 := by exact prefixLift 3114421
  have htrace : WordTrace (prefixWord ++ tailWord_3114421) baseStart_3114421 baseEnd_3114421 := by
    simpa [prefixWord, tailWord_3114421, baseEnd_3114421] using wordTrace_append hprefix tailTrace_3114421
  have hstable : (prefixWord ++ tailWord_3114421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114421).length < 2 ^ (prefixWord ++ tailWord_3114421).sum := by decide
  have hdescent : baseEnd_3114421 < baseStart_3114421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114425 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 4]
def baseStart_3114425 : Nat := 118140960795 + 3114425 * 2 ^ 59
def prefixEnd_3114425 : Nat := 4983230072969 + 3 ^ 40 * 3114425 * 2
def baseEnd_3114425 : Nat := 355377108306462784792117

theorem tailTrace_3114425 : CollatzResearch.WordTrace tailWord_3114425 prefixEnd_3114425 355377108306462784792117 := by
  unfold tailWord_3114425
  simp only [CollatzResearch.WordTrace]
  refine ⟨113592411741977601288272729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75728274494651734192181819 113592411741977601288272729)
  ·
    refine ⟨85194308806483200966204547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113592411741977601288272729 85194308806483200966204547)
    ·
      refine ⟨127791463209724801449306821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85194308806483200966204547 127791463209724801449306821)
      ·
        refine ⟨23960899351823400271745029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127791463209724801449306821 23960899351823400271745029)
        ·
          refine ⟨4492668628466887550952193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23960899351823400271745029 4492668628466887550952193)
          ·
            refine ⟨3369501471350165663214145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4492668628466887550952193 3369501471350165663214145)
            ·
              refine ⟨2527126103512624247410609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3369501471350165663214145 2527126103512624247410609)
              ·
                refine ⟨1895344577634468185557957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527126103512624247410609 1895344577634468185557957)
                ·
                  refine ⟨355377108306462784792117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895344577634468185557957 355377108306462784792117)
                  ·
                    rfl

theorem cell22_3114425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_3114425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114425 prefixEnd_3114425 := by exact prefixLift 3114425
  have htrace : WordTrace (prefixWord ++ tailWord_3114425) baseStart_3114425 baseEnd_3114425 := by
    simpa [prefixWord, tailWord_3114425, baseEnd_3114425] using wordTrace_append hprefix tailTrace_3114425
  have hstable : (prefixWord ++ tailWord_3114425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114425).length < 2 ^ (prefixWord ++ tailWord_3114425).sum := by decide
  have hdescent : baseEnd_3114425 < baseStart_3114425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114436 : List Nat := [2, 3, 3, 2, 1, 1, 3, 7]
def baseStart_3114436 : Nat := 118140960795 + 3114436 * 2 ^ 59
def prefixEnd_3114436 : Nat := 4983230072969 + 3 ^ 40 * 3114436 * 2
def baseEnd_3114436 : Nat := 118459454493798665816813

theorem tailTrace_3114436 : CollatzResearch.WordTrace tailWord_3114436 prefixEnd_3114436 118459454493798665816813 := by
  unfold tailWord_3114436
  simp only [CollatzResearch.WordTrace]
  refine ⟨56796406472468875083461581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75728541963291833444615441 56796406472468875083461581)
  ·
    refine ⟨21298652427175828156298093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56796406472468875083461581 21298652427175828156298093)
    ·
      refine ⟨7986994660190935558611785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21298652427175828156298093 7986994660190935558611785)
      ·
        refine ⟨5990245995143201668958839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7986994660190935558611785 5990245995143201668958839)
        ·
          refine ⟨8985368992714802503438259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990245995143201668958839 8985368992714802503438259)
          ·
            refine ⟨13478053489072203755157389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8985368992714802503438259 13478053489072203755157389)
            ·
              refine ⟨5054270058402076408184021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13478053489072203755157389 5054270058402076408184021)
              ·
                refine ⟨118459454493798665816813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5054270058402076408184021 118459454493798665816813)
                ·
                  rfl

theorem cell22_3114436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 7].length) (baseStart_3114436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114436 prefixEnd_3114436 := by exact prefixLift 3114436
  have htrace : WordTrace (prefixWord ++ tailWord_3114436) baseStart_3114436 baseEnd_3114436 := by
    simpa [prefixWord, tailWord_3114436, baseEnd_3114436] using wordTrace_append hprefix tailTrace_3114436
  have hstable : (prefixWord ++ tailWord_3114436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114436).length < 2 ^ (prefixWord ++ tailWord_3114436).sum := by decide
  have hdescent : baseEnd_3114436 < baseStart_3114436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114479 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_3114479 : Nat := 118140960795 + 3114479 * 2 ^ 59
def prefixEnd_3114479 : Nat := 4983230072969 + 3 ^ 40 * 3114479 * 2
def baseEnd_3114479 : Nat := 1066149810222950213526185

theorem tailTrace_3114479 : CollatzResearch.WordTrace tailWord_3114479 prefixEnd_3114479 1066149810222950213526185 := by
  unfold tailWord_3114479
  simp only [CollatzResearch.WordTrace]
  refine ⟨113594381283781968510738491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75729587522521312340492327 113594381283781968510738491)
  ·
    refine ⟨170391571925672952766107737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113594381283781968510738491 170391571925672952766107737)
    ·
      refine ⟨127793678944254714574580803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170391571925672952766107737 127793678944254714574580803)
      ·
        refine ⟨191690518416382071861871205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127793678944254714574580803 191690518416382071861871205)
        ·
          refine ⟨35941972203071638474100851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191690518416382071861871205 35941972203071638474100851)
          ·
            refine ⟨53912958304607457711151277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35941972203071638474100851 53912958304607457711151277)
            ·
              refine ⟨20217359364227796641681729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53912958304607457711151277 20217359364227796641681729)
              ·
                refine ⟨15163019523170847481261297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20217359364227796641681729 15163019523170847481261297)
                ·
                  refine ⟨11372264642378135610945973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15163019523170847481261297 11372264642378135610945973)
                  ·
                    refine ⟨1066149810222950213526185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11372264642378135610945973 1066149810222950213526185)
                    ·
                      rfl

theorem cell22_3114479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_3114479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114479 prefixEnd_3114479 := by exact prefixLift 3114479
  have htrace : WordTrace (prefixWord ++ tailWord_3114479) baseStart_3114479 baseEnd_3114479 := by
    simpa [prefixWord, tailWord_3114479, baseEnd_3114479] using wordTrace_append hprefix tailTrace_3114479
  have hstable : (prefixWord ++ tailWord_3114479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114479).length < 2 ^ (prefixWord ++ tailWord_3114479).sum := by decide
  have hdescent : baseEnd_3114479 < baseStart_3114479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114481 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 5]
def baseStart_3114481 : Nat := 118140960795 + 3114481 * 2 ^ 59
def prefixEnd_3114481 : Nat := 4983230072969 + 3 ^ 40 * 3114481 * 2
def baseEnd_3114481 : Nat := 355383498287940958325393

theorem tailTrace_3114481 : CollatzResearch.WordTrace tailWord_3114481 prefixEnd_3114481 355383498287940958325393 := by
  unfold tailWord_3114481
  simp only [CollatzResearch.WordTrace]
  refine ⟨113594454229774722852311297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75729636153183148568207531 113594454229774722852311297)
  ·
    refine ⟨85195840672331042139233473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113594454229774722852311297 85195840672331042139233473)
    ·
      refine ⟨63896880504248281604425105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85195840672331042139233473 63896880504248281604425105)
      ·
        refine ⟨47922660378186211203318829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63896880504248281604425105 47922660378186211203318829)
        ·
          refine ⟨17970997641819829201244561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47922660378186211203318829 17970997641819829201244561)
          ·
            refine ⟨13478248231364871900933421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17970997641819829201244561 13478248231364871900933421)
            ·
              refine ⟨5054343086761826962850033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13478248231364871900933421 5054343086761826962850033)
              ·
                refine ⟨3790757315071370222137525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5054343086761826962850033 3790757315071370222137525)
                ·
                  refine ⟨355383498287940958325393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3790757315071370222137525 355383498287940958325393)
                  ·
                    rfl

theorem cell22_3114481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_3114481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114481 prefixEnd_3114481 := by exact prefixLift 3114481
  have htrace : WordTrace (prefixWord ++ tailWord_3114481) baseStart_3114481 baseEnd_3114481 := by
    simpa [prefixWord, tailWord_3114481, baseEnd_3114481] using wordTrace_append hprefix tailTrace_3114481
  have hstable : (prefixWord ++ tailWord_3114481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114481).length < 2 ^ (prefixWord ++ tailWord_3114481).sum := by decide
  have hdescent : baseEnd_3114481 < baseStart_3114481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114485 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3114485 : Nat := 118140960795 + 3114485 * 2 ^ 59
def prefixEnd_3114485 : Nat := 4983230072969 + 3 ^ 40 * 3114485 * 2
def baseEnd_3114485 : Nat := 1066151864145568197876167

theorem tailTrace_3114485 : CollatzResearch.WordTrace tailWord_3114485 prefixEnd_3114485 1066151864145568197876167 := by
  unfold tailWord_3114485
  simp only [CollatzResearch.WordTrace]
  refine ⟨113594600121760231535456909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75729733414506821023637939 113594600121760231535456909)
  ·
    refine ⟨42597975045660086825796341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113594600121760231535456909 42597975045660086825796341)
    ·
      refine ⟨3993560160530633139918407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42597975045660086825796341 3993560160530633139918407)
      ·
        refine ⟨5990340240795949709877611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993560160530633139918407 5990340240795949709877611)
        ·
          refine ⟨8985510361193924564816417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990340240795949709877611 8985510361193924564816417)
          ·
            refine ⟨6739132770895443423612313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985510361193924564816417 6739132770895443423612313)
            ·
              refine ⟨5054349578171582567709235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6739132770895443423612313 5054349578171582567709235)
              ·
                refine ⟨7581524367257373851563853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5054349578171582567709235 7581524367257373851563853)
                ·
                  refine ⟨2843071637721515194336445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7581524367257373851563853 2843071637721515194336445)
                  ·
                    refine ⟨1066151864145568197876167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843071637721515194336445 1066151864145568197876167)
                    ·
                      rfl

theorem cell22_3114485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3114485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114485 prefixEnd_3114485 := by exact prefixLift 3114485
  have htrace : WordTrace (prefixWord ++ tailWord_3114485) baseStart_3114485 baseEnd_3114485 := by
    simpa [prefixWord, tailWord_3114485, baseEnd_3114485] using wordTrace_append hprefix tailTrace_3114485
  have hstable : (prefixWord ++ tailWord_3114485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114485).length < 2 ^ (prefixWord ++ tailWord_3114485).sum := by decide
  have hdescent : baseEnd_3114485 < baseStart_3114485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114528 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_3114528 : Nat := 118140960795 + 3114528 * 2 ^ 59
def prefixEnd_3114528 : Nat := 4983230072969 + 3 ^ 40 * 3114528 * 2
def baseEnd_3114528 : Nat := 1066166583924330419051035

theorem tailTrace_3114528 : CollatzResearch.WordTrace tailWord_3114528 prefixEnd_3114528 1066166583924330419051035 := by
  unfold tailWord_3114528
  simp only [CollatzResearch.WordTrace]
  refine ⟨56798084230302224939636119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75730778973736299919514825 56798084230302224939636119)
  ·
    refine ⟨85197126345453337409454179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56798084230302224939636119 85197126345453337409454179)
    ·
      refine ⟨127795689518180006114181269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85197126345453337409454179 127795689518180006114181269)
      ·
        refine ⟨5990422946164687786602247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127795689518180006114181269 5990422946164687786602247)
        ·
          refine ⟨8985634419247031679903371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990422946164687786602247 8985634419247031679903371)
          ·
            refine ⟨13478451628870547519855057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8985634419247031679903371 13478451628870547519855057)
            ·
              refine ⟨10108838721652910639891293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13478451628870547519855057 10108838721652910639891293)
              ·
                refine ⟨3790814520619841489959235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10108838721652910639891293 3790814520619841489959235)
                ·
                  refine ⟨5686221780929762234938853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3790814520619841489959235 5686221780929762234938853)
                  ·
                    refine ⟨1066166583924330419051035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5686221780929762234938853 1066166583924330419051035)
                    ·
                      rfl

theorem cell22_3114528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_3114528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114528 prefixEnd_3114528 := by exact prefixLift 3114528
  have htrace : WordTrace (prefixWord ++ tailWord_3114528) baseStart_3114528 baseEnd_3114528 := by
    simpa [prefixWord, tailWord_3114528, baseEnd_3114528] using wordTrace_append hprefix tailTrace_3114528
  have hstable : (prefixWord ++ tailWord_3114528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114528).length < 2 ^ (prefixWord ++ tailWord_3114528).sum := by decide
  have hdescent : baseEnd_3114528 < baseStart_3114528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114569 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_3114569 : Nat := 118140960795 + 3114569 * 2 ^ 59
def prefixEnd_3114569 : Nat := 4983230072969 + 3 ^ 40 * 3114569 * 2
def baseEnd_3114569 : Nat := 1066180619062219978775909

theorem tailTrace_3114569 : CollatzResearch.WordTrace tailWord_3114569 prefixEnd_3114569 1066180619062219978775909 := by
  unfold tailWord_3114569
  simp only [CollatzResearch.WordTrace]
  refine ⟨113597663853455913881514761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75731775902303942587676507 113597663853455913881514761)
  ·
    refine ⟨85198247890091935411136071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113597663853455913881514761 85198247890091935411136071)
    ·
      refine ⟨127797371835137903116704107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85198247890091935411136071 127797371835137903116704107)
      ·
        refine ⟨191696057752706854675056161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127797371835137903116704107 191696057752706854675056161)
        ·
          refine ⟨143772043314530141006292121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191696057752706854675056161 143772043314530141006292121)
          ·
            refine ⟨107829032485897605754719091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143772043314530141006292121 107829032485897605754719091)
            ·
              refine ⟨161743548728846408632078637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107829032485897605754719091 161743548728846408632078637)
              ·
                refine ⟨60653830773317403237029489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161743548728846408632078637 60653830773317403237029489)
                ·
                  refine ⟨45490373079988052427772117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60653830773317403237029489 45490373079988052427772117)
                  ·
                    refine ⟨1066180619062219978775909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45490373079988052427772117 1066180619062219978775909)
                    ·
                      rfl

theorem cell22_3114569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_3114569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114569 prefixEnd_3114569 := by exact prefixLift 3114569
  have htrace : WordTrace (prefixWord ++ tailWord_3114569) baseStart_3114569 baseEnd_3114569 := by
    simpa [prefixWord, tailWord_3114569, baseEnd_3114569] using wordTrace_append hprefix tailTrace_3114569
  have hstable : (prefixWord ++ tailWord_3114569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114569).length < 2 ^ (prefixWord ++ tailWord_3114569).sum := by decide
  have hdescent : baseEnd_3114569 < baseStart_3114569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114605 : List Nat := [1, 5, 1, 1, 5, 1, 1, 7]
def baseStart_3114605 : Nat := 118140960795 + 3114605 * 2 ^ 59
def prefixEnd_3114605 : Nat := 4983230072969 + 3 ^ 40 * 3114605 * 2
def baseEnd_3114605 : Nat := 118465882510880876097311

theorem tailTrace_3114605 : CollatzResearch.WordTrace tailWord_3114605 prefixEnd_3114605 118465882510880876097311 := by
  unfold tailWord_3114605
  simp only [CollatzResearch.WordTrace]
  refine ⟨113598976881325492029825269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75732651254216994686550179 113598976881325492029825269)
  ·
    refine ⟨10649904082624264877796119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113598976881325492029825269 10649904082624264877796119)
    ·
      refine ⟨15974856123936397316694179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10649904082624264877796119 15974856123936397316694179)
      ·
        refine ⟨23962284185904595975041269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15974856123936397316694179 23962284185904595975041269)
        ·
          refine ⟨2246464142428555872660119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23962284185904595975041269 2246464142428555872660119)
          ·
            refine ⟨3369696213642833808990179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246464142428555872660119 3369696213642833808990179)
            ·
              refine ⟨5054544320464250713485269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3369696213642833808990179 5054544320464250713485269)
              ·
                refine ⟨118465882510880876097311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5054544320464250713485269 118465882510880876097311)
                ·
                  rfl

theorem cell22_3114605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 7].length) (baseStart_3114605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114605 prefixEnd_3114605 := by exact prefixLift 3114605
  have htrace : WordTrace (prefixWord ++ tailWord_3114605) baseStart_3114605 baseEnd_3114605 := by
    simpa [prefixWord, tailWord_3114605, baseEnd_3114605] using wordTrace_append hprefix tailTrace_3114605
  have hstable : (prefixWord ++ tailWord_3114605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114605).length < 2 ^ (prefixWord ++ tailWord_3114605).sum := by decide
  have hdescent : baseEnd_3114605 < baseStart_3114605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114661 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 6]
def baseStart_3114661 : Nat := 118140960795 + 3114661 * 2 ^ 59
def prefixEnd_3114661 : Nat := 4983230072969 + 3 ^ 40 * 3114661 * 2
def baseEnd_3114661 : Nat := 355404037514120801825209

theorem tailTrace_3114661 : CollatzResearch.WordTrace tailWord_3114661 prefixEnd_3114661 355404037514120801825209 := by
  unfold tailWord_3114661
  simp only [CollatzResearch.WordTrace]
  refine ⟨113601019369122613593863837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75734012912748409062575891 113601019369122613593863837)
  ·
    refine ⟨42600382263420980097698939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113601019369122613593863837 42600382263420980097698939)
    ·
      refine ⟨63900573395131470146548409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42600382263420980097698939 63900573395131470146548409)
      ·
        refine ⟨47925430046348602609911307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63900573395131470146548409 47925430046348602609911307)
        ·
          refine ⟨71888145069522903914866961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47925430046348602609911307 71888145069522903914866961)
          ·
            refine ⟨53916108802142177936150221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71888145069522903914866961 53916108802142177936150221)
            ·
              refine ⟨20218540800803316726056333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53916108802142177936150221 20218540800803316726056333)
              ·
                refine ⟨7581952800301243772271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20218540800803316726056333 7581952800301243772271125)
                ·
                  refine ⟨355404037514120801825209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7581952800301243772271125 355404037514120801825209)
                  ·
                    rfl

theorem cell22_3114661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_3114661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114661 prefixEnd_3114661 := by exact prefixLift 3114661
  have htrace : WordTrace (prefixWord ++ tailWord_3114661) baseStart_3114661 baseEnd_3114661 := by
    simpa [prefixWord, tailWord_3114661, baseEnd_3114661] using wordTrace_append hprefix tailTrace_3114661
  have hstable : (prefixWord ++ tailWord_3114661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114661).length < 2 ^ (prefixWord ++ tailWord_3114661).sum := by decide
  have hdescent : baseEnd_3114661 < baseStart_3114661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114691 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 8, 4]
def baseStart_3114691 : Nat := 118140960795 + 3114691 * 2 ^ 59
def prefixEnd_3114691 : Nat := 4983230072969 + 3 ^ 40 * 3114691 * 2
def baseEnd_3114691 : Nat := 1066222382155452327225535

theorem tailTrace_3114691 : CollatzResearch.WordTrace tailWord_3114691 prefixEnd_3114691 1066222382155452327225535 := by
  unfold tailWord_3114691
  simp only [CollatzResearch.WordTrace]
  refine ⟨113602113559013928717455927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75734742372675952478303951 113602113559013928717455927)
  ·
    refine ⟨170403170338520893076183891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113602113559013928717455927 170403170338520893076183891)
    ·
      refine ⟨255604755507781339614275837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170403170338520893076183891 255604755507781339614275837)
      ·
        refine ⟨95851783315418002355353439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255604755507781339614275837 95851783315418002355353439)
        ·
          refine ⟨143777674973127003533030159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95851783315418002355353439 143777674973127003533030159)
          ·
            refine ⟨215666512459690505299545239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143777674973127003533030159 215666512459690505299545239)
            ·
              refine ⟨323499768689535757949317859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215666512459690505299545239 323499768689535757949317859)
              ·
                refine ⟨485249653034303636923976789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323499768689535757949317859 485249653034303636923976789)
                ·
                  refine ⟨5686519371495745745202853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 485249653034303636923976789 5686519371495745745202853)
                  ·
                    refine ⟨1066222382155452327225535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5686519371495745745202853 1066222382155452327225535)
                    ·
                      rfl

theorem cell22_3114691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_3114691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114691 prefixEnd_3114691 := by exact prefixLift 3114691
  have htrace : WordTrace (prefixWord ++ tailWord_3114691) baseStart_3114691 baseEnd_3114691 := by
    simpa [prefixWord, tailWord_3114691, baseEnd_3114691] using wordTrace_append hprefix tailTrace_3114691
  have hstable : (prefixWord ++ tailWord_3114691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114691).length < 2 ^ (prefixWord ++ tailWord_3114691).sum := by decide
  have hdescent : baseEnd_3114691 < baseStart_3114691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114736 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_3114736 : Nat := 118140960795 + 3114736 * 2 ^ 59
def prefixEnd_3114736 : Nat := 4983230072969 + 3 ^ 40 * 3114736 * 2
def baseEnd_3114736 : Nat := 1066237786575087209850397

theorem tailTrace_3114736 : CollatzResearch.WordTrace tailWord_3114736 prefixEnd_3114736 1066237786575087209850397 := by
  unfold tailWord_3114736
  simp only [CollatzResearch.WordTrace]
  refine ⟨56801877421925450701422031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75735836562567267601896041 56801877421925450701422031)
  ·
    refine ⟨85202816132888176052133047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56801877421925450701422031 85202816132888176052133047)
    ·
      refine ⟨127804224199332264078199571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85202816132888176052133047 127804224199332264078199571)
      ·
        refine ⟨191706336298998396117299357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127804224199332264078199571 191706336298998396117299357)
        ·
          refine ⟨71889876112124398543987259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191706336298998396117299357 71889876112124398543987259)
          ·
            refine ⟨107834814168186597815980889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71889876112124398543987259 107834814168186597815980889)
            ·
              refine ⟨80876110626139948361985667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107834814168186597815980889 80876110626139948361985667)
              ·
                refine ⟨121314165939209922542978501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80876110626139948361985667 121314165939209922542978501)
                ·
                  refine ⟨22746406113601860476808469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121314165939209922542978501 22746406113601860476808469)
                  ·
                    refine ⟨1066237786575087209850397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22746406113601860476808469 1066237786575087209850397)
                    ·
                      rfl

theorem cell22_3114736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_3114736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114736 prefixEnd_3114736 := by exact prefixLift 3114736
  have htrace : WordTrace (prefixWord ++ tailWord_3114736) baseStart_3114736 baseEnd_3114736 := by
    simpa [prefixWord, tailWord_3114736, baseEnd_3114736] using wordTrace_append hprefix tailTrace_3114736
  have hstable : (prefixWord ++ tailWord_3114736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114736).length < 2 ^ (prefixWord ++ tailWord_3114736).sum := by decide
  have hdescent : baseEnd_3114736 < baseStart_3114736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114751 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 9]
def baseStart_3114751 : Nat := 118140960795 + 3114751 * 2 ^ 59
def prefixEnd_3114751 : Nat := 4983230072969 + 3 ^ 40 * 3114751 * 2
def baseEnd_3114751 : Nat := 355414307127210723575117

theorem tailTrace_3114751 : CollatzResearch.WordTrace tailWord_3114751 prefixEnd_3114751 355414307127210723575117 := by
  unfold tailWord_3114751
  simp only [CollatzResearch.WordTrace]
  refine ⟨113604301938796558964640107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75736201292531039309760071 113604301938796558964640107)
  ·
    refine ⟨170406452908194838446960161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113604301938796558964640107 170406452908194838446960161)
    ·
      refine ⟨127804839681146128835220121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170406452908194838446960161 127804839681146128835220121)
      ·
        refine ⟨95853629760859596626415091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127804839681146128835220121 95853629760859596626415091)
        ·
          refine ⟨143780444641289394939622637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95853629760859596626415091 143780444641289394939622637)
          ·
            refine ⟨53917666740483523102358489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143780444641289394939622637 53917666740483523102358489)
            ·
              refine ⟨40438250055362642326768867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53917666740483523102358489 40438250055362642326768867)
              ·
                refine ⟨60657375083043963490153301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40438250055362642326768867 60657375083043963490153301)
                ·
                  refine ⟨355414307127210723575117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60657375083043963490153301 355414307127210723575117)
                  ·
                    rfl

theorem cell22_3114751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_3114751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114751 prefixEnd_3114751 := by exact prefixLift 3114751
  have htrace : WordTrace (prefixWord ++ tailWord_3114751) baseStart_3114751 baseEnd_3114751 := by
    simpa [prefixWord, tailWord_3114751, baseEnd_3114751] using wordTrace_append hprefix tailTrace_3114751
  have hstable : (prefixWord ++ tailWord_3114751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114751).length < 2 ^ (prefixWord ++ tailWord_3114751).sum := by decide
  have hdescent : baseEnd_3114751 < baseStart_3114751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114770 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3114770 : Nat := 118140960795 + 3114770 * 2 ^ 59
def prefixEnd_3114770 : Nat := 4983230072969 + 3 ^ 40 * 3114770 * 2
def baseEnd_3114770 : Nat := 1066249425469922454500293

theorem tailTrace_3114770 : CollatzResearch.WordTrace tailWord_3114770 prefixEnd_3114770 1066249425469922454500293 := by
  unfold tailWord_3114770
  simp only [CollatzResearch.WordTrace]
  refine ⟨28401248731431931302395441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75736663283818483473054509 28401248731431931302395441)
  ·
    refine ⟨21300936548573948476796581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28401248731431931302395441 21300936548573948476796581)
    ·
      refine ⟨3993925602857615339399359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21300936548573948476796581 3993925602857615339399359)
      ·
        refine ⟨5990888404286423009099039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993925602857615339399359 5990888404286423009099039)
        ·
          refine ⟨8986332606429634513648559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990888404286423009099039 8986332606429634513648559)
          ·
            refine ⟨13479498909644451770472839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986332606429634513648559 13479498909644451770472839)
            ·
              refine ⟨20219248364466677655709259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13479498909644451770472839 20219248364466677655709259)
              ·
                refine ⟨30328872546700016483563889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20219248364466677655709259 30328872546700016483563889)
                ·
                  refine ⟨22746654410025012362672917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30328872546700016483563889 22746654410025012362672917)
                  ·
                    refine ⟨1066249425469922454500293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22746654410025012362672917 1066249425469922454500293)
                    ·
                      rfl

theorem cell22_3114770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3114770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114770 prefixEnd_3114770 := by exact prefixLift 3114770
  have htrace : WordTrace (prefixWord ++ tailWord_3114770) baseStart_3114770 baseEnd_3114770 := by
    simpa [prefixWord, tailWord_3114770, baseEnd_3114770] using wordTrace_append hprefix tailTrace_3114770
  have hstable : (prefixWord ++ tailWord_3114770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114770).length < 2 ^ (prefixWord ++ tailWord_3114770).sum := by decide
  have hdescent : baseEnd_3114770 < baseStart_3114770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114783 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 2, 5]
def baseStart_3114783 : Nat := 118140960795 + 3114783 * 2 ^ 59
def prefixEnd_3114783 : Nat := 4983230072969 + 3 ^ 40 * 3114783 * 2
def baseEnd_3114783 : Nat := 1066253875635594753925253

theorem tailTrace_3114783 : CollatzResearch.WordTrace tailWord_3114783 prefixEnd_3114783 1066253875635594753925253 := by
  unfold tailWord_3114783
  simp only [CollatzResearch.WordTrace]
  refine ⟨113605469074680628429805003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75736979383120418953203335 113605469074680628429805003)
  ·
    refine ⟨170408203612020942644707505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113605469074680628429805003 170408203612020942644707505)
    ·
      refine ⟨127806152709015706983530629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170408203612020942644707505 127806152709015706983530629)
      ·
        refine ⟨23963653632940445059411993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127806152709015706983530629 23963653632940445059411993)
        ·
          refine ⟨17972740224705333794558995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23963653632940445059411993 17972740224705333794558995)
          ·
            refine ⟨26959110337058000691838493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17972740224705333794558995 26959110337058000691838493)
            ·
              refine ⟨10109666376396750259439435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26959110337058000691838493 10109666376396750259439435)
              ·
                refine ⟨15164499564595125389159153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10109666376396750259439435 15164499564595125389159153)
                ·
                  refine ⟨11373374673446344041869365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15164499564595125389159153 11373374673446344041869365)
                  ·
                    refine ⟨1066253875635594753925253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11373374673446344041869365 1066253875635594753925253)
                    ·
                      rfl

theorem cell22_3114783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_3114783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114783 prefixEnd_3114783 := by exact prefixLift 3114783
  have htrace : WordTrace (prefixWord ++ tailWord_3114783) baseStart_3114783 baseEnd_3114783 := by
    simpa [prefixWord, tailWord_3114783, baseEnd_3114783] using wordTrace_append hprefix tailTrace_3114783
  have hstable : (prefixWord ++ tailWord_3114783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114783).length < 2 ^ (prefixWord ++ tailWord_3114783).sum := by decide
  have hdescent : baseEnd_3114783 < baseStart_3114783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114806 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3114806 : Nat := 118140960795 + 3114806 * 2 ^ 59
def prefixEnd_3114806 : Nat := 4983230072969 + 3 ^ 40 * 3114806 * 2
def baseEnd_3114806 : Nat := 1066261749005630360600183

theorem tailTrace_3114806 : CollatzResearch.WordTrace tailWord_3114806 prefixEnd_3114806 1066261749005630360600183 := by
  unfold tailWord_3114806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100394247099831459868267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75737538635731535571928181 7100394247099831459868267)
  ·
    refine ⟨10650591370649747189802401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7100394247099831459868267 10650591370649747189802401)
    ·
      refine ⟨7987943527987310392351801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10650591370649747189802401 7987943527987310392351801)
      ·
        refine ⟨5990957645990482794263851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7987943527987310392351801 5990957645990482794263851)
        ·
          refine ⟨8986436468985724191395777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990957645990482794263851 8986436468985724191395777)
          ·
            refine ⟨6739827351739293143546833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8986436468985724191395777 6739827351739293143546833)
            ·
              refine ⟨5054870513804469857660125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6739827351739293143546833 5054870513804469857660125)
              ·
                refine ⟨1895576442676676196622547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5054870513804469857660125 1895576442676676196622547)
                ·
                  refine ⟨2843364664015014294933821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895576442676676196622547 2843364664015014294933821)
                  ·
                    refine ⟨1066261749005630360600183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843364664015014294933821 1066261749005630360600183)
                    ·
                      rfl

theorem cell22_3114806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3114806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114806 prefixEnd_3114806 := by exact prefixLift 3114806
  have htrace : WordTrace (prefixWord ++ tailWord_3114806) baseStart_3114806 baseEnd_3114806 := by
    simpa [prefixWord, tailWord_3114806, baseEnd_3114806] using wordTrace_append hprefix tailTrace_3114806
  have hstable : (prefixWord ++ tailWord_3114806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114806).length < 2 ^ (prefixWord ++ tailWord_3114806).sum := by decide
  have hdescent : baseEnd_3114806 < baseStart_3114806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114862 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3114862 : Nat := 118140960795 + 3114862 * 2 ^ 59
def prefixEnd_3114862 : Nat := 4983230072969 + 3 ^ 40 * 3114862 * 2
def baseEnd_3114862 : Nat := 1066280918950064881200011

theorem tailTrace_3114862 : CollatzResearch.WordTrace tailWord_3114862 prefixEnd_3114862 1066280918950064881200011 := by
  unfold tailWord_3114862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14201043805174303115241355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75738900294262949947953893 14201043805174303115241355)
  ·
    refine ⟨21301565707761454672862033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14201043805174303115241355 21301565707761454672862033)
    ·
      refine ⟨15976174280821091004646525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21301565707761454672862033 15976174280821091004646525)
      ·
        refine ⟨5991065355307909126742447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15976174280821091004646525 5991065355307909126742447)
        ·
          refine ⟨8986598032961863690113671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5991065355307909126742447 8986598032961863690113671)
          ·
            refine ⟨13479897049442795535170507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986598032961863690113671 13479897049442795535170507)
            ·
              refine ⟨20219845574164193302755761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13479897049442795535170507 20219845574164193302755761)
              ·
                refine ⟨15164884180623144977066821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20219845574164193302755761 15164884180623144977066821)
                ·
                  refine ⟨2843415783866839683200029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15164884180623144977066821 2843415783866839683200029)
                  ·
                    refine ⟨1066280918950064881200011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843415783866839683200029 1066280918950064881200011)
                    ·
                      rfl

theorem cell22_3114862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3114862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114862 prefixEnd_3114862 := by exact prefixLift 3114862
  have htrace : WordTrace (prefixWord ++ tailWord_3114862) baseStart_3114862 baseEnd_3114862 := by
    simpa [prefixWord, tailWord_3114862, baseEnd_3114862] using wordTrace_append hprefix tailTrace_3114862
  have hstable : (prefixWord ++ tailWord_3114862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114862).length < 2 ^ (prefixWord ++ tailWord_3114862).sum := by decide
  have hdescent : baseEnd_3114862 < baseStart_3114862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114881 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 4]
def baseStart_3114881 : Nat := 118140960795 + 3114881 * 2 ^ 59
def prefixEnd_3114881 : Nat := 4983230072969 + 3 ^ 40 * 3114881 * 2
def baseEnd_3114881 : Nat := 355429141012785054991651

theorem tailTrace_3114881 : CollatzResearch.WordTrace tailWord_3114881 prefixEnd_3114881 355429141012785054991651 := by
  unfold tailWord_3114881
  simp only [CollatzResearch.WordTrace]
  refine ⟨113609043428325591166872497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75739362285550394111248331 113609043428325591166872497)
  ·
    refine ⟨85206782571244193375154373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113609043428325591166872497 85206782571244193375154373)
    ·
      refine ⟨15976271732108286257841445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85206782571244193375154373 15976271732108286257841445)
      ·
        refine ⟨2995550949770303673345271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15976271732108286257841445 2995550949770303673345271)
        ·
          refine ⟨4493326424655455510017907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995550949770303673345271 4493326424655455510017907)
          ·
            refine ⟨6739989636983183265026861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493326424655455510017907 6739989636983183265026861)
            ·
              refine ⟨2527496113868693724385073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6739989636983183265026861 2527496113868693724385073)
              ·
                refine ⟨1895622085401520293288805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527496113868693724385073 1895622085401520293288805)
                ·
                  refine ⟨355429141012785054991651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1895622085401520293288805 355429141012785054991651)
                  ·
                    rfl

theorem cell22_3114881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_3114881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114881 prefixEnd_3114881 := by exact prefixLift 3114881
  have htrace : WordTrace (prefixWord ++ tailWord_3114881) baseStart_3114881 baseEnd_3114881 := by
    simpa [prefixWord, tailWord_3114881, baseEnd_3114881] using wordTrace_append hprefix tailTrace_3114881
  have hstable : (prefixWord ++ tailWord_3114881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114881).length < 2 ^ (prefixWord ++ tailWord_3114881).sum := by decide
  have hdescent : baseEnd_3114881 < baseStart_3114881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114941 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_3114941 : Nat := 118140960795 + 3114941 * 2 ^ 59
def prefixEnd_3114941 : Nat := 4983230072969 + 3 ^ 40 * 3114941 * 2
def baseEnd_3114941 : Nat := 1066307962264535008474769

theorem tailTrace_3114941 : CollatzResearch.WordTrace tailWord_3114941 prefixEnd_3114941 1066307962264535008474769 := by
  unfold tailWord_3114941
  simp only [CollatzResearch.WordTrace]
  refine ⟨113611231808108221414056677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75740821205405480942704451 113611231808108221414056677)
  ·
    refine ⟨21302105964020291515135627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113611231808108221414056677 21302105964020291515135627)
    ·
      refine ⟨31953158946030437272703441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21302105964020291515135627 31953158946030437272703441)
      ·
        refine ⟨23964869209522827954527581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31953158946030437272703441 23964869209522827954527581)
        ·
          refine ⟨8986825953571060482947843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23964869209522827954527581 8986825953571060482947843)
          ·
            refine ⟨13480238930356590724421765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986825953571060482947843 13480238930356590724421765)
            ·
              refine ⟨2527544799441860760829081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13480238930356590724421765 2527544799441860760829081)
              ·
                refine ⟨1895658599581395570621811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527544799441860760829081 1895658599581395570621811)
                ·
                  refine ⟨2843487899372093355932717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895658599581395570621811 2843487899372093355932717)
                  ·
                    refine ⟨1066307962264535008474769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843487899372093355932717 1066307962264535008474769)
                    ·
                      rfl

theorem cell22_3114941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_3114941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114941 prefixEnd_3114941 := by exact prefixLift 3114941
  have htrace : WordTrace (prefixWord ++ tailWord_3114941) baseStart_3114941 baseEnd_3114941 := by
    simpa [prefixWord, tailWord_3114941, baseEnd_3114941] using wordTrace_append hprefix tailTrace_3114941
  have hstable : (prefixWord ++ tailWord_3114941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114941).length < 2 ^ (prefixWord ++ tailWord_3114941).sum := by decide
  have hdescent : baseEnd_3114941 < baseStart_3114941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114965 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 8]
def baseStart_3114965 : Nat := 118140960795 + 3114965 * 2 ^ 59
def prefixEnd_3114965 : Nat := 4983230072969 + 3 ^ 40 * 3114965 * 2
def baseEnd_3114965 : Nat := 355438725985002315291565

theorem tailTrace_3114965 : CollatzResearch.WordTrace tailWord_3114965 prefixEnd_3114965 355438725985002315291565 := by
  unfold tailWord_3114965
  simp only [CollatzResearch.WordTrace]
  refine ⟨113612107160021273512930349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75741404773347515675286899 113612107160021273512930349)
  ·
    refine ⟨42604540185007977567348881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113612107160021273512930349 42604540185007977567348881)
    ·
      refine ⟨31953405138755983175511661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42604540185007977567348881 31953405138755983175511661)
      ·
        refine ⟨11982526927033493690816873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31953405138755983175511661 11982526927033493690816873)
        ·
          refine ⟨8986895195275120268112655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11982526927033493690816873 8986895195275120268112655)
          ·
            refine ⟨13480342792912680402168983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8986895195275120268112655 13480342792912680402168983)
            ·
              refine ⟨20220514189369020603253475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13480342792912680402168983 20220514189369020603253475)
              ·
                refine ⟨30330771284053530904880213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20220514189369020603253475 30330771284053530904880213)
                ·
                  refine ⟨355438725985002315291565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30330771284053530904880213 355438725985002315291565)
                  ·
                    rfl

theorem cell22_3114965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_3114965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114965 prefixEnd_3114965 := by exact prefixLift 3114965
  have htrace : WordTrace (prefixWord ++ tailWord_3114965) baseStart_3114965 baseEnd_3114965 := by
    simpa [prefixWord, tailWord_3114965, baseEnd_3114965] using wordTrace_append hprefix tailTrace_3114965
  have hstable : (prefixWord ++ tailWord_3114965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114965).length < 2 ^ (prefixWord ++ tailWord_3114965).sum := by decide
  have hdescent : baseEnd_3114965 < baseStart_3114965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114980 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_3114980 : Nat := 118140960795 + 3114980 * 2 ^ 59
def prefixEnd_3114980 : Nat := 4983230072969 + 3 ^ 40 * 3114980 * 2
def baseEnd_3114980 : Nat := 1066321312761551906749649

theorem tailTrace_3114980 : CollatzResearch.WordTrace tailWord_3114980 prefixEnd_3114980 1066321312761551906749649 := by
  unfold tailWord_3114980
  simp only [CollatzResearch.WordTrace]
  refine ⟨56806327127483465537363197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75741769503311287383150929 56806327127483465537363197)
  ·
    refine ⟨21302372672806299576511199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56806327127483465537363197 21302372672806299576511199)
    ·
      refine ⟨31953559009209449364766799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21302372672806299576511199 31953559009209449364766799)
      ·
        refine ⟨47930338513814174047150199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31953559009209449364766799 47930338513814174047150199)
        ·
          refine ⟨71895507770721261070725299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47930338513814174047150199 71895507770721261070725299)
          ·
            refine ⟨107843261656081891606087949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71895507770721261070725299 107843261656081891606087949)
            ·
              refine ⟨40441223121030709352282981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107843261656081891606087949 40441223121030709352282981)
              ·
                refine ⟨7582729335193258003553059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40441223121030709352282981 7582729335193258003553059)
                ·
                  refine ⟨11374094002789887005329589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7582729335193258003553059 11374094002789887005329589)
                  ·
                    refine ⟨1066321312761551906749649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11374094002789887005329589 1066321312761551906749649)
                    ·
                      rfl

theorem cell22_3114980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_3114980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114980 prefixEnd_3114980 := by exact prefixLift 3114980
  have htrace : WordTrace (prefixWord ++ tailWord_3114980) baseStart_3114980 baseEnd_3114980 := by
    simpa [prefixWord, tailWord_3114980, baseEnd_3114980] using wordTrace_append hprefix tailTrace_3114980
  have hstable : (prefixWord ++ tailWord_3114980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114980).length < 2 ^ (prefixWord ++ tailWord_3114980).sum := by decide
  have hdescent : baseEnd_3114980 < baseStart_3114980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3114995 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 2, 4]
def baseStart_3114995 : Nat := 118140960795 + 3114995 * 2 ^ 59
def prefixEnd_3114995 : Nat := 4983230072969 + 3 ^ 40 * 3114995 * 2
def baseEnd_3114995 : Nat := 1066326447568096867624603

theorem tailTrace_3114995 : CollatzResearch.WordTrace tailWord_3114995 prefixEnd_3114995 1066326447568096867624603 := by
  unfold tailWord_3114995
  simp only [CollatzResearch.WordTrace]
  refine ⟨113613201349912588636522439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75742134233275059091014959 113613201349912588636522439)
  ·
    refine ⟨170419802024868882954783659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113613201349912588636522439 170419802024868882954783659)
    ·
      refine ⟨255629703037303324432175489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170419802024868882954783659 255629703037303324432175489)
      ·
        refine ⟨191722277277977493324131617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255629703037303324432175489 191722277277977493324131617)
        ·
          refine ⟨143791707958483119993098713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191722277277977493324131617 143791707958483119993098713)
          ·
            refine ⟨107843780968862339994824035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143791707958483119993098713 107843780968862339994824035)
            ·
              refine ⟨161765671453293509992236053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107843780968862339994824035 161765671453293509992236053)
              ·
                refine ⟨7582765849373133280886065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161765671453293509992236053 7582765849373133280886065)
                ·
                  refine ⟨5687074387029849960664549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7582765849373133280886065 5687074387029849960664549)
                  ·
                    refine ⟨1066326447568096867624603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5687074387029849960664549 1066326447568096867624603)
                    ·
                      rfl

theorem cell22_3114995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_3114995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3114995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3114995 prefixEnd_3114995 := by exact prefixLift 3114995
  have htrace : WordTrace (prefixWord ++ tailWord_3114995) baseStart_3114995 baseEnd_3114995 := by
    simpa [prefixWord, tailWord_3114995, baseEnd_3114995] using wordTrace_append hprefix tailTrace_3114995
  have hstable : (prefixWord ++ tailWord_3114995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3114995).length < 2 ^ (prefixWord ++ tailWord_3114995).sum := by decide
  have hdescent : baseEnd_3114995 < baseStart_3114995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3114995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115044 : List Nat := [2, 3, 1, 4, 3, 1, 8]
def baseStart_3115044 : Nat := 118140960795 + 3115044 * 2 ^ 59
def prefixEnd_3115044 : Nat := 4983230072969 + 3 ^ 40 * 3115044 * 2
def baseEnd_3115044 : Nat := 39494193380351002709239

theorem tailTrace_3115044 : CollatzResearch.WordTrace tailWord_3115044 prefixEnd_3115044 39494193380351002709239 := by
  unfold tailWord_3115044
  simp only [CollatzResearch.WordTrace]
  refine ⟨56807494263367535002528093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75743325684490046670037457 56807494263367535002528093)
  ·
    refine ⟨21302810348762825625948035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56807494263367535002528093 21302810348762825625948035)
    ·
      refine ⟨31954215523144238438922053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21302810348762825625948035 31954215523144238438922053)
      ·
        refine ⟨5991415410589544707297885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31954215523144238438922053 5991415410589544707297885)
        ·
          refine ⟨2246780778971079265236707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5991415410589544707297885 2246780778971079265236707)
          ·
            refine ⟨3370171168456618897855061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246780778971079265236707 3370171168456618897855061)
            ·
              refine ⟨39494193380351002709239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3370171168456618897855061 39494193380351002709239)
              ·
                rfl

theorem cell22_3115044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 8].length) (baseStart_3115044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115044 prefixEnd_3115044 := by exact prefixLift 3115044
  have htrace : WordTrace (prefixWord ++ tailWord_3115044) baseStart_3115044 baseEnd_3115044 := by
    simpa [prefixWord, tailWord_3115044, baseEnd_3115044] using wordTrace_append hprefix tailTrace_3115044
  have hstable : (prefixWord ++ tailWord_3115044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115044).length < 2 ^ (prefixWord ++ tailWord_3115044).sum := by decide
  have hdescent : baseEnd_3115044 < baseStart_3115044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115059 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 1, 3]
def baseStart_3115059 : Nat := 118140960795 + 3115059 * 2 ^ 59
def prefixEnd_3115059 : Nat := 4983230072969 + 3 ^ 40 * 3115059 * 2
def baseEnd_3115059 : Nat := 1066348356076022034024407

theorem tailTrace_3115059 : CollatzResearch.WordTrace tailWord_3115059 prefixEnd_3115059 1066348356076022034024407 := by
  unfold tailWord_3115059
  simp only [CollatzResearch.WordTrace]
  refine ⟨113615535621680727566852231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75743690414453818377901487 113615535621680727566852231)
  ·
    refine ⟨170423303432521091350278347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113615535621680727566852231 170423303432521091350278347)
    ·
      refine ⟨255634955148781637025417521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170423303432521091350278347 255634955148781637025417521)
      ·
        refine ⟨191726216361586227769063141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255634955148781637025417521 191726216361586227769063141)
        ·
          refine ⟨35948665567797417706699339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191726216361586227769063141 35948665567797417706699339)
          ·
            refine ⟨53922998351696126560049009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35948665567797417706699339 53922998351696126560049009)
            ·
              refine ⟨40442248763772094920036757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53922998351696126560049009 40442248763772094920036757)
              ·
                refine ⟨1895730410801816949376723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40442248763772094920036757 1895730410801816949376723)
                ·
                  refine ⟨2843595616202725424065085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895730410801816949376723 2843595616202725424065085)
                  ·
                    refine ⟨1066348356076022034024407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843595616202725424065085 1066348356076022034024407)
                    ·
                      rfl

theorem cell22_3115059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 3].length) (baseStart_3115059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115059 prefixEnd_3115059 := by exact prefixLift 3115059
  have htrace : WordTrace (prefixWord ++ tailWord_3115059) baseStart_3115059 baseEnd_3115059 := by
    simpa [prefixWord, tailWord_3115059, baseEnd_3115059] using wordTrace_append hprefix tailTrace_3115059
  have hstable : (prefixWord ++ tailWord_3115059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115059).length < 2 ^ (prefixWord ++ tailWord_3115059).sum := by decide
  have hdescent : baseEnd_3115059 < baseStart_3115059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115072 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_3115072 : Nat := 118140960795 + 3115072 * 2 ^ 59
def prefixEnd_3115072 : Nat := 4983230072969 + 3 ^ 40 * 3115072 * 2
def baseEnd_3115072 : Nat := 355450935413898111149789

theorem tailTrace_3115072 : CollatzResearch.WordTrace tailWord_3115072 prefixEnd_3115072 355450935413898111149789 := by
  unfold tailWord_3115072
  simp only [CollatzResearch.WordTrace]
  refine ⟨56808004885316815393537735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75744006513755753858050313 56808004885316815393537735)
  ·
    refine ⟨85212007327975223090306603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56808004885316815393537735 85212007327975223090306603)
    ·
      refine ⟨127818010991962834635459905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85212007327975223090306603 127818010991962834635459905)
      ·
        refine ⟨95863508243972125976594929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127818010991962834635459905 95863508243972125976594929)
        ·
          refine ⟨71897631182979094482446197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95863508243972125976594929 71897631182979094482446197)
          ·
            refine ⟨6740402923404290107729331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71897631182979094482446197 6740402923404290107729331)
            ·
              refine ⟨10110604385106435161593997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740402923404290107729331 10110604385106435161593997)
              ·
                refine ⟨3791476644414913185597749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10110604385106435161593997 3791476644414913185597749)
                ·
                  refine ⟨355450935413898111149789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3791476644414913185597749 355450935413898111149789)
                  ·
                    rfl

theorem cell22_3115072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_3115072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115072 prefixEnd_3115072 := by exact prefixLift 3115072
  have htrace : WordTrace (prefixWord ++ tailWord_3115072) baseStart_3115072 baseEnd_3115072 := by
    simpa [prefixWord, tailWord_3115072, baseEnd_3115072] using wordTrace_append hprefix tailTrace_3115072
  have hstable : (prefixWord ++ tailWord_3115072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115072).length < 2 ^ (prefixWord ++ tailWord_3115072).sum := by decide
  have hdescent : baseEnd_3115072 < baseStart_3115072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115106 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3115106 : Nat := 118140960795 + 3115106 * 2 ^ 59
def prefixEnd_3115106 : Nat := 4983230072969 + 3 ^ 40 * 3115106 * 2
def baseEnd_3115106 : Nat := 355454815045509859366421

theorem tailTrace_3115106 : CollatzResearch.WordTrace tailWord_3115106 prefixEnd_3115106 355454815045509859366421 := by
  unfold tailWord_3115106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28404312463127613648453293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75744833235006969729208781 28404312463127613648453293)
  ·
    refine ⟨10651617173672855118169985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28404312463127613648453293 10651617173672855118169985)
    ·
      refine ⟨7988712880254641338627489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10651617173672855118169985 7988712880254641338627489)
      ·
        refine ⟨5991534660190981003970617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7988712880254641338627489 5991534660190981003970617)
        ·
          refine ⟨4493650995143235752977963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5991534660190981003970617 4493650995143235752977963)
          ·
            refine ⟨6740476492714853629466945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493650995143235752977963 6740476492714853629466945)
            ·
              refine ⟨5055357369536140222100209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6740476492714853629466945 5055357369536140222100209)
              ·
                refine ⟨3791518027152105166575157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055357369536140222100209 3791518027152105166575157)
                ·
                  refine ⟨355454815045509859366421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3791518027152105166575157 355454815045509859366421)
                  ·
                    rfl

theorem cell22_3115106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3115106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115106 prefixEnd_3115106 := by exact prefixLift 3115106
  have htrace : WordTrace (prefixWord ++ tailWord_3115106) baseStart_3115106 baseEnd_3115106 := by
    simpa [prefixWord, tailWord_3115106, baseEnd_3115106] using wordTrace_append hprefix tailTrace_3115106
  have hstable : (prefixWord ++ tailWord_3115106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115106).length < 2 ^ (prefixWord ++ tailWord_3115106).sum := by decide
  have hdescent : baseEnd_3115106 < baseStart_3115106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115117 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3115117 : Nat := 118140960795 + 3115117 * 2 ^ 59
def prefixEnd_3115117 : Nat := 4983230072969 + 3 ^ 40 * 3115117 * 2
def baseEnd_3115117 : Nat := 355456070220443072024743

theorem tailTrace_3115117 : CollatzResearch.WordTrace tailWord_3115117 prefixEnd_3115117 355456070220443072024743 := by
  unfold tailWord_3115117
  simp only [CollatzResearch.WordTrace]
  refine ⟨113617651055470603472463605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75745100703647068981642403 113617651055470603472463605)
  ·
    refine ⟨10651654786450369075543463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113617651055470603472463605 10651654786450369075543463)
    ·
      refine ⟨15977482179675553613315195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10651654786450369075543463 15977482179675553613315195)
      ·
        refine ⟨23966223269513330419972793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15977482179675553613315195 23966223269513330419972793)
        ·
          refine ⟨17974667452134997814979595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23966223269513330419972793 17974667452134997814979595)
          ·
            refine ⟨26962001178202496722469393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17974667452134997814979595 26962001178202496722469393)
            ·
              refine ⟨20221500883651872541852045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26962001178202496722469393 20221500883651872541852045)
              ·
                refine ⟨7583062831369452203194517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20221500883651872541852045 7583062831369452203194517)
                ·
                  refine ⟨355456070220443072024743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7583062831369452203194517 355456070220443072024743)
                  ·
                    rfl

theorem cell22_3115117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3115117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115117 prefixEnd_3115117 := by exact prefixLift 3115117
  have htrace : WordTrace (prefixWord ++ tailWord_3115117) baseStart_3115117 baseEnd_3115117 := by
    simpa [prefixWord, tailWord_3115117, baseEnd_3115117] using wordTrace_append hprefix tailTrace_3115117
  have hstable : (prefixWord ++ tailWord_3115117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115117).length < 2 ^ (prefixWord ++ tailWord_3115117).sum := by decide
  have hdescent : baseEnd_3115117 < baseStart_3115117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115132 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_3115132 : Nat := 118140960795 + 3115132 * 2 ^ 59
def prefixEnd_3115132 : Nat := 4983230072969 + 3 ^ 40 * 3115132 * 2
def baseEnd_3115132 : Nat := 1066373345467874176949183

theorem tailTrace_3115132 : CollatzResearch.WordTrace tailWord_3115132 prefixEnd_3115132 1066373345467874176949183 := by
  unfold tailWord_3115132
  simp only [CollatzResearch.WordTrace]
  refine ⟨56809099075208130517129825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75745465433610840689506433 56809099075208130517129825)
  ·
    refine ⟨42606824306406097887847369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56809099075208130517129825 42606824306406097887847369)
    ·
      refine ⟨31955118229804573415885527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42606824306406097887847369 31955118229804573415885527)
      ·
        refine ⟨47932677344706860123828291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31955118229804573415885527 47932677344706860123828291)
        ·
          refine ⟨71899016017060290185742437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47932677344706860123828291 71899016017060290185742437)
          ·
            refine ⟨13481065503198804409826707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71899016017060290185742437 13481065503198804409826707)
            ·
              refine ⟨20221598254798206614740061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13481065503198804409826707 20221598254798206614740061)
              ·
                refine ⟨7583099345549327480527523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20221598254798206614740061 7583099345549327480527523)
                ·
                  refine ⟨11374649018323991220791285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583099345549327480527523 11374649018323991220791285)
                  ·
                    refine ⟨1066373345467874176949183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11374649018323991220791285 1066373345467874176949183)
                    ·
                      rfl

theorem cell22_3115132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_3115132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115132 prefixEnd_3115132 := by exact prefixLift 3115132
  have htrace : WordTrace (prefixWord ++ tailWord_3115132) baseStart_3115132 baseEnd_3115132 := by
    simpa [prefixWord, tailWord_3115132, baseEnd_3115132] using wordTrace_append hprefix tailTrace_3115132
  have hstable : (prefixWord ++ tailWord_3115132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115132).length < 2 ^ (prefixWord ++ tailWord_3115132).sum := by decide
  have hdescent : baseEnd_3115132 < baseStart_3115132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115194 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_3115194 : Nat := 118140960795 + 3115194 * 2 ^ 59
def prefixEnd_3115194 : Nat := 4983230072969 + 3 ^ 40 * 3115194 * 2
def baseEnd_3115194 : Nat := 1066394569334926681898993

theorem tailTrace_3115194 : CollatzResearch.WordTrace tailWord_3115194 prefixEnd_3115194 1066394569334926681898993 := by
  unfold tailWord_3115194
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405114869047911405754159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75746972984127763748677757 28405114869047911405754159)
  ·
    refine ⟨42607672303571867108631239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28405114869047911405754159 42607672303571867108631239)
    ·
      refine ⟨63911508455357800662946859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42607672303571867108631239 63911508455357800662946859)
      ·
        refine ⟨95867262683036700994420289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63911508455357800662946859 95867262683036700994420289)
        ·
          refine ⟨71900447012277525745815217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95867262683036700994420289 71900447012277525745815217)
          ·
            refine ⟨53925335259208144309361413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71900447012277525745815217 53925335259208144309361413)
            ·
              refine ⟨10111000361101527058005265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53925335259208144309361413 10111000361101527058005265)
              ·
                refine ⟨7583250270826145293503949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10111000361101527058005265 7583250270826145293503949)
                ·
                  refine ⟨2843718851559804485063981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7583250270826145293503949 2843718851559804485063981)
                  ·
                    refine ⟨1066394569334926681898993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843718851559804485063981 1066394569334926681898993)
                    ·
                      rfl

theorem cell22_3115194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_3115194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115194 prefixEnd_3115194 := by exact prefixLift 3115194
  have htrace : WordTrace (prefixWord ++ tailWord_3115194) baseStart_3115194 baseEnd_3115194 := by
    simpa [prefixWord, tailWord_3115194, baseEnd_3115194] using wordTrace_append hprefix tailTrace_3115194
  have hstable : (prefixWord ++ tailWord_3115194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115194).length < 2 ^ (prefixWord ++ tailWord_3115194).sum := by decide
  have hdescent : baseEnd_3115194 < baseStart_3115194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115196 : List Nat := [2, 2, 2, 3, 3, 2, 2, 6]
def baseStart_3115196 : Nat := 118140960795 + 3115196 * 2 ^ 59
def prefixEnd_3115196 : Nat := 4983230072969 + 3 ^ 40 * 3115196 * 2
def baseEnd_3115196 : Nat := 118488361552866593705443

theorem tailTrace_3115196 : CollatzResearch.WordTrace tailWord_3115196 prefixEnd_3115196 118488361552866593705443 := by
  unfold tailWord_3115196
  simp only [CollatzResearch.WordTrace]
  refine ⟨56810266211092199982294721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75747021614789599976392961 56810266211092199982294721)
  ·
    refine ⟨42607699658319149986721041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56810266211092199982294721 42607699658319149986721041)
    ·
      refine ⟨31955774743739362490040781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42607699658319149986721041 31955774743739362490040781)
      ·
        refine ⟨11983415528902260933765293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31955774743739362490040781 11983415528902260933765293)
        ·
          refine ⟨4493780823338347850161985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11983415528902260933765293 4493780823338347850161985)
          ·
            refine ⟨3370335617503760887621489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4493780823338347850161985 3370335617503760887621489)
            ·
              refine ⟨2527751713127820665716117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370335617503760887621489 2527751713127820665716117)
              ·
                refine ⟨118488361552866593705443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2527751713127820665716117 118488361552866593705443)
                ·
                  rfl

theorem cell22_3115196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 6].length) (baseStart_3115196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115196 prefixEnd_3115196 := by exact prefixLift 3115196
  have htrace : WordTrace (prefixWord ++ tailWord_3115196) baseStart_3115196 baseEnd_3115196 := by
    simpa [prefixWord, tailWord_3115196, baseEnd_3115196] using wordTrace_append hprefix tailTrace_3115196
  have hstable : (prefixWord ++ tailWord_3115196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115196).length < 2 ^ (prefixWord ++ tailWord_3115196).sum := by decide
  have hdescent : baseEnd_3115196 < baseStart_3115196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115234 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3115234 : Nat := 118140960795 + 3115234 * 2 ^ 59
def prefixEnd_3115234 : Nat := 4983230072969 + 3 ^ 40 * 3115234 * 2
def baseEnd_3115234 : Nat := 1066408262152379910898871

theorem tailTrace_3115234 : CollatzResearch.WordTrace tailWord_3115234 prefixEnd_3115234 1066408262152379910898871 := by
  unfold tailWord_3115234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28405479599011683113618189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75747945597364488302981837 28405479599011683113618189)
  ·
    refine ⟨10652054849629381167606821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28405479599011683113618189 10652054849629381167606821)
    ·
      refine ⟨1997260284305508968926279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10652054849629381167606821 1997260284305508968926279)
      ·
        refine ⟨2995890426458263453389419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997260284305508968926279 2995890426458263453389419)
        ·
          refine ⟨4493835639687395180084129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2995890426458263453389419 4493835639687395180084129)
          ·
            refine ⟨3370376729765546385063097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4493835639687395180084129 3370376729765546385063097)
            ·
              refine ⟨2527782547324159788797323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370376729765546385063097 2527782547324159788797323)
              ·
                refine ⟨3791673820986239683195985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527782547324159788797323 3791673820986239683195985)
                ·
                  refine ⟨2843755365739679762396989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3791673820986239683195985 2843755365739679762396989)
                  ·
                    refine ⟨1066408262152379910898871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843755365739679762396989 1066408262152379910898871)
                    ·
                      rfl

theorem cell22_3115234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3115234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115234 prefixEnd_3115234 := by exact prefixLift 3115234
  have htrace : WordTrace (prefixWord ++ tailWord_3115234) baseStart_3115234 baseEnd_3115234 := by
    simpa [prefixWord, tailWord_3115234, baseEnd_3115234] using wordTrace_append hprefix tailTrace_3115234
  have hstable : (prefixWord ++ tailWord_3115234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115234).length < 2 ^ (prefixWord ++ tailWord_3115234).sum := by decide
  have hdescent : baseEnd_3115234 < baseStart_3115234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115301 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_3115301 : Nat := 118140960795 + 3115301 * 2 ^ 59
def prefixEnd_3115301 : Nat := 4983230072969 + 3 ^ 40 * 3115301 * 2
def baseEnd_3115301 : Nat := 1066431197621614069473665

theorem tailTrace_3115301 : CollatzResearch.WordTrace tailWord_3115301 prefixEnd_3115301 1066431197621614069473665 := by
  unfold tailWord_3115301
  simp only [CollatzResearch.WordTrace]
  refine ⟨113624362086804002897161757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75749574724536001931441171 113624362086804002897161757)
  ·
    refine ⟨42609135782551501086435659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113624362086804002897161757 42609135782551501086435659)
    ·
      refine ⟨63913703673827251629653489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42609135782551501086435659 63913703673827251629653489)
      ·
        refine ⟨47935277755370438722240117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63913703673827251629653489 47935277755370438722240117)
        ·
          refine ⟨4493932289565978630210011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47935277755370438722240117 4493932289565978630210011)
          ·
            refine ⟨6740898434348967945315017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493932289565978630210011 6740898434348967945315017)
            ·
              refine ⟨5055673825761725958986263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6740898434348967945315017 5055673825761725958986263)
              ·
                refine ⟨7583510738642588938479395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5055673825761725958986263 7583510738642588938479395)
                ·
                  refine ⟨11375266107963883407719093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7583510738642588938479395 11375266107963883407719093)
                  ·
                    refine ⟨1066431197621614069473665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11375266107963883407719093 1066431197621614069473665)
                    ·
                      rfl

theorem cell22_3115301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_3115301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115301 prefixEnd_3115301 := by exact prefixLift 3115301
  have htrace : WordTrace (prefixWord ++ tailWord_3115301) baseStart_3115301 baseEnd_3115301 := by
    simpa [prefixWord, tailWord_3115301, baseEnd_3115301] using wordTrace_append hprefix tailTrace_3115301
  have hstable : (prefixWord ++ tailWord_3115301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115301).length < 2 ^ (prefixWord ++ tailWord_3115301).sum := by decide
  have hdescent : baseEnd_3115301 < baseStart_3115301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115312 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_3115312 : Nat := 118140960795 + 3115312 * 2 ^ 59
def prefixEnd_3115312 : Nat := 4983230072969 + 3 ^ 40 * 3115312 * 2
def baseEnd_3115312 : Nat := 1066434963146413707448631

theorem tailTrace_3115312 : CollatzResearch.WordTrace tailWord_3115312 prefixEnd_3115312 1066434963146413707448631 := by
  unfold tailWord_3115312
  simp only [CollatzResearch.WordTrace]
  refine ⟨56812381644882075887906095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75749842193176101183874793 56812381644882075887906095)
  ·
    refine ⟨85218572467323113831859143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56812381644882075887906095 85218572467323113831859143)
    ·
      refine ⟨127827858700984670747788715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85218572467323113831859143 127827858700984670747788715)
      ·
        refine ⟨191741788051477006121683073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127827858700984670747788715 191741788051477006121683073)
        ·
          refine ⟨143806341038607754591262305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191741788051477006121683073 143806341038607754591262305)
          ·
            refine ⟨107854755778955815943446729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143806341038607754591262305 107854755778955815943446729)
            ·
              refine ⟨80891066834216861957585047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107854755778955815943446729 80891066834216861957585047)
              ·
                refine ⟨121336600251325292936377571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80891066834216861957585047 121336600251325292936377571)
                ·
                  refine ⟨182004900376987939404566357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121336600251325292936377571 182004900376987939404566357)
                  ·
                    refine ⟨1066434963146413707448631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182004900376987939404566357 1066434963146413707448631)
                    ·
                      rfl

theorem cell22_3115312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_3115312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115312 prefixEnd_3115312 := by exact prefixLift 3115312
  have htrace : WordTrace (prefixWord ++ tailWord_3115312) baseStart_3115312 baseEnd_3115312 := by
    simpa [prefixWord, tailWord_3115312, baseEnd_3115312] using wordTrace_append hprefix tailTrace_3115312
  have hstable : (prefixWord ++ tailWord_3115312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115312).length < 2 ^ (prefixWord ++ tailWord_3115312).sum := by decide
  have hdescent : baseEnd_3115312 < baseStart_3115312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115316 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3115316 : Nat := 118140960795 + 3115316 * 2 ^ 59
def prefixEnd_3115316 : Nat := 4983230072969 + 3 ^ 40 * 3115316 * 2
def baseEnd_3115316 : Nat := 1066436332428159030348619

theorem tailTrace_3115316 : CollatzResearch.WordTrace tailWord_3115316 prefixEnd_3115316 1066436332428159030348619 := by
  unfold tailWord_3115316
  simp only [CollatzResearch.WordTrace]
  refine ⟨56812454590874830229478901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75749939454499773639305201 56812454590874830229478901)
  ·
    refine ⟨5326167617894515334013647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56812454590874830229478901 5326167617894515334013647)
    ·
      refine ⟨7989251426841773001020471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5326167617894515334013647 7989251426841773001020471)
      ·
        refine ⟨11983877140262659501530707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989251426841773001020471 11983877140262659501530707)
        ·
          refine ⟨17975815710393989252296061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11983877140262659501530707 17975815710393989252296061)
          ·
            refine ⟨6740930891397745969611023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17975815710393989252296061 6740930891397745969611023)
            ·
              refine ⟨10111396337096618954416535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740930891397745969611023 10111396337096618954416535)
              ·
                refine ⟨15167094505644928431624803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10111396337096618954416535 15167094505644928431624803)
                ·
                  refine ⟨22750641758467392647437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15167094505644928431624803 22750641758467392647437205)
                  ·
                    refine ⟨1066436332428159030348619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22750641758467392647437205 1066436332428159030348619)
                    ·
                      rfl

theorem cell22_3115316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3115316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115316 prefixEnd_3115316 := by exact prefixLift 3115316
  have htrace : WordTrace (prefixWord ++ tailWord_3115316) baseStart_3115316 baseEnd_3115316 := by
    simpa [prefixWord, tailWord_3115316, baseEnd_3115316] using wordTrace_append hprefix tailTrace_3115316
  have hstable : (prefixWord ++ tailWord_3115316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115316).length < 2 ^ (prefixWord ++ tailWord_3115316).sum := by decide
  have hdescent : baseEnd_3115316 < baseStart_3115316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115346 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3115346 : Nat := 118140960795 + 3115346 * 2 ^ 59
def prefixEnd_3115346 : Nat := 4983230072969 + 3 ^ 40 * 3115346 * 2
def baseEnd_3115346 : Nat := 1066446602041248952098527

theorem tailTrace_3115346 : CollatzResearch.WordTrace tailWord_3115346 prefixEnd_3115346 1066446602041248952098527 := by
  unfold tailWord_3115346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28406500842910243895637473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75750668914427317055033261 28406500842910243895637473)
  ·
    refine ⟨21304875632182682921728105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28406500842910243895637473 21304875632182682921728105)
    ·
      refine ⟨15978656724137012191296079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21304875632182682921728105 15978656724137012191296079)
      ·
        refine ⟨23967985086205518286944119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15978656724137012191296079 23967985086205518286944119)
        ·
          refine ⟨35951977629308277430416179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23967985086205518286944119 35951977629308277430416179)
          ·
            refine ⟨53927966443962416145624269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35951977629308277430416179 53927966443962416145624269)
            ·
              refine ⟨20222987416485906054609101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53927966443962416145624269 20222987416485906054609101)
              ·
                refine ⟨7583620281182214770478413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20222987416485906054609101 7583620281182214770478413)
                ·
                  refine ⟨2843857605443330538929405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7583620281182214770478413 2843857605443330538929405)
                  ·
                    refine ⟨1066446602041248952098527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843857605443330538929405 1066446602041248952098527)
                    ·
                      rfl

theorem cell22_3115346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3115346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115346 prefixEnd_3115346 := by exact prefixLift 3115346
  have htrace : WordTrace (prefixWord ++ tailWord_3115346) baseStart_3115346 baseEnd_3115346 := by
    simpa [prefixWord, tailWord_3115346, baseEnd_3115346] using wordTrace_append hprefix tailTrace_3115346
  have hstable : (prefixWord ++ tailWord_3115346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115346).length < 2 ^ (prefixWord ++ tailWord_3115346).sum := by decide
  have hdescent : baseEnd_3115346 < baseStart_3115346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115359 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 5]
def baseStart_3115359 : Nat := 118140960795 + 3115359 * 2 ^ 59
def prefixEnd_3115359 : Nat := 4983230072969 + 3 ^ 40 * 3115359 * 2
def baseEnd_3115359 : Nat := 355483684068973750507829

theorem tailTrace_3115359 : CollatzResearch.WordTrace tailWord_3115359 prefixEnd_3115359 355483684068973750507829 := by
  unfold tailWord_3115359
  simp only [CollatzResearch.WordTrace]
  refine ⟨113626477520593878802773131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75750985013729252535182087 113626477520593878802773131)
  ·
    refine ⟨170439716280890818204159697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113626477520593878802773131 170439716280890818204159697)
    ·
      refine ⟨127829787210668113653119773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170439716280890818204159697 127829787210668113653119773)
      ·
        refine ⟨47936170204000542619919915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127829787210668113653119773 47936170204000542619919915)
        ·
          refine ⟨71904255306000813929879873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47936170204000542619919915 71904255306000813929879873)
          ·
            refine ⟨53928191479500610447409905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71904255306000813929879873 53928191479500610447409905)
            ·
              refine ⟨40446143609625457835557429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53928191479500610447409905 40446143609625457835557429)
              ·
                refine ⟨3791825963402386672083509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40446143609625457835557429 3791825963402386672083509)
                ·
                  refine ⟨355483684068973750507829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3791825963402386672083509 355483684068973750507829)
                  ·
                    rfl

theorem cell22_3115359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 5].length) (baseStart_3115359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115359 prefixEnd_3115359 := by exact prefixLift 3115359
  have htrace : WordTrace (prefixWord ++ tailWord_3115359) baseStart_3115359 baseEnd_3115359 := by
    simpa [prefixWord, tailWord_3115359, baseEnd_3115359] using wordTrace_append hprefix tailTrace_3115359
  have hstable : (prefixWord ++ tailWord_3115359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115359).length < 2 ^ (prefixWord ++ tailWord_3115359).sum := by decide
  have hdescent : baseEnd_3115359 < baseStart_3115359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115449 : List Nat := [1, 2, 1, 4, 3, 11]
def baseStart_3115449 : Nat := 118140960795 + 3115449 * 2 ^ 59
def prefixEnd_3115449 : Nat := 4983230072969 + 3 ^ 40 * 3115449 * 2
def baseEnd_3115449 : Nat := 13166442728965321194731

theorem tailTrace_3115449 : CollatzResearch.WordTrace tailWord_3115449 prefixEnd_3115449 13166442728965321194731 := by
  unfold tailWord_3115449
  simp only [CollatzResearch.WordTrace]
  refine ⟨113629760090267824173549401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75753173393511882782366267 113629760090267824173549401)
  ·
    refine ⟨85222320067700868130162051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113629760090267824173549401 85222320067700868130162051)
    ·
      refine ⟨127833480101551302195243077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85222320067700868130162051 127833480101551302195243077)
      ·
        refine ⟨23968777519040869161608077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127833480101551302195243077 23968777519040869161608077)
        ·
          refine ⟨8988291569640325935603029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23968777519040869161608077 8988291569640325935603029)
          ·
            refine ⟨13166442728965321194731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8988291569640325935603029 13166442728965321194731)
            ·
              rfl

theorem cell22_3115449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 11].length) (baseStart_3115449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115449 prefixEnd_3115449 := by exact prefixLift 3115449
  have htrace : WordTrace (prefixWord ++ tailWord_3115449) baseStart_3115449 baseEnd_3115449 := by
    simpa [prefixWord, tailWord_3115449, baseEnd_3115449] using wordTrace_append hprefix tailTrace_3115449
  have hstable : (prefixWord ++ tailWord_3115449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115449).length < 2 ^ (prefixWord ++ tailWord_3115449).sum := by decide
  have hdescent : baseEnd_3115449 < baseStart_3115449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115453 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_3115453 : Nat := 118140960795 + 3115453 * 2 ^ 59
def prefixEnd_3115453 : Nat := 4983230072969 + 3 ^ 40 * 3115453 * 2
def baseEnd_3115453 : Nat := 1066483230327936339673199

theorem tailTrace_3115453 : CollatzResearch.WordTrace tailWord_3115453 prefixEnd_3115453 1066483230327936339673199 := by
  unfold tailWord_3115453
  simp only [CollatzResearch.WordTrace]
  refine ⟨113629905982253332856695013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75753270654835555237796675 113629905982253332856695013)
  ·
    refine ⟨21305607371672499910630315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113629905982253332856695013 21305607371672499910630315)
    ·
      refine ⟨31958411057508749865945473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21305607371672499910630315 31958411057508749865945473)
      ·
        refine ⟨23968808293131562399459105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31958411057508749865945473 23968808293131562399459105)
        ·
          refine ⟨17976606219848671799594329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23968808293131562399459105 17976606219848671799594329)
          ·
            refine ⟨13482454664886503849695747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17976606219848671799594329 13482454664886503849695747)
            ·
              refine ⟨20223681997329755774543621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13482454664886503849695747 20223681997329755774543621)
              ·
                refine ⟨3791940374499329207726929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20223681997329755774543621 3791940374499329207726929)
                ·
                  refine ⟨2843955280874496905795197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3791940374499329207726929 2843955280874496905795197)
                  ·
                    refine ⟨1066483230327936339673199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2843955280874496905795197 1066483230327936339673199)
                    ·
                      rfl

theorem cell22_3115453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_3115453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115453 prefixEnd_3115453 := by exact prefixLift 3115453
  have htrace : WordTrace (prefixWord ++ tailWord_3115453) baseStart_3115453 baseEnd_3115453 := by
    simpa [prefixWord, tailWord_3115453, baseEnd_3115453] using wordTrace_append hprefix tailTrace_3115453
  have hstable : (prefixWord ++ tailWord_3115453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115453).length < 2 ^ (prefixWord ++ tailWord_3115453).sum := by decide
  have hdescent : baseEnd_3115453 < baseStart_3115453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115601 : List Nat := [1, 2, 2, 1, 3, 3, 2, 8]
def baseStart_3115601 : Nat := 118140960795 + 3115601 * 2 ^ 59
def prefixEnd_3115601 : Nat := 4983230072969 + 3 ^ 40 * 3115601 * 2
def baseEnd_3115601 : Nat := 118503765972501476330305

theorem tailTrace_3115601 : CollatzResearch.WordTrace tailWord_3115601 prefixEnd_3115601 118503765972501476330305 := by
  unfold tailWord_3115601
  simp only [CollatzResearch.WordTrace]
  refine ⟨113635303985717154133082657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75756869323811436088721771 113635303985717154133082657)
  ·
    refine ⟨85226477989287865599811993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113635303985717154133082657 85226477989287865599811993)
    ·
      refine ⟨63919858491965899199858995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85226477989287865599811993 63919858491965899199858995)
      ·
        refine ⟨95879787737948848799788493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63919858491965899199858995 95879787737948848799788493)
        ·
          refine ⟨35954920401730818299920685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95879787737948848799788493 35954920401730818299920685)
          ·
            refine ⟨13483095150649056862470257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35954920401730818299920685 13483095150649056862470257)
            ·
              refine ⟨10112321362986792646852693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13483095150649056862470257 10112321362986792646852693)
              ·
                refine ⟨118503765972501476330305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10112321362986792646852693 118503765972501476330305)
                ·
                  rfl

theorem cell22_3115601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 8].length) (baseStart_3115601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115601 prefixEnd_3115601 := by exact prefixLift 3115601
  have htrace : WordTrace (prefixWord ++ tailWord_3115601) baseStart_3115601 baseEnd_3115601 := by
    simpa [prefixWord, tailWord_3115601, baseEnd_3115601] using wordTrace_append hprefix tailTrace_3115601
  have hstable : (prefixWord ++ tailWord_3115601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115601).length < 2 ^ (prefixWord ++ tailWord_3115601).sum := by decide
  have hdescent : baseEnd_3115601 < baseStart_3115601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115618 : List Nat := [3, 3, 2, 3, 11]
def baseStart_3115618 : Nat := 118140960795 + 3115618 * 2 ^ 59
def prefixEnd_3115618 : Nat := 4983230072969 + 3 ^ 40 * 3115618 * 2
def baseEnd_3115618 : Nat := 4389052317695188927151

theorem tailTrace_3115618 : CollatzResearch.WordTrace tailWord_3115618 prefixEnd_3115618 4389052317695188927151 := by
  unfold tailWord_3115618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408981006663891509112877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75757282684437044024301005 28408981006663891509112877)
  ·
    refine ⟨10653367877498959315917329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28408981006663891509112877 10653367877498959315917329)
    ·
      refine ⟨7990025908124219486937997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10653367877498959315917329 7990025908124219486937997)
      ·
        refine ⟨2996259715546582307601749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7990025908124219486937997 2996259715546582307601749)
        ·
          refine ⟨4389052317695188927151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2996259715546582307601749 4389052317695188927151)
          ·
            rfl

theorem cell22_3115618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 11].length) (baseStart_3115618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115618 prefixEnd_3115618 := by exact prefixLift 3115618
  have htrace : WordTrace (prefixWord ++ tailWord_3115618) baseStart_3115618 baseEnd_3115618 := by
    simpa [prefixWord, tailWord_3115618, baseEnd_3115618] using wordTrace_append hprefix tailTrace_3115618
  have hstable : (prefixWord ++ tailWord_3115618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115618).length < 2 ^ (prefixWord ++ tailWord_3115618).sum := by decide
  have hdescent : baseEnd_3115618 < baseStart_3115618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115624 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 4]
def baseStart_3115624 : Nat := 118140960795 + 3115624 * 2 ^ 59
def prefixEnd_3115624 : Nat := 4983230072969 + 3 ^ 40 * 3115624 * 2
def baseEnd_3115624 : Nat := 355513922374182964549225

theorem tailTrace_3115624 : CollatzResearch.WordTrace tailWord_3115624 prefixEnd_3115624 355513922374182964549225 := by
  unfold tailWord_3115624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56818071432316914530584963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75757428576422552707446617 56818071432316914530584963)
  ·
    refine ⟨85227107148475371795877445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56818071432316914530584963 85227107148475371795877445)
    ·
      refine ⟨15980082590339132211727021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85227107148475371795877445 15980082590339132211727021)
      ·
        refine ⟨5992530971377174579397633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15980082590339132211727021 5992530971377174579397633)
        ·
          refine ⟨4494398228532880934548225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5992530971377174579397633 4494398228532880934548225)
          ·
            refine ⟨3370798671399660700911169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494398228532880934548225 3370798671399660700911169)
            ·
              refine ⟨2528099003549745525683377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3370798671399660700911169 2528099003549745525683377)
              ·
                refine ⟨1896074252662309144262533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528099003549745525683377 1896074252662309144262533)
                ·
                  refine ⟨355513922374182964549225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1896074252662309144262533 355513922374182964549225)
                  ·
                    rfl

theorem cell22_3115624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 4].length) (baseStart_3115624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115624 prefixEnd_3115624 := by exact prefixLift 3115624
  have htrace : WordTrace (prefixWord ++ tailWord_3115624) baseStart_3115624 baseEnd_3115624 := by
    simpa [prefixWord, tailWord_3115624, baseEnd_3115624] using wordTrace_append hprefix tailTrace_3115624
  have hstable : (prefixWord ++ tailWord_3115624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115624).length < 2 ^ (prefixWord ++ tailWord_3115624).sum := by decide
  have hdescent : baseEnd_3115624 < baseStart_3115624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115631 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3115631 : Nat := 118140960795 + 3115631 * 2 ^ 59
def prefixEnd_3115631 : Nat := 4983230072969 + 3 ^ 40 * 3115631 * 2
def baseEnd_3115631 : Nat := 1066544163365603208722653

theorem tailTrace_3115631 : CollatzResearch.WordTrace tailWord_3115631 prefixEnd_3115631 1066544163365603208722653 := by
  unfold tailWord_3115631
  simp only [CollatzResearch.WordTrace]
  refine ⟨113636398175608469256674747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75757598783738979504449831 113636398175608469256674747)
  ·
    refine ⟨170454597263412703885012121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113636398175608469256674747 170454597263412703885012121)
    ·
      refine ⟨127840947947559527913759091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170454597263412703885012121 127840947947559527913759091)
      ·
        refine ⟨191761421921339291870638637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127840947947559527913759091 191761421921339291870638637)
        ·
          refine ⟨71910533220502234451489489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191761421921339291870638637 71910533220502234451489489)
          ·
            refine ⟨53932899915376675838617117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71910533220502234451489489 53932899915376675838617117)
            ·
              refine ⟨20224837468266253439481419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53932899915376675838617117 20224837468266253439481419)
              ·
                refine ⟨30337256202399380159222129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20224837468266253439481419 30337256202399380159222129)
                ·
                  refine ⟨22752942151799535119416597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30337256202399380159222129 22752942151799535119416597)
                  ·
                    refine ⟨1066544163365603208722653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22752942151799535119416597 1066544163365603208722653)
                    ·
                      rfl

theorem cell22_3115631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3115631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115631 prefixEnd_3115631 := by exact prefixLift 3115631
  have htrace : WordTrace (prefixWord ++ tailWord_3115631) baseStart_3115631 baseEnd_3115631 := by
    simpa [prefixWord, tailWord_3115631, baseEnd_3115631] using wordTrace_append hprefix tailTrace_3115631
  have hstable : (prefixWord ++ tailWord_3115631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115631).length < 2 ^ (prefixWord ++ tailWord_3115631).sum := by decide
  have hdescent : baseEnd_3115631 < baseStart_3115631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115708 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 6]
def baseStart_3115708 : Nat := 118140960795 + 3115708 * 2 ^ 59
def prefixEnd_3115708 : Nat := 4983230072969 + 3 ^ 40 * 3115708 * 2
def baseEnd_3115708 : Nat := 355523507346400224849139

theorem tailTrace_3115708 : CollatzResearch.WordTrace tailWord_3115708 prefixEnd_3115708 355523507346400224849139 := by
  unfold tailWord_3115708
  simp only [CollatzResearch.WordTrace]
  refine ⟨56819603298164755703613889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75759471064219674271485185 56819603298164755703613889)
  ·
    refine ⟨42614702473623566777710417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56819603298164755703613889 42614702473623566777710417)
    ·
      refine ⟨31961026855217675083282813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42614702473623566777710417 31961026855217675083282813)
      ·
        refine ⟨11985385070706628156231055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31961026855217675083282813 11985385070706628156231055)
        ·
          refine ⟨17978077606059942234346583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11985385070706628156231055 17978077606059942234346583)
          ·
            refine ⟨26967116409089913351519875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17978077606059942234346583 26967116409089913351519875)
            ·
              refine ⟨40450674613634870027279813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26967116409089913351519875 40450674613634870027279813)
              ·
                refine ⟨7584501490056538130114965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40450674613634870027279813 7584501490056538130114965)
                ·
                  refine ⟨355523507346400224849139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7584501490056538130114965 355523507346400224849139)
                  ·
                    rfl

theorem cell22_3115708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_3115708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115708 prefixEnd_3115708 := by exact prefixLift 3115708
  have htrace : WordTrace (prefixWord ++ tailWord_3115708) baseStart_3115708 baseEnd_3115708 := by
    simpa [prefixWord, tailWord_3115708, baseEnd_3115708] using wordTrace_append hprefix tailTrace_3115708
  have hstable : (prefixWord ++ tailWord_3115708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115708).length < 2 ^ (prefixWord ++ tailWord_3115708).sum := by decide
  have hdescent : baseEnd_3115708 < baseStart_3115708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115757 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_3115757 : Nat := 118140960795 + 3115757 * 2 ^ 59
def prefixEnd_3115757 : Nat := 4983230072969 + 3 ^ 40 * 3115757 * 2
def baseEnd_3115757 : Nat := 1066587295740580880072267

theorem tailTrace_3115757 : CollatzResearch.WordTrace tailWord_3115757 prefixEnd_3115757 1066587295740580880072267 := by
  unfold tailWord_3115757
  simp only [CollatzResearch.WordTrace]
  refine ⟨113640993773151992775761525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75760662515434661850507683 113640993773151992775761525)
  ·
    refine ⟨10653843166232999322727643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113640993773151992775761525 10653843166232999322727643)
    ·
      refine ⟨15980764749349498984091465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10653843166232999322727643 15980764749349498984091465)
      ·
        refine ⟨11985573562012124238068599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15980764749349498984091465 11985573562012124238068599)
        ·
          refine ⟨17978360343018186357102899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11985573562012124238068599 17978360343018186357102899)
          ·
            refine ⟨26967540514527279535654349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17978360343018186357102899 26967540514527279535654349)
            ·
              refine ⟨10112827692947729825870381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26967540514527279535654349 10112827692947729825870381)
              ·
                refine ⟨3792310384855398684701393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10112827692947729825870381 3792310384855398684701393)
                ·
                  refine ⟨2844232788641549013526045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3792310384855398684701393 2844232788641549013526045)
                  ·
                    refine ⟨1066587295740580880072267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2844232788641549013526045 1066587295740580880072267)
                    ·
                      rfl

theorem cell22_3115757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_3115757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115757 prefixEnd_3115757 := by exact prefixLift 3115757
  have htrace : WordTrace (prefixWord ++ tailWord_3115757) baseStart_3115757 baseEnd_3115757 := by
    simpa [prefixWord, tailWord_3115757, baseEnd_3115757] using wordTrace_append hprefix tailTrace_3115757
  have hstable : (prefixWord ++ tailWord_3115757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115757).length < 2 ^ (prefixWord ++ tailWord_3115757).sum := by decide
  have hdescent : baseEnd_3115757 < baseStart_3115757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115843 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 8]
def baseStart_3115843 : Nat := 118140960795 + 3115843 * 2 ^ 59
def prefixEnd_3115843 : Nat := 4983230072969 + 3 ^ 40 * 3115843 * 2
def baseEnd_3115843 : Nat := 355538911766035107474001

theorem tailTrace_3115843 : CollatzResearch.WordTrace tailWord_3115843 prefixEnd_3115843 355538911766035107474001 := by
  unfold tailWord_3115843
  simp only [CollatzResearch.WordTrace]
  refine ⟨113644130450840429463392183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75762753633893619642261455 113644130450840429463392183)
  ·
    refine ⟨170466195676260644195088275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113644130450840429463392183 170466195676260644195088275)
    ·
      refine ⟨255699293514390966292632413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170466195676260644195088275 255699293514390966292632413)
      ·
        refine ⟨95887235067896612359737155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255699293514390966292632413 95887235067896612359737155)
        ·
          refine ⟨143830852601844918539605733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95887235067896612359737155 143830852601844918539605733)
          ·
            refine ⟨26968284862845922226176075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143830852601844918539605733 26968284862845922226176075)
            ·
              refine ⟨40452427294268883339264113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26968284862845922226176075 40452427294268883339264113)
              ·
                refine ⟨30339320470701662504448085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40452427294268883339264113 30339320470701662504448085)
                ·
                  refine ⟨355538911766035107474001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30339320470701662504448085 355538911766035107474001)
                  ·
                    rfl

theorem cell22_3115843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_3115843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115843 prefixEnd_3115843 := by exact prefixLift 3115843
  have htrace : WordTrace (prefixWord ++ tailWord_3115843) baseStart_3115843 baseEnd_3115843 := by
    simpa [prefixWord, tailWord_3115843, baseEnd_3115843] using wordTrace_append hprefix tailTrace_3115843
  have hstable : (prefixWord ++ tailWord_3115843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115843).length < 2 ^ (prefixWord ++ tailWord_3115843).sum := by decide
  have hdescent : baseEnd_3115843 < baseStart_3115843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115890 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_3115890 : Nat := 118140960795 + 3115890 * 2 ^ 59
def prefixEnd_3115890 : Nat := 4983230072969 + 3 ^ 40 * 3115890 * 2
def baseEnd_3115890 : Nat := 1066632824358612866496859

theorem tailTrace_3115890 : CollatzResearch.WordTrace tailWord_3115890 prefixEnd_3115890 1066632824358612866496859 := by
  unfold tailWord_3115890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28411461170417539122588281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75763896454446770993568749 28411461170417539122588281)
  ·
    refine ⟨21308595877813154341941211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28411461170417539122588281 21308595877813154341941211)
    ·
      refine ⟨31962893816719731512911817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21308595877813154341941211 31962893816719731512911817)
      ·
        refine ⟨23972170362539798634683863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31962893816719731512911817 23972170362539798634683863)
        ·
          refine ⟨35958255543809697952025795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23972170362539798634683863 35958255543809697952025795)
          ·
            refine ⟨53937383315714546928038693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35958255543809697952025795 53937383315714546928038693)
            ·
              refine ⟨10113259371696477549007255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53937383315714546928038693 10113259371696477549007255)
              ·
                refine ⟨15169889057544716323510883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10113259371696477549007255 15169889057544716323510883)
                ·
                  refine ⟨22754833586317074485266325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15169889057544716323510883 22754833586317074485266325)
                  ·
                    refine ⟨1066632824358612866496859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22754833586317074485266325 1066632824358612866496859)
                    ·
                      rfl

theorem cell22_3115890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_3115890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115890 prefixEnd_3115890 := by exact prefixLift 3115890
  have htrace : WordTrace (prefixWord ++ tailWord_3115890) baseStart_3115890 baseEnd_3115890 := by
    simpa [prefixWord, tailWord_3115890, baseEnd_3115890] using wordTrace_append hprefix tailTrace_3115890
  have hstable : (prefixWord ++ tailWord_3115890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115890).length < 2 ^ (prefixWord ++ tailWord_3115890).sum := by decide
  have hdescent : baseEnd_3115890 < baseStart_3115890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3115982 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3115982 : Nat := 118140960795 + 3115982 * 2 ^ 59
def prefixEnd_3115982 : Nat := 4983230072969 + 3 ^ 40 * 3115982 * 2
def baseEnd_3115982 : Nat := 1066664317838755293196577

theorem tailTrace_3115982 : CollatzResearch.WordTrace tailWord_3115982 prefixEnd_3115982 1066664317838755293196577 := by
  unfold tailWord_3115982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206150024667107025337775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75766133464891237468468133 14206150024667107025337775)
  ·
    refine ⟨21309225037000660538006663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14206150024667107025337775 21309225037000660538006663)
    ·
      refine ⟨31963837555500990807009995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21309225037000660538006663 31963837555500990807009995)
      ·
        refine ⟨47945756333251486210514993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31963837555500990807009995 47945756333251486210514993)
        ·
          refine ⟨35959317249938614657886245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47945756333251486210514993 35959317249938614657886245)
          ·
            refine ⟨6742371984363490248353671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35959317249938614657886245 6742371984363490248353671)
            ·
              refine ⟨10113557976545235372530507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742371984363490248353671 10113557976545235372530507)
              ·
                refine ⟨15170336964817853058795761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10113557976545235372530507 15170336964817853058795761)
                ·
                  refine ⟨11377752723613389794096821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15170336964817853058795761 11377752723613389794096821)
                  ·
                    refine ⟨1066664317838755293196577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11377752723613389794096821 1066664317838755293196577)
                    ·
                      rfl

theorem cell22_3115982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3115982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3115982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3115982 prefixEnd_3115982 := by exact prefixLift 3115982
  have htrace : WordTrace (prefixWord ++ tailWord_3115982) baseStart_3115982 baseEnd_3115982 := by
    simpa [prefixWord, tailWord_3115982, baseEnd_3115982] using wordTrace_append hprefix tailTrace_3115982
  have hstable : (prefixWord ++ tailWord_3115982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3115982).length < 2 ^ (prefixWord ++ tailWord_3115982).sum := by decide
  have hdescent : baseEnd_3115982 < baseStart_3115982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3115982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116018 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_3116018 : Nat := 118140960795 + 3116018 * 2 ^ 59
def prefixEnd_3116018 : Nat := 4983230072969 + 3 ^ 40 * 3116018 * 2
def baseEnd_3116018 : Nat := 355558880458154399765489

theorem tailTrace_3116018 : CollatzResearch.WordTrace tailWord_3116018 prefixEnd_3116018 355558880458154399765489 := by
  unfold tailWord_3116018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28412628306301608587753177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75767008816804289567341805 28412628306301608587753177)
  ·
    refine ⟨21309471229726206440814883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28412628306301608587753177 21309471229726206440814883)
    ·
      refine ⟨31964206844589309661222325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21309471229726206440814883 31964206844589309661222325)
      ·
        refine ⟨2996644391680247780739593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31964206844589309661222325 2996644391680247780739593)
        ·
          refine ⟨2247483293760185835554695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2996644391680247780739593 2247483293760185835554695)
          ·
            refine ⟨3371224940640278753332043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247483293760185835554695 3371224940640278753332043)
            ·
              refine ⟨5056837410960418129998065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371224940640278753332043 5056837410960418129998065)
              ·
                refine ⟨3792628058220313597498549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056837410960418129998065 3792628058220313597498549)
                ·
                  refine ⟨355558880458154399765489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3792628058220313597498549 355558880458154399765489)
                  ·
                    rfl

theorem cell22_3116018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_3116018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116018 prefixEnd_3116018 := by exact prefixLift 3116018
  have htrace : WordTrace (prefixWord ++ tailWord_3116018) baseStart_3116018 baseEnd_3116018 := by
    simpa [prefixWord, tailWord_3116018, baseEnd_3116018] using wordTrace_append hprefix tailTrace_3116018
  have hstable : (prefixWord ++ tailWord_3116018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116018).length < 2 ^ (prefixWord ++ tailWord_3116018).sum := by decide
  have hdescent : baseEnd_3116018 < baseStart_3116018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116042 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3116042 : Nat := 118140960795 + 3116042 * 2 ^ 59
def prefixEnd_3116042 : Nat := 4983230072969 + 3 ^ 40 * 3116042 * 2
def baseEnd_3116042 : Nat := 1066684857064935136696393

theorem tailTrace_3116042 : CollatzResearch.WordTrace tailWord_3116042 prefixEnd_3116042 1066684857064935136696393 := by
  unfold tailWord_3116042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28412847144279871612471595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75767592384746324299924253 28412847144279871612471595)
  ·
    refine ⟨42619270716419807418707393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28412847144279871612471595 42619270716419807418707393)
    ·
      refine ⟨31964453037314855564030545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42619270716419807418707393 31964453037314855564030545)
      ·
        refine ⟨23973339777986141673022909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31964453037314855564030545 23973339777986141673022909)
        ·
          refine ⟨8990002416744803127383591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23973339777986141673022909 8990002416744803127383591)
          ·
            refine ⟨13485003625117204691075387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8990002416744803127383591 13485003625117204691075387)
            ·
              refine ⟨20227505437675807036613081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13485003625117204691075387 20227505437675807036613081)
              ·
                refine ⟨15170629078256855277459811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20227505437675807036613081 15170629078256855277459811)
                ·
                  refine ⟨22755943617385282916189717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15170629078256855277459811 22755943617385282916189717)
                  ·
                    refine ⟨1066684857064935136696393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22755943617385282916189717 1066684857064935136696393)
                    ·
                      rfl

theorem cell22_3116042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3116042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116042 prefixEnd_3116042 := by exact prefixLift 3116042
  have htrace : WordTrace (prefixWord ++ tailWord_3116042) baseStart_3116042 baseEnd_3116042 := by
    simpa [prefixWord, tailWord_3116042, baseEnd_3116042] using wordTrace_append hprefix tailTrace_3116042
  have hstable : (prefixWord ++ tailWord_3116042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116042).length < 2 ^ (prefixWord ++ tailWord_3116042).sum := by decide
  have hdescent : baseEnd_3116042 < baseStart_3116042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116044 : List Nat := [2, 2, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_3116044 : Nat := 118140960795 + 3116044 * 2 ^ 59
def prefixEnd_3116044 : Nat := 4983230072969 + 3 ^ 40 * 3116044 * 2
def baseEnd_3116044 : Nat := 1066685541705807798146387

theorem tailTrace_3116044 : CollatzResearch.WordTrace tailWord_3116044 prefixEnd_3116044 1066685541705807798146387 := by
  unfold tailWord_3116044
  simp only [CollatzResearch.WordTrace]
  refine ⟨56825730761556120395729593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75767641015408160527639457 56825730761556120395729593)
  ·
    refine ⟨42619298071167090296797195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56825730761556120395729593 42619298071167090296797195)
    ·
      refine ⟨63928947106750635445195793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42619298071167090296797195 63928947106750635445195793)
      ·
        refine ⟨47946710330062976583896845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63928947106750635445195793 47946710330062976583896845)
        ·
          refine ⟨17980016373773616218961317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47946710330062976583896845 17980016373773616218961317)
          ·
            refine ⟨3371253070082553041055247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17980016373773616218961317 3371253070082553041055247)
            ·
              refine ⟨5056879605123829561582871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371253070082553041055247 5056879605123829561582871)
              ·
                refine ⟨7585319407685744342374307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5056879605123829561582871 7585319407685744342374307)
                ·
                  refine ⟨11377979111528616513561461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7585319407685744342374307 11377979111528616513561461)
                  ·
                    refine ⟨1066685541705807798146387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11377979111528616513561461 1066685541705807798146387)
                    ·
                      rfl

theorem cell22_3116044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_3116044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116044 prefixEnd_3116044 := by exact prefixLift 3116044
  have htrace : WordTrace (prefixWord ++ tailWord_3116044) baseStart_3116044 baseEnd_3116044 := by
    simpa [prefixWord, tailWord_3116044, baseEnd_3116044] using wordTrace_append hprefix tailTrace_3116044
  have hstable : (prefixWord ++ tailWord_3116044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116044).length < 2 ^ (prefixWord ++ tailWord_3116044).sum := by decide
  have hdescent : baseEnd_3116044 < baseStart_3116044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116057 : List Nat := [1, 2, 1, 2, 1, 1, 8, 6]
def baseStart_3116057 : Nat := 118140960795 + 3116057 * 2 ^ 59
def prefixEnd_3116057 : Nat := 4983230072969 + 3 ^ 40 * 3116057 * 2
def baseEnd_3116057 : Nat := 118521110207942233063483

theorem tailTrace_3116057 : CollatzResearch.WordTrace tailWord_3116057 prefixEnd_3116057 118521110207942233063483 := by
  unfold tailWord_3116057
  simp only [CollatzResearch.WordTrace]
  refine ⟨113651935672065144011682425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75767957114710096007788283 113651935672065144011682425)
  ·
    refine ⟨85238951754048858008761819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113651935672065144011682425 85238951754048858008761819)
    ·
      refine ⟨127858427631073287013142729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85238951754048858008761819 127858427631073287013142729)
      ·
        refine ⟨95893820723304965259857047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127858427631073287013142729 95893820723304965259857047)
        ·
          refine ⟨143840731084957447889785571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95893820723304965259857047 143840731084957447889785571)
          ·
            refine ⟨215761096627436171834678357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143840731084957447889785571 215761096627436171834678357)
            ·
              refine ⟨2528450351102767638687637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 215761096627436171834678357 2528450351102767638687637)
              ·
                refine ⟨118521110207942233063483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2528450351102767638687637 118521110207942233063483)
                ·
                  rfl

theorem cell22_3116057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 6].length) (baseStart_3116057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116057 prefixEnd_3116057 := by exact prefixLift 3116057
  have htrace : WordTrace (prefixWord ++ tailWord_3116057) baseStart_3116057 baseEnd_3116057 := by
    simpa [prefixWord, tailWord_3116057, baseEnd_3116057] using wordTrace_append hprefix tailTrace_3116057
  have hstable : (prefixWord ++ tailWord_3116057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116057).length < 2 ^ (prefixWord ++ tailWord_3116057).sum := by decide
  have hdescent : baseEnd_3116057 < baseStart_3116057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116074 : List Nat := [3, 1, 4, 1, 3, 2, 8]
def baseStart_3116074 : Nat := 118140960795 + 3116074 * 2 ^ 59
def prefixEnd_3116074 : Nat := 4983230072969 + 3 ^ 40 * 3116074 * 2
def baseEnd_3116074 : Nat := 39507252271070285922085

theorem tailTrace_3116074 : CollatzResearch.WordTrace tailWord_3116074 prefixEnd_3116074 39507252271070285922085 := by
  unfold tailWord_3116074
  simp only [CollatzResearch.WordTrace]
  refine ⟨28413138928250888978762819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75768370475335703943367517 28413138928250888978762819)
  ·
    refine ⟨42619708392376333468144229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28413138928250888978762819 42619708392376333468144229)
    ·
      refine ⟨7991195323570562525277043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42619708392376333468144229 7991195323570562525277043)
      ·
        refine ⟨11986792985355843787915565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7991195323570562525277043 11986792985355843787915565)
        ·
          refine ⟨4495047369508441420468337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11986792985355843787915565 4495047369508441420468337)
          ·
            refine ⟨3371285527131331065351253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495047369508441420468337 3371285527131331065351253)
            ·
              refine ⟨39507252271070285922085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3371285527131331065351253 39507252271070285922085)
              ·
                rfl

theorem cell22_3116074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 8].length) (baseStart_3116074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116074 prefixEnd_3116074 := by exact prefixLift 3116074
  have htrace : WordTrace (prefixWord ++ tailWord_3116074) baseStart_3116074 baseEnd_3116074 := by
    simpa [prefixWord, tailWord_3116074, baseEnd_3116074] using wordTrace_append hprefix tailTrace_3116074
  have hstable : (prefixWord ++ tailWord_3116074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116074).length < 2 ^ (prefixWord ++ tailWord_3116074).sum := by decide
  have hdescent : baseEnd_3116074 < baseStart_3116074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116164 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3116164 : Nat := 118140960795 + 3116164 * 2 ^ 59
def prefixEnd_3116164 : Nat := 4983230072969 + 3 ^ 40 * 3116164 * 2
def baseEnd_3116164 : Nat := 355575540052722495048673

theorem tailTrace_3116164 : CollatzResearch.WordTrace tailWord_3116164 prefixEnd_3116164 355575540052722495048673 := by
  unfold tailWord_3116164
  simp only [CollatzResearch.WordTrace]
  refine ⟨56827919141338750642913773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75770558855118334190551697 56827919141338750642913773)
  ·
    refine ⟨21310469678002031491092665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56827919141338750642913773 21310469678002031491092665)
    ·
      refine ⟨15982852258501523618319499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21310469678002031491092665 15982852258501523618319499)
      ·
        refine ⟨23974278387752285427479249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15982852258501523618319499 23974278387752285427479249)
        ·
          refine ⟨17980708790814214070609437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23974278387752285427479249 17980708790814214070609437)
          ·
            refine ⟨6742765796555330276478539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17980708790814214070609437 6742765796555330276478539)
            ·
              refine ⟨10114148694832995414717809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742765796555330276478539 10114148694832995414717809)
              ·
                refine ⟨7585611521124746561038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114148694832995414717809 7585611521124746561038357)
                ·
                  refine ⟨355575540052722495048673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7585611521124746561038357 355575540052722495048673)
                  ·
                    rfl

theorem cell22_3116164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3116164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116164 prefixEnd_3116164 := by exact prefixLift 3116164
  have htrace : WordTrace (prefixWord ++ tailWord_3116164) baseStart_3116164 baseEnd_3116164 := by
    simpa [prefixWord, tailWord_3116164, baseEnd_3116164] using wordTrace_append hprefix tailTrace_3116164
  have hstable : (prefixWord ++ tailWord_3116164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116164).length < 2 ^ (prefixWord ++ tailWord_3116164).sum := by decide
  have hdescent : baseEnd_3116164 < baseStart_3116164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116183 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 1, 4]
def baseStart_3116183 : Nat := 118140960795 + 3116183 * 2 ^ 59
def prefixEnd_3116183 : Nat := 4983230072969 + 3 ^ 40 * 3116183 * 2
def baseEnd_3116183 : Nat := 1066733124246457768920961

theorem tailTrace_3116183 : CollatzResearch.WordTrace tailWord_3116183 prefixEnd_3116183 1066733124246457768920961 := by
  unfold tailWord_3116183
  simp only [CollatzResearch.WordTrace]
  refine ⟨113656531269608667530769203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75771020846405778353846135 113656531269608667530769203)
  ·
    refine ⟨170484796904413001296153805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113656531269608667530769203 170484796904413001296153805)
    ·
      refine ⟨63931798839154875486057677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170484796904413001296153805 63931798839154875486057677)
      ·
        refine ⟨23974424564683078307271629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63931798839154875486057677 23974424564683078307271629)
        ·
          refine ⟨8990409211756154365226861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23974424564683078307271629 8990409211756154365226861)
          ·
            refine ⟨3371403454408557886960073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8990409211756154365226861 3371403454408557886960073)
            ·
              refine ⟨2528552590806418415220055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371403454408557886960073 2528552590806418415220055)
              ·
                refine ⟨3792828886209627622830083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528552590806418415220055 3792828886209627622830083)
                ·
                  refine ⟨5689243329314441434245125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3792828886209627622830083 5689243329314441434245125)
                  ·
                    refine ⟨1066733124246457768920961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689243329314441434245125 1066733124246457768920961)
                    ·
                      rfl

theorem cell22_3116183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_3116183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116183 prefixEnd_3116183 := by exact prefixLift 3116183
  have htrace : WordTrace (prefixWord ++ tailWord_3116183) baseStart_3116183 baseEnd_3116183 := by
    simpa [prefixWord, tailWord_3116183, baseEnd_3116183] using wordTrace_append hprefix tailTrace_3116183
  have hstable : (prefixWord ++ tailWord_3116183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116183).length < 2 ^ (prefixWord ++ tailWord_3116183).sum := by decide
  have hdescent : baseEnd_3116183 < baseStart_3116183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116192 : List Nat := [2, 1, 1, 4, 2, 1, 11]
def baseStart_3116192 : Nat := 118140960795 + 3116192 * 2 ^ 59
def prefixEnd_3116192 : Nat := 4983230072969 + 3 ^ 40 * 3116192 * 2
def baseEnd_3116192 : Nat := 39508748338162397979479

theorem tailTrace_3116192 : CollatzResearch.WordTrace tailWord_3116192 prefixEnd_3116192 39508748338162397979479 := by
  unfold tailWord_3116192
  simp only [CollatzResearch.WordTrace]
  refine ⟨56828429763288031033923415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75771239684384041378564553 56828429763288031033923415)
  ·
    refine ⟨85242644644932046550885123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56828429763288031033923415 85242644644932046550885123)
    ·
      refine ⟨127863966967398069826327685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85242644644932046550885123 127863966967398069826327685)
      ·
        refine ⟨23974493806387138092436441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127863966967398069826327685 23974493806387138092436441)
        ·
          refine ⟨17980870354790353569327331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23974493806387138092436441 17980870354790353569327331)
          ·
            refine ⟨26971305532185530353990997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17980870354790353569327331 26971305532185530353990997)
            ·
              refine ⟨39508748338162397979479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26971305532185530353990997 39508748338162397979479)
              ·
                rfl

theorem cell22_3116192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 11].length) (baseStart_3116192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116192 prefixEnd_3116192 := by exact prefixLift 3116192
  have htrace : WordTrace (prefixWord ++ tailWord_3116192) baseStart_3116192 baseEnd_3116192 := by
    simpa [prefixWord, tailWord_3116192, baseEnd_3116192] using wordTrace_append hprefix tailTrace_3116192
  have hstable : (prefixWord ++ tailWord_3116192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116192).length < 2 ^ (prefixWord ++ tailWord_3116192).sum := by decide
  have hdescent : baseEnd_3116192 < baseStart_3116192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116196 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_3116196 : Nat := 118140960795 + 3116196 * 2 ^ 59
def prefixEnd_3116196 : Nat := 4983230072969 + 3 ^ 40 * 3116196 * 2
def baseEnd_3116196 : Nat := 1066737574412130068345921

theorem tailTrace_3116196 : CollatzResearch.WordTrace tailWord_3116196 prefixEnd_3116196 1066737574412130068345921 := by
  unfold tailWord_3116196
  simp only [CollatzResearch.WordTrace]
  refine ⟨56828502709280785375496221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75771336945707713833994961 56828502709280785375496221)
  ·
    refine ⟨21310688515980294515811083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56828502709280785375496221 21310688515980294515811083)
    ·
      refine ⟨31966032773970441773716625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21310688515980294515811083 31966032773970441773716625)
      ·
        refine ⟨23974524580477831330287469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31966032773970441773716625 23974524580477831330287469)
        ·
          refine ⟨8990446717679186748857801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23974524580477831330287469 8990446717679186748857801)
          ·
            refine ⟨6742835038259390061643351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8990446717679186748857801 6742835038259390061643351)
            ·
              refine ⟨10114252557389085092465027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742835038259390061643351 10114252557389085092465027)
              ·
                refine ⟨15171378836083627638697541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10114252557389085092465027 15171378836083627638697541)
                ·
                  refine ⟨2844633531765680182255789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15171378836083627638697541 2844633531765680182255789)
                  ·
                    refine ⟨1066737574412130068345921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2844633531765680182255789 1066737574412130068345921)
                    ·
                      rfl

theorem cell22_3116196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_3116196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116196 prefixEnd_3116196 := by exact prefixLift 3116196
  have htrace : WordTrace (prefixWord ++ tailWord_3116196) baseStart_3116196 baseEnd_3116196 := by
    simpa [prefixWord, tailWord_3116196, baseEnd_3116196] using wordTrace_append hprefix tailTrace_3116196
  have hstable : (prefixWord ++ tailWord_3116196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116196).length < 2 ^ (prefixWord ++ tailWord_3116196).sum := by decide
  have hdescent : baseEnd_3116196 < baseStart_3116196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116271 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 5]
def baseStart_3116271 : Nat := 118140960795 + 3116271 * 2 ^ 59
def prefixEnd_3116271 : Nat := 4983230072969 + 3 ^ 40 * 3116271 * 2
def baseEnd_3116271 : Nat := 355587749481618290906897

theorem tailTrace_3116271 : CollatzResearch.WordTrace tailWord_3116271 prefixEnd_3116271 355587749481618290906897 := by
  unfold tailWord_3116271
  simp only [CollatzResearch.WordTrace]
  refine ⟨113659740893289858559972667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75773160595526572373315111 113659740893289858559972667)
  ·
    refine ⟨170489611339934787839959001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113659740893289858559972667 170489611339934787839959001)
    ·
      refine ⟨127867208504951090879969251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170489611339934787839959001 127867208504951090879969251)
      ·
        refine ⟨191800812757426636319953877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127867208504951090879969251 191800812757426636319953877)
        ·
          refine ⟨4495331549002186788748919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 191800812757426636319953877 4495331549002186788748919)
          ·
            refine ⟨6742997323503280183123379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495331549002186788748919 6742997323503280183123379)
            ·
              refine ⟨10114495985254920274685069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6742997323503280183123379 10114495985254920274685069)
              ·
                refine ⟨3792935994470595103006901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10114495985254920274685069 3792935994470595103006901)
                ·
                  refine ⟨355587749481618290906897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3792935994470595103006901 355587749481618290906897)
                  ·
                    rfl

theorem cell22_3116271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 5].length) (baseStart_3116271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116271 prefixEnd_3116271 := by exact prefixLift 3116271
  have htrace : WordTrace (prefixWord ++ tailWord_3116271) baseStart_3116271 baseEnd_3116271 := by
    simpa [prefixWord, tailWord_3116271, baseEnd_3116271] using wordTrace_append hprefix tailTrace_3116271
  have hstable : (prefixWord ++ tailWord_3116271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116271).length < 2 ^ (prefixWord ++ tailWord_3116271).sum := by decide
  have hdescent : baseEnd_3116271 < baseStart_3116271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116333 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3116333 : Nat := 118140960795 + 3116333 * 2 ^ 59
def prefixEnd_3116333 : Nat := 4983230072969 + 3 ^ 40 * 3116333 * 2
def baseEnd_3116333 : Nat := 355594824103969125890167

theorem tailTrace_3116333 : CollatzResearch.WordTrace tailWord_3116333 prefixEnd_3116333 355594824103969125890167 := by
  unfold tailWord_3116333
  simp only [CollatzResearch.WordTrace]
  refine ⟨113662002219065243148729653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75774668146043495432486435 113662002219065243148729653)
  ·
    refine ⟨10655812708037366545193405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113662002219065243148729653 10655812708037366545193405)
    ·
      refine ⟨3995929765514012454447527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10655812708037366545193405 3995929765514012454447527)
      ·
        refine ⟨5993894648271018681671291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995929765514012454447527 5993894648271018681671291)
        ·
          refine ⟨8990841972406528022506937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5993894648271018681671291 8990841972406528022506937)
          ·
            refine ⟨6743131479304896016880203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8990841972406528022506937 6743131479304896016880203)
            ·
              refine ⟨10114697218957344025320305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6743131479304896016880203 10114697218957344025320305)
              ·
                refine ⟨7586022914218008018990229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10114697218957344025320305 7586022914218008018990229)
                ·
                  refine ⟨355594824103969125890167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7586022914218008018990229 355594824103969125890167)
                  ·
                    rfl

theorem cell22_3116333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3116333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116333 prefixEnd_3116333 := by exact prefixLift 3116333
  have htrace : WordTrace (prefixWord ++ tailWord_3116333) baseStart_3116333 baseEnd_3116333 := by
    simpa [prefixWord, tailWord_3116333, baseEnd_3116333] using wordTrace_append hprefix tailTrace_3116333
  have hstable : (prefixWord ++ tailWord_3116333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116333).length < 2 ^ (prefixWord ++ tailWord_3116333).sum := by decide
  have hdescent : baseEnd_3116333 < baseStart_3116333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116483 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 2, 3]
def baseStart_3116483 : Nat := 118140960795 + 3116483 * 2 ^ 59
def prefixEnd_3116483 : Nat := 4983230072969 + 3 ^ 40 * 3116483 * 2
def baseEnd_3116483 : Nat := 1066835820377356986420041

theorem tailTrace_3116483 : CollatzResearch.WordTrace tailWord_3116483 prefixEnd_3116483 1066835820377356986420041 := by
  unfold tailWord_3116483
  simp only [CollatzResearch.WordTrace]
  refine ⟨113667473168521818766690103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75778315445681212511126735 113667473168521818766690103)
  ·
    refine ⟨170501209752782728150035155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113667473168521818766690103 170501209752782728150035155)
    ·
      refine ⟨255751814629174092225052733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170501209752782728150035155 255751814629174092225052733)
      ·
        refine ⟨95906930485940284584394775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255751814629174092225052733 95906930485940284584394775)
        ·
          refine ⟨143860395728910426876592163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95906930485940284584394775 143860395728910426876592163)
          ·
            refine ⟨215790593593365640314888245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143860395728910426876592163 215790593593365640314888245)
            ·
              refine ⟨20230368149378028779520773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215790593593365640314888245 20230368149378028779520773)
              ·
                refine ⟨3793194028008380396160145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20230368149378028779520773 3793194028008380396160145)
                ·
                  refine ⟨2844895521006285297120109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3793194028008380396160145 2844895521006285297120109)
                  ·
                    refine ⟨1066835820377356986420041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2844895521006285297120109 1066835820377356986420041)
                    ·
                      rfl

theorem cell22_3116483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 3].length) (baseStart_3116483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116483 prefixEnd_3116483 := by exact prefixLift 3116483
  have htrace : WordTrace (prefixWord ++ tailWord_3116483) baseStart_3116483 baseEnd_3116483 := by
    simpa [prefixWord, tailWord_3116483, baseEnd_3116483] using wordTrace_append hprefix tailTrace_3116483
  have hstable : (prefixWord ++ tailWord_3116483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116483).length < 2 ^ (prefixWord ++ tailWord_3116483).sum := by decide
  have hdescent : baseEnd_3116483 < baseStart_3116483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116500 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3116500 : Nat := 118140960795 + 3116500 * 2 ^ 59
def prefixEnd_3116500 : Nat := 4983230072969 + 3 ^ 40 * 3116500 * 2
def baseEnd_3116500 : Nat := 1066841639824774608744989

theorem tailTrace_3116500 : CollatzResearch.WordTrace tailWord_3116500 prefixEnd_3116500 1066841639824774608744989 := by
  unfold tailWord_3116500
  simp only [CollatzResearch.WordTrace]
  refine ⟨56834046604730115335029477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75778728806306820446705969 56834046604730115335029477)
  ·
    refine ⟨10656383738386896625318027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56834046604730115335029477 10656383738386896625318027)
    ·
      refine ⟨15984575607580344937977041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10656383738386896625318027 15984575607580344937977041)
      ·
        refine ⟨11988431705685258703482781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15984575607580344937977041 11988431705685258703482781)
        ·
          refine ⟨4495661889631972013806043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11988431705685258703482781 4495661889631972013806043)
          ·
            refine ⟨6743492834447958020709065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495661889631972013806043 6743492834447958020709065)
            ·
              refine ⟨5057619625835968515531799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6743492834447958020709065 5057619625835968515531799)
              ·
                refine ⟨7586429438753952773297699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057619625835968515531799 7586429438753952773297699)
                ·
                  refine ⟨11379644158130929159946549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586429438753952773297699 11379644158130929159946549)
                  ·
                    refine ⟨1066841639824774608744989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11379644158130929159946549 1066841639824774608744989)
                    ·
                      rfl

theorem cell22_3116500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3116500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116500 prefixEnd_3116500 := by exact prefixLift 3116500
  have htrace : WordTrace (prefixWord ++ tailWord_3116500) baseStart_3116500 baseEnd_3116500 := by
    simpa [prefixWord, tailWord_3116500, baseEnd_3116500] using wordTrace_append hprefix tailTrace_3116500
  have hstable : (prefixWord ++ tailWord_3116500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116500).length < 2 ^ (prefixWord ++ tailWord_3116500).sum := by decide
  have hdescent : baseEnd_3116500 < baseStart_3116500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116513 : List Nat := [1, 2, 3, 1, 2, 4, 3, 6]
def baseStart_3116513 : Nat := 118140960795 + 3116513 * 2 ^ 59
def prefixEnd_3116513 : Nat := 4983230072969 + 3 ^ 40 * 3116513 * 2
def baseEnd_3116513 : Nat := 118538454443382989796661

theorem tailTrace_3116513 : CollatzResearch.WordTrace tailWord_3116513 prefixEnd_3116513 118538454443382989796661 := by
  unfold tailWord_3116513
  simp only [CollatzResearch.WordTrace]
  refine ⟨113668567358413133890282193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75779044905608755926854795 113668567358413133890282193)
  ·
    refine ⟨85251425518809850417711645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113668567358413133890282193 85251425518809850417711645)
    ·
      refine ⟨31969284569553693906641867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85251425518809850417711645 31969284569553693906641867)
      ·
        refine ⟨47953926854330540859962801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31969284569553693906641867 47953926854330540859962801)
        ·
          refine ⟨35965445140747905644972101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47953926854330540859962801 35965445140747905644972101)
          ·
            refine ⟨6743520963890232308432269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35965445140747905644972101 6743520963890232308432269)
            ·
              refine ⟨2528820361458837115662101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6743520963890232308432269 2528820361458837115662101)
              ·
                refine ⟨118538454443382989796661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2528820361458837115662101 118538454443382989796661)
                ·
                  rfl

theorem cell22_3116513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 6].length) (baseStart_3116513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116513 prefixEnd_3116513 := by exact prefixLift 3116513
  have htrace : WordTrace (prefixWord ++ tailWord_3116513) baseStart_3116513 baseEnd_3116513 := by
    simpa [prefixWord, tailWord_3116513, baseEnd_3116513] using wordTrace_append hprefix tailTrace_3116513
  have hstable : (prefixWord ++ tailWord_3116513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116513).length < 2 ^ (prefixWord ++ tailWord_3116513).sum := by decide
  have hdescent : baseEnd_3116513 < baseStart_3116513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116515 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 2, 4]
def baseStart_3116515 : Nat := 118140960795 + 3116515 * 2 ^ 59
def prefixEnd_3116515 : Nat := 4983230072969 + 3 ^ 40 * 3116515 * 2
def baseEnd_3116515 : Nat := 1066846774631319569619943

theorem tailTrace_3116515 : CollatzResearch.WordTrace tailWord_3116515 prefixEnd_3116515 1066846774631319569619943 := by
  unfold tailWord_3116515
  simp only [CollatzResearch.WordTrace]
  refine ⟨113668640304405888231854999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75779093536270592154569999 113668640304405888231854999)
  ·
    refine ⟨170502960456608832347782499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113668640304405888231854999 170502960456608832347782499)
    ·
      refine ⟨255754440684913248521673749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170502960456608832347782499 255754440684913248521673749)
      ·
        refine ⟨11988489407105308524453457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255754440684913248521673749 11988489407105308524453457)
        ·
          refine ⟨8991367055328981393340093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11988489407105308524453457 8991367055328981393340093)
          ·
            refine ⟨3371762645748368022502535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8991367055328981393340093 3371762645748368022502535)
            ·
              refine ⟨5057643968622552033753803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371762645748368022502535 5057643968622552033753803)
              ·
                refine ⟨7586465952933828050630705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5057643968622552033753803 7586465952933828050630705)
                ·
                  refine ⟨5689849464700371037973029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586465952933828050630705 5689849464700371037973029)
                  ·
                    refine ⟨1066846774631319569619943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5689849464700371037973029 1066846774631319569619943)
                    ·
                      rfl

theorem cell22_3116515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 4].length) (baseStart_3116515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116515 prefixEnd_3116515 := by exact prefixLift 3116515
  have htrace : WordTrace (prefixWord ++ tailWord_3116515) baseStart_3116515 baseEnd_3116515 := by
    simpa [prefixWord, tailWord_3116515, baseEnd_3116515] using wordTrace_append hprefix tailTrace_3116515
  have hstable : (prefixWord ++ tailWord_3116515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116515).length < 2 ^ (prefixWord ++ tailWord_3116515).sum := by decide
  have hdescent : baseEnd_3116515 < baseStart_3116515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116564 : List Nat := [2, 4, 3, 1, 3, 1, 2, 6]
def baseStart_3116564 : Nat := 118140960795 + 3116564 * 2 ^ 59
def prefixEnd_3116564 : Nat := 4983230072969 + 3 ^ 40 * 3116564 * 2
def baseEnd_3116564 : Nat := 118540394259188863904977

theorem tailTrace_3116564 : CollatzResearch.WordTrace tailWord_3116564 prefixEnd_3116564 118540394259188863904977 := by
  unfold tailWord_3116564
  simp only [CollatzResearch.WordTrace]
  refine ⟨56835213740614184800194373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75780284987485579733592497 56835213740614184800194373)
  ·
    refine ⟨10656602576365159650036445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56835213740614184800194373 10656602576365159650036445)
    ·
      refine ⟨3996225966136934868763667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10656602576365159650036445 3996225966136934868763667)
      ·
        refine ⟨5994338949205402303145501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996225966136934868763667 5994338949205402303145501)
        ·
          refine ⟨2247877105952025863679563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5994338949205402303145501 2247877105952025863679563)
          ·
            refine ⟨3371815658928038795519345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247877105952025863679563 3371815658928038795519345)
            ·
              refine ⟨2528861744196029096639509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371815658928038795519345 2528861744196029096639509)
              ·
                refine ⟨118540394259188863904977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2528861744196029096639509 118540394259188863904977)
                ·
                  rfl

theorem cell22_3116564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 6].length) (baseStart_3116564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116564 prefixEnd_3116564 := by exact prefixLift 3116564
  have htrace : WordTrace (prefixWord ++ tailWord_3116564) baseStart_3116564 baseEnd_3116564 := by
    simpa [prefixWord, tailWord_3116564, baseEnd_3116564] using wordTrace_append hprefix tailTrace_3116564
  have hstable : (prefixWord ++ tailWord_3116564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116564).length < 2 ^ (prefixWord ++ tailWord_3116564).sum := by decide
  have hdescent : baseEnd_3116564 < baseStart_3116564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116579 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 1, 3]
def baseStart_3116579 : Nat := 118140960795 + 3116579 * 2 ^ 59
def prefixEnd_3116579 : Nat := 4983230072969 + 3 ^ 40 * 3116579 * 2
def baseEnd_3116579 : Nat := 1066868683139244736019747

theorem tailTrace_3116579 : CollatzResearch.WordTrace tailWord_3116579 prefixEnd_3116579 1066868683139244736019747 := by
  unfold tailWord_3116579
  simp only [CollatzResearch.WordTrace]
  refine ⟨113670974576174027162184791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75780649717449351441456527 113670974576174027162184791)
  ·
    refine ⟨170506461864261040743277187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113670974576174027162184791 170506461864261040743277187)
    ·
      refine ⟨255759692796391561114915781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170506461864261040743277187 255759692796391561114915781)
      ·
        refine ⟨47954942399323417709046709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255759692796391561114915781 47954942399323417709046709)
        ·
          refine ⟨4495775849936570410223129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47954942399323417709046709 4495775849936570410223129)
          ·
            refine ⟨3371831887452427807667347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495775849936570410223129 3371831887452427807667347)
            ·
              refine ⟨5057747831178641711501021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371831887452427807667347 5057747831178641711501021)
              ·
                refine ⟨1896655436691990641812883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5057747831178641711501021 1896655436691990641812883)
                ·
                  refine ⟨2844983155037985962719325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896655436691990641812883 2844983155037985962719325)
                  ·
                    refine ⟨1066868683139244736019747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2844983155037985962719325 1066868683139244736019747)
                    ·
                      rfl

theorem cell22_3116579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 1, 3].length) (baseStart_3116579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116579 prefixEnd_3116579 := by exact prefixLift 3116579
  have htrace : WordTrace (prefixWord ++ tailWord_3116579) baseStart_3116579 baseEnd_3116579 := by
    simpa [prefixWord, tailWord_3116579, baseEnd_3116579] using wordTrace_append hprefix tailTrace_3116579
  have hstable : (prefixWord ++ tailWord_3116579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116579).length < 2 ^ (prefixWord ++ tailWord_3116579).sum := by decide
  have hdescent : baseEnd_3116579 < baseStart_3116579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116618 : List Nat := [3, 1, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3116618 : Nat := 118140960795 + 3116618 * 2 ^ 59
def prefixEnd_3116618 : Nat := 4983230072969 + 3 ^ 40 * 3116618 * 2
def baseEnd_3116618 : Nat := 1066882033636261634294627

theorem tailTrace_3116618 : CollatzResearch.WordTrace tailWord_3116618 prefixEnd_3116618 1066882033636261634294627 := by
  unfold tailWord_3116618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28418099255758184205713627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75781598015355157881903005 28418099255758184205713627)
  ·
    refine ⟨42627148883637276308570441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28418099255758184205713627 42627148883637276308570441)
    ·
      refine ⟨31970361662727957231427831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42627148883637276308570441 31970361662727957231427831)
      ·
        refine ⟨47955542494091935847141747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31970361662727957231427831 47955542494091935847141747)
        ·
          refine ⟨71933313741137903770712621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47955542494091935847141747 71933313741137903770712621)
          ·
            refine ⟨26974992652926713914017233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71933313741137903770712621 26974992652926713914017233)
            ·
              refine ⟨20231244489695035435512925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26974992652926713914017233 20231244489695035435512925)
              ·
                refine ⟨7586716683635638288317347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20231244489695035435512925 7586716683635638288317347)
                ·
                  refine ⟨11380075025453457432476021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7586716683635638288317347 11380075025453457432476021)
                  ·
                    refine ⟨1066882033636261634294627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11380075025453457432476021 1066882033636261634294627)
                    ·
                      rfl

theorem cell22_3116618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3116618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116618 prefixEnd_3116618 := by exact prefixLift 3116618
  have htrace : WordTrace (prefixWord ++ tailWord_3116618) baseStart_3116618 baseEnd_3116618 := by
    simpa [prefixWord, tailWord_3116618, baseEnd_3116618] using wordTrace_append hprefix tailTrace_3116618
  have hstable : (prefixWord ++ tailWord_3116618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116618).length < 2 ^ (prefixWord ++ tailWord_3116618).sum := by decide
  have hdescent : baseEnd_3116618 < baseStart_3116618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116648 : List Nat := [2, 1, 4, 3, 1, 11]
def baseStart_3116648 : Nat := 118140960795 + 3116648 * 2 ^ 59
def prefixEnd_3116648 : Nat := 4983230072969 + 3 ^ 40 * 3116648 * 2
def baseEnd_3116648 : Nat := 13171509916658661185735

theorem tailTrace_3116648 : CollatzResearch.WordTrace tailWord_3116648 prefixEnd_3116648 13171509916658661185735 := by
  unfold tailWord_3116648
  simp only [CollatzResearch.WordTrace]
  refine ⟨56836745606462025973223299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75782327475282701297631065 56836745606462025973223299)
  ·
    refine ⟨85255118409693038959834949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56836745606462025973223299 85255118409693038959834949)
    ·
      refine ⟨15985334701817444804969053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85255118409693038959834949 15985334701817444804969053)
      ·
        refine ⟨5994500513181541801863395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15985334701817444804969053 5994500513181541801863395)
        ·
          refine ⟨8991750769772312702795093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5994500513181541801863395 8991750769772312702795093)
          ·
            refine ⟨13171509916658661185735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8991750769772312702795093 13171509916658661185735)
            ·
              rfl

theorem cell22_3116648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 11].length) (baseStart_3116648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116648 prefixEnd_3116648 := by exact prefixLift 3116648
  have htrace : WordTrace (prefixWord ++ tailWord_3116648) baseStart_3116648 baseEnd_3116648 := by
    simpa [prefixWord, tailWord_3116648, baseEnd_3116648] using wordTrace_append hprefix tailTrace_3116648
  have hstable : (prefixWord ++ tailWord_3116648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116648).length < 2 ^ (prefixWord ++ tailWord_3116648).sum := by decide
  have hdescent : baseEnd_3116648 < baseStart_3116648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116650 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_3116650 : Nat := 118140960795 + 3116650 * 2 ^ 59
def prefixEnd_3116650 : Nat := 4983230072969 + 3 ^ 40 * 3116650 * 2
def baseEnd_3116650 : Nat := 1066892987890224217494529

theorem tailTrace_3116650 : CollatzResearch.WordTrace tailWord_3116650 prefixEnd_3116650 1066892987890224217494529 := by
  unfold tailWord_3116650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28418391039729201572004851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75782376105944537525346269 28418391039729201572004851)
  ·
    refine ⟨42627586559593802358007277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28418391039729201572004851 42627586559593802358007277)
    ·
      refine ⟨15985344959847675884252729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42627586559593802358007277 15985344959847675884252729)
      ·
        refine ⟨11989008719885756913189547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15985344959847675884252729 11989008719885756913189547)
        ·
          refine ⟨17983513079828635369784321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11989008719885756913189547 17983513079828635369784321)
          ·
            refine ⟨13487634809871476527338241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17983513079828635369784321 13487634809871476527338241)
            ·
              refine ⟨10115726107403607395503681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13487634809871476527338241 10115726107403607395503681)
              ·
                refine ⟨7586794580552705546627761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10115726107403607395503681 7586794580552705546627761)
                ·
                  refine ⟨5690095935414529159970821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7586794580552705546627761 5690095935414529159970821)
                  ·
                    refine ⟨1066892987890224217494529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690095935414529159970821 1066892987890224217494529)
                    ·
                      rfl

theorem cell22_3116650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_3116650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116650 prefixEnd_3116650 := by exact prefixLift 3116650
  have htrace : WordTrace (prefixWord ++ tailWord_3116650) baseStart_3116650 baseEnd_3116650 := by
    simpa [prefixWord, tailWord_3116650, baseEnd_3116650] using wordTrace_append hprefix tailTrace_3116650
  have hstable : (prefixWord ++ tailWord_3116650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116650).length < 2 ^ (prefixWord ++ tailWord_3116650).sum := by decide
  have hdescent : baseEnd_3116650 < baseStart_3116650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116727 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 5]
def baseStart_3116727 : Nat := 118140960795 + 3116727 * 2 ^ 59
def prefixEnd_3116727 : Nat := 4983230072969 + 3 ^ 40 * 3116727 * 2
def baseEnd_3116727 : Nat := 355639782187940561106431

theorem tailTrace_3116727 : CollatzResearch.WordTrace tailWord_3116727 prefixEnd_3116727 355639782187940561106431 := by
  unfold tailWord_3116727
  simp only [CollatzResearch.WordTrace]
  refine ⟨113676372579637848438572435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75784248386425232292381623 113676372579637848438572435)
  ·
    refine ⟨170514558869456772657858653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113676372579637848438572435 170514558869456772657858653)
    ·
      refine ⟨63942959576046289746696995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170514558869456772657858653 63942959576046289746696995)
      ·
        refine ⟨95914439364069434620045493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63942959576046289746696995 95914439364069434620045493)
        ·
          refine ⟨8991978690381509495629265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95914439364069434620045493 8991978690381509495629265)
          ·
            refine ⟨6743984017786132121721949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8991978690381509495629265 6743984017786132121721949)
            ·
              refine ⟨2528994006669799545645731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6743984017786132121721949 2528994006669799545645731)
              ·
                refine ⟨3793491010004699318468597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528994006669799545645731 3793491010004699318468597)
                ·
                  refine ⟨355639782187940561106431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3793491010004699318468597 355639782187940561106431)
                  ·
                    rfl

theorem cell22_3116727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 5].length) (baseStart_3116727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116727 prefixEnd_3116727 := by exact prefixLift 3116727
  have htrace : WordTrace (prefixWord ++ tailWord_3116727) baseStart_3116727 baseEnd_3116727 := by
    simpa [prefixWord, tailWord_3116727, baseEnd_3116727] using wordTrace_append hprefix tailTrace_3116727
  have hstable : (prefixWord ++ tailWord_3116727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116727).length < 2 ^ (prefixWord ++ tailWord_3116727).sum := by decide
  have hdescent : baseEnd_3116727 < baseStart_3116727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116748 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_3116748 : Nat := 118140960795 + 3116748 * 2 ^ 59
def prefixEnd_3116748 : Nat := 4983230072969 + 3 ^ 40 * 3116748 * 2
def baseEnd_3116748 : Nat := 1066926535292984628544229

theorem tailTrace_3116748 : CollatzResearch.WordTrace tailWord_3116748 prefixEnd_3116748 1066926535292984628544229 := by
  unfold tailWord_3116748
  simp only [CollatzResearch.WordTrace]
  refine ⟨56838569256280884512543449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75784759008374512683391265 56838569256280884512543449)
  ·
    refine ⟨42628926942210663384407587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56838569256280884512543449 42628926942210663384407587)
    ·
      refine ⟨63943390413315995076611381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42628926942210663384407587 63943390413315995076611381)
      ·
        refine ⟨5994692851248374538432317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63943390413315995076611381 5994692851248374538432317)
        ·
          refine ⟨2248009819218140451912119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5994692851248374538432317 2248009819218140451912119)
          ·
            refine ⟨3372014728827210677868179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248009819218140451912119 3372014728827210677868179)
            ·
              refine ⟨5058022093240816016802269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372014728827210677868179 5058022093240816016802269)
              ·
                refine ⟨1896758284965306006300851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5058022093240816016802269 1896758284965306006300851)
                ·
                  refine ⟨2845137427447959009451277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896758284965306006300851 2845137427447959009451277)
                  ·
                    refine ⟨1066926535292984628544229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845137427447959009451277 1066926535292984628544229)
                    ·
                      rfl

theorem cell22_3116748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_3116748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116748 prefixEnd_3116748 := by exact prefixLift 3116748
  have htrace : WordTrace (prefixWord ++ tailWord_3116748) baseStart_3116748 baseEnd_3116748 := by
    simpa [prefixWord, tailWord_3116748, baseEnd_3116748] using wordTrace_append hprefix tailTrace_3116748
  have hstable : (prefixWord ++ tailWord_3116748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116748).length < 2 ^ (prefixWord ++ tailWord_3116748).sum := by decide
  have hdescent : baseEnd_3116748 < baseStart_3116748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116815 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 7, 3]
def baseStart_3116815 : Nat := 118140960795 + 3116815 * 2 ^ 59
def prefixEnd_3116815 : Nat := 4983230072969 + 3 ^ 40 * 3116815 * 2
def baseEnd_3116815 : Nat := 1066949470762218787119023

theorem tailTrace_3116815 : CollatzResearch.WordTrace tailWord_3116815 prefixEnd_3116815 1066949470762218787119023 := by
  unfold tailWord_3116815
  simp only [CollatzResearch.WordTrace]
  refine ⟨113679582203319039467775899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75786388135546026311850599 113679582203319039467775899)
  ·
    refine ⟨170519373304978559201663849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113679582203319039467775899 170519373304978559201663849)
    ·
      refine ⟨127889529978733919401247887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170519373304978559201663849 127889529978733919401247887)
      ·
        refine ⟨191834294968100879101871831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127889529978733919401247887 191834294968100879101871831)
        ·
          refine ⟨287751442452151318652807747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191834294968100879101871831 287751442452151318652807747)
          ·
            refine ⟨431627163678226977979211621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287751442452151318652807747 431627163678226977979211621)
            ·
              refine ⟨80930093189667558371102179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 431627163678226977979211621 80930093189667558371102179)
              ·
                refine ⟨121395139784501337556653269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80930093189667558371102179 121395139784501337556653269)
                ·
                  refine ⟨2845198588699250098984061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 121395139784501337556653269 2845198588699250098984061)
                  ·
                    refine ⟨1066949470762218787119023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845198588699250098984061 1066949470762218787119023)
                    ·
                      rfl

theorem cell22_3116815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_3116815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116815 prefixEnd_3116815 := by exact prefixLift 3116815
  have htrace : WordTrace (prefixWord ++ tailWord_3116815) baseStart_3116815 baseEnd_3116815 := by
    simpa [prefixWord, tailWord_3116815, baseEnd_3116815] using wordTrace_append hprefix tailTrace_3116815
  have hstable : (prefixWord ++ tailWord_3116815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116815).length < 2 ^ (prefixWord ++ tailWord_3116815).sum := by decide
  have hdescent : baseEnd_3116815 < baseStart_3116815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116832 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_3116832 : Nat := 118140960795 + 3116832 * 2 ^ 59
def prefixEnd_3116832 : Nat := 4983230072969 + 3 ^ 40 * 3116832 * 2
def baseEnd_3116832 : Nat := 1066955290209636409443971

theorem tailTrace_3116832 : CollatzResearch.WordTrace tailWord_3116832 prefixEnd_3116832 1066955290209636409443971 := by
  unfold tailWord_3116832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56840101122128725685572375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75786801496171634247429833 56840101122128725685572375)
  ·
    refine ⟨85260151683193088528358563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56840101122128725685572375 85260151683193088528358563)
    ·
      refine ⟨127890227524789632792537845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85260151683193088528358563 127890227524789632792537845)
      ·
        refine ⟨11989708830449028074300423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127890227524789632792537845 11989708830449028074300423)
        ·
          refine ⟨17984563245673542111450635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11989708830449028074300423 17984563245673542111450635)
          ·
            refine ⟨26976844868510313167175953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17984563245673542111450635 26976844868510313167175953)
            ·
              refine ⟨20232633651382734875381965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26976844868510313167175953 20232633651382734875381965)
              ·
                refine ⟨7587237619268525578268237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20232633651382734875381965 7587237619268525578268237)
                ·
                  refine ⟨2845214107225697091850589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7587237619268525578268237 2845214107225697091850589)
                  ·
                    refine ⟨1066955290209636409443971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845214107225697091850589 1066955290209636409443971)
                    ·
                      rfl

theorem cell22_3116832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_3116832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116832 prefixEnd_3116832 := by exact prefixLift 3116832
  have htrace : WordTrace (prefixWord ++ tailWord_3116832) baseStart_3116832 baseEnd_3116832 := by
    simpa [prefixWord, tailWord_3116832, baseEnd_3116832] using wordTrace_append hprefix tailTrace_3116832
  have hstable : (prefixWord ++ tailWord_3116832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116832).length < 2 ^ (prefixWord ++ tailWord_3116832).sum := by decide
  have hdescent : baseEnd_3116832 < baseStart_3116832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116922 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_3116922 : Nat := 118140960795 + 3116922 * 2 ^ 59
def prefixEnd_3116922 : Nat := 4983230072969 + 3 ^ 40 * 3116922 * 2
def baseEnd_3116922 : Nat := 1066986099048906174693695

theorem tailTrace_3116922 : CollatzResearch.WordTrace tailWord_3116922 prefixEnd_3116922 1066986099048906174693695 := by
  unfold tailWord_3116922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28420871203482849185480255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75788989875954264494614013 28420871203482849185480255)
  ·
    refine ⟨42631306805224273778220383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28420871203482849185480255 42631306805224273778220383)
    ·
      refine ⟨63946960207836410667330575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42631306805224273778220383 63946960207836410667330575)
      ·
        refine ⟨95920440311754616000995863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63946960207836410667330575 95920440311754616000995863)
        ·
          refine ⟨143880660467631924001493795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95920440311754616000995863 143880660467631924001493795)
          ·
            refine ⟨215820990701447886002240693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143880660467631924001493795 215820990701447886002240693)
            ·
              refine ⟨20233217878260739312710065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215820990701447886002240693 20233217878260739312710065)
              ·
                refine ⟨15174913408695554484532549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20233217878260739312710065 15174913408695554484532549)
                ·
                  refine ⟨2845296264130416465849853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15174913408695554484532549 2845296264130416465849853)
                  ·
                    refine ⟨1066986099048906174693695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845296264130416465849853 1066986099048906174693695)
                    ·
                      rfl

theorem cell22_3116922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_3116922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116922 prefixEnd_3116922 := by exact prefixLift 3116922
  have htrace : WordTrace (prefixWord ++ tailWord_3116922) baseStart_3116922 baseEnd_3116922 := by
    simpa [prefixWord, tailWord_3116922, baseEnd_3116922] using wordTrace_append hprefix tailTrace_3116922
  have hstable : (prefixWord ++ tailWord_3116922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116922).length < 2 ^ (prefixWord ++ tailWord_3116922).sum := by decide
  have hdescent : baseEnd_3116922 < baseStart_3116922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116926 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3116926 : Nat := 118140960795 + 3116926 * 2 ^ 59
def prefixEnd_3116926 : Nat := 4983230072969 + 3 ^ 40 * 3116926 * 2
def baseEnd_3116926 : Nat := 1066987468330651497593683

theorem tailTrace_3116926 : CollatzResearch.WordTrace tailWord_3116926 prefixEnd_3116926 1066987468330651497593683 := by
  unfold tailWord_3116926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14210453838239613178133329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75789087137277936950044421 14210453838239613178133329)
  ·
    refine ⟨10657840378679709883599997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14210453838239613178133329 10657840378679709883599997)
    ·
      refine ⟨3996690142004891206349999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10657840378679709883599997 3996690142004891206349999)
      ·
        refine ⟨5995035213007336809524999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996690142004891206349999 5995035213007336809524999)
        ·
          refine ⟨8992552819511005214287499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995035213007336809524999 8992552819511005214287499)
          ·
            refine ⟨13488829229266507821431249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8992552819511005214287499 13488829229266507821431249)
            ·
              refine ⟨10116621921949880866073437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13488829229266507821431249 10116621921949880866073437)
              ·
                refine ⟨3793733220731205324777539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10116621921949880866073437 3793733220731205324777539)
                ·
                  refine ⟨5690599831096807987166309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793733220731205324777539 5690599831096807987166309)
                  ·
                    refine ⟨1066987468330651497593683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690599831096807987166309 1066987468330651497593683)
                    ·
                      rfl

theorem cell22_3116926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3116926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116926 prefixEnd_3116926 := by exact prefixLift 3116926
  have htrace : WordTrace (prefixWord ++ tailWord_3116926) baseStart_3116926 baseEnd_3116926 := by
    simpa [prefixWord, tailWord_3116926, baseEnd_3116926] using wordTrace_append hprefix tailTrace_3116926
  have hstable : (prefixWord ++ tailWord_3116926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116926).length < 2 ^ (prefixWord ++ tailWord_3116926).sum := by decide
  have hdescent : baseEnd_3116926 < baseStart_3116926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116937 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_3116937 : Nat := 118140960795 + 3116937 * 2 ^ 59
def prefixEnd_3116937 : Nat := 4983230072969 + 3 ^ 40 * 3116937 * 2
def baseEnd_3116937 : Nat := 1066991233855451135568649

theorem tailTrace_3116937 : CollatzResearch.WordTrace tailWord_3116937 prefixEnd_3116937 1066991233855451135568649 := by
  unfold tailWord_3116937
  simp only [CollatzResearch.WordTrace]
  refine ⟨113684031908877054303717065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75789354605918036202478043 113684031908877054303717065)
  ·
    refine ⟨85263023931657790727787799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113684031908877054303717065 85263023931657790727787799)
    ·
      refine ⟨127894535897486686091681699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85263023931657790727787799 127894535897486686091681699)
      ·
        refine ⟨191841803846230029137522549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127894535897486686091681699 191841803846230029137522549)
        ·
          refine ⟨17985169110584065231642739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191841803846230029137522549 17985169110584065231642739)
          ·
            refine ⟨26977753665876097847464109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17985169110584065231642739 26977753665876097847464109)
            ·
              refine ⟨10116657624703536692799041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26977753665876097847464109 10116657624703536692799041)
              ·
                refine ⟨7587493218527652519599281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10116657624703536692799041 7587493218527652519599281)
                ·
                  refine ⟨5690619913895739389699461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7587493218527652519599281 5690619913895739389699461)
                  ·
                    refine ⟨1066991233855451135568649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690619913895739389699461 1066991233855451135568649)
                    ·
                      rfl

theorem cell22_3116937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_3116937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116937 prefixEnd_3116937 := by exact prefixLift 3116937
  have htrace : WordTrace (prefixWord ++ tailWord_3116937) baseStart_3116937 baseEnd_3116937 := by
    simpa [prefixWord, tailWord_3116937, baseEnd_3116937] using wordTrace_append hprefix tailTrace_3116937
  have hstable : (prefixWord ++ tailWord_3116937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116937).length < 2 ^ (prefixWord ++ tailWord_3116937).sum := by decide
  have hdescent : baseEnd_3116937 < baseStart_3116937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3116956 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_3116956 : Nat := 118140960795 + 3116956 * 2 ^ 59
def prefixEnd_3116956 : Nat := 4983230072969 + 3 ^ 40 * 3116956 * 2
def baseEnd_3116956 : Nat := 1066997737943741419343591

theorem tailTrace_3116956 : CollatzResearch.WordTrace tailWord_3116956 prefixEnd_3116956 1066997737943741419343591 := by
  unfold tailWord_3116956
  simp only [CollatzResearch.WordTrace]
  refine ⟨56842362447904110274329361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75789816597205480365772481 56842362447904110274329361)
  ·
    refine ⟨42631771835928082705747021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56842362447904110274329361 42631771835928082705747021)
    ·
      refine ⟨15986914438473031014655133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42631771835928082705747021 15986914438473031014655133)
      ·
        refine ⟨5995092914427386630495675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15986914438473031014655133 5995092914427386630495675)
        ·
          refine ⟨8992639371641079945743513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995092914427386630495675 8992639371641079945743513)
          ·
            refine ⟨6744479528730809959307635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8992639371641079945743513 6744479528730809959307635)
            ·
              refine ⟨10116719293096214938961453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6744479528730809959307635 10116719293096214938961453)
              ·
                refine ⟨3793769734911080602110545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10116719293096214938961453 3793769734911080602110545)
                ·
                  refine ⟨2845327301183310451582909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3793769734911080602110545 2845327301183310451582909)
                  ·
                    refine ⟨1066997737943741419343591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845327301183310451582909 1066997737943741419343591)
                    ·
                      rfl

theorem cell22_3116956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_3116956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3116956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3116956 prefixEnd_3116956 := by exact prefixLift 3116956
  have htrace : WordTrace (prefixWord ++ tailWord_3116956) baseStart_3116956 baseEnd_3116956 := by
    simpa [prefixWord, tailWord_3116956, baseEnd_3116956] using wordTrace_append hprefix tailTrace_3116956
  have hstable : (prefixWord ++ tailWord_3116956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3116956).length < 2 ^ (prefixWord ++ tailWord_3116956).sum := by decide
  have hdescent : baseEnd_3116956 < baseStart_3116956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3116956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117072 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_3117072 : Nat := 118140960795 + 3117072 * 2 ^ 59
def prefixEnd_3117072 : Nat := 4983230072969 + 3 ^ 40 * 3117072 * 2
def baseEnd_3117072 : Nat := 1067037447114355783443235

theorem tailTrace_3117072 : CollatzResearch.WordTrace tailWord_3117072 prefixEnd_3117072 1067037447114355783443235 := by
  unfold tailWord_3117072
  simp only [CollatzResearch.WordTrace]
  refine ⟨56844477881693986179940735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75792637175591981573254313 56844477881693986179940735)
  ·
    refine ⟨85266716822540979269911103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56844477881693986179940735 85266716822540979269911103)
    ·
      refine ⟨127900075233811468904866655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85266716822540979269911103 127900075233811468904866655)
      ·
        refine ⟨191850112850717203357299983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127900075233811468904866655 191850112850717203357299983)
        ·
          refine ⟨287775169276075805035949975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191850112850717203357299983 287775169276075805035949975)
          ·
            refine ⟨431662753914113707553924963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287775169276075805035949975 431662753914113707553924963)
            ·
              refine ⟨647494130871170561330887445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431662753914113707553924963 647494130871170561330887445)
              ·
                refine ⟨30351287384586120062385349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 647494130871170561330887445 30351287384586120062385349)
                ·
                  refine ⟨5690866384609897511697253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30351287384586120062385349 5690866384609897511697253)
                  ·
                    refine ⟨1067037447114355783443235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690866384609897511697253 1067037447114355783443235)
                    ·
                      rfl

theorem cell22_3117072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_3117072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117072 prefixEnd_3117072 := by exact prefixLift 3117072
  have htrace : WordTrace (prefixWord ++ tailWord_3117072) baseStart_3117072 baseEnd_3117072 := by
    simpa [prefixWord, tailWord_3117072, baseEnd_3117072] using wordTrace_append hprefix tailTrace_3117072
  have hstable : (prefixWord ++ tailWord_3117072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117072).length < 2 ^ (prefixWord ++ tailWord_3117072).sum := by decide
  have hdescent : baseEnd_3117072 < baseStart_3117072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117087 : List Nat := [1, 1, 2, 4, 1, 2, 3, 8]
def baseStart_3117087 : Nat := 118140960795 + 3117087 * 2 ^ 59
def prefixEnd_3117087 : Nat := 4983230072969 + 3 ^ 40 * 3117087 * 2
def baseEnd_3117087 : Nat := 118560286880100082702021

theorem tailTrace_3117087 : CollatzResearch.WordTrace tailWord_3117087 prefixEnd_3117087 118560286880100082702021 := by
  unfold tailWord_3117087
  simp only [CollatzResearch.WordTrace]
  refine ⟨113689502858333629921677515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75793001905555753281118343 113689502858333629921677515)
  ·
    refine ⟨170534254287500444882516273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113689502858333629921677515 170534254287500444882516273)
    ·
      refine ⟨127900690715625333661887205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170534254287500444882516273 127900690715625333661887205)
      ·
        refine ⟨23981379509179750061603851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127900690715625333661887205 23981379509179750061603851)
        ·
          refine ⟨35972069263769625092405777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23981379509179750061603851 35972069263769625092405777)
          ·
            refine ⟨26979051947827218819304333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35972069263769625092405777 26979051947827218819304333)
            ·
              refine ⟨10117144480435207057239125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26979051947827218819304333 10117144480435207057239125)
              ·
                refine ⟨118560286880100082702021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10117144480435207057239125 118560286880100082702021)
                ·
                  rfl

theorem cell22_3117087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 8].length) (baseStart_3117087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117087 prefixEnd_3117087 := by exact prefixLift 3117087
  have htrace : WordTrace (prefixWord ++ tailWord_3117087) baseStart_3117087 baseEnd_3117087 := by
    simpa [prefixWord, tailWord_3117087, baseEnd_3117087] using wordTrace_append hprefix tailTrace_3117087
  have hstable : (prefixWord ++ tailWord_3117087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117087).length < 2 ^ (prefixWord ++ tailWord_3117087).sum := by decide
  have hdescent : baseEnd_3117087 < baseStart_3117087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117166 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_3117166 : Nat := 118140960795 + 3117166 * 2 ^ 59
def prefixEnd_3117166 : Nat := 4983230072969 + 3 ^ 40 * 3117166 * 2
def baseEnd_3117166 : Nat := 355689875078456957197649

theorem tailTrace_3117166 : CollatzResearch.WordTrace tailWord_3117166 prefixEnd_3117166 355689875078456957197649 := by
  unfold tailWord_3117166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14211548028130928301725419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75794922816698284275868901 14211548028130928301725419)
  ·
    refine ⟨21317322042196392452588129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14211548028130928301725419 21317322042196392452588129)
    ·
      refine ⟨15987991531647294339441097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21317322042196392452588129 15987991531647294339441097)
      ·
        refine ⟨11990993648735470754580823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15987991531647294339441097 11990993648735470754580823)
        ·
          refine ⟨17986490473103206131871235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11990993648735470754580823 17986490473103206131871235)
          ·
            refine ⟨26979735709654809197806853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17986490473103206131871235 26979735709654809197806853)
            ·
              refine ⟨5058700445560276724588785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26979735709654809197806853 5058700445560276724588785)
              ·
                refine ⟨3794025334170207543441589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5058700445560276724588785 3794025334170207543441589)
                ·
                  refine ⟨355689875078456957197649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3794025334170207543441589 355689875078456957197649)
                  ·
                    rfl

theorem cell22_3117166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_3117166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117166 prefixEnd_3117166 := by exact prefixLift 3117166
  have htrace : WordTrace (prefixWord ++ tailWord_3117166) baseStart_3117166 baseEnd_3117166 := by
    simpa [prefixWord, tailWord_3117166, baseEnd_3117166] using wordTrace_append hprefix tailTrace_3117166
  have hstable : (prefixWord ++ tailWord_3117166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117166).length < 2 ^ (prefixWord ++ tailWord_3117166).sum := by decide
  have hdescent : baseEnd_3117166 < baseStart_3117166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117170 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_3117170 : Nat := 118140960795 + 3117170 * 2 ^ 59
def prefixEnd_3117170 : Nat := 4983230072969 + 3 ^ 40 * 3117170 * 2
def baseEnd_3117170 : Nat := 1067070994517116194492935

theorem tailTrace_3117170 : CollatzResearch.WordTrace tailWord_3117170 prefixEnd_3117170 1067070994517116194492935 := by
  unfold tailWord_3117170
  simp only [CollatzResearch.WordTrace]
  refine ⟨28423132529258233774237241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75795020078021956731299309 28423132529258233774237241)
  ·
    refine ⟨21317349396943675330677931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28423132529258233774237241 21317349396943675330677931)
    ·
      refine ⟨31976024095415512996016897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21317349396943675330677931 31976024095415512996016897)
      ·
        refine ⟨23982018071561634747012673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31976024095415512996016897 23982018071561634747012673)
        ·
          refine ⟨17986513553671226060259505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23982018071561634747012673 17986513553671226060259505)
          ·
            refine ⟨13489885165253419545194629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17986513553671226060259505 13489885165253419545194629)
            ·
              refine ⟨2529353468485016164723993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13489885165253419545194629 2529353468485016164723993)
              ·
                refine ⟨1897015101363762123542995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529353468485016164723993 1897015101363762123542995)
                ·
                  refine ⟨2845522652045643185314493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897015101363762123542995 2845522652045643185314493)
                  ·
                    refine ⟨1067070994517116194492935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845522652045643185314493 1067070994517116194492935)
                    ·
                      rfl

theorem cell22_3117170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_3117170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117170 prefixEnd_3117170 := by exact prefixLift 3117170
  have htrace : WordTrace (prefixWord ++ tailWord_3117170) baseStart_3117170 baseEnd_3117170 := by
    simpa [prefixWord, tailWord_3117170, baseEnd_3117170] using wordTrace_append hprefix tailTrace_3117170
  have hstable : (prefixWord ++ tailWord_3117170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117170).length < 2 ^ (prefixWord ++ tailWord_3117170).sum := by decide
  have hdescent : baseEnd_3117170 < baseStart_3117170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117194 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_3117194 : Nat := 118140960795 + 3117194 * 2 ^ 59
def prefixEnd_3117194 : Nat := 4983230072969 + 3 ^ 40 * 3117194 * 2
def baseEnd_3117194 : Nat := 355693070069196043964287

theorem tailTrace_3117194 : CollatzResearch.WordTrace tailWord_3117194 prefixEnd_3117194 355693070069196043964287 := by
  unfold tailWord_3117194
  simp only [CollatzResearch.WordTrace]
  refine ⟨28423351367236496798955659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75795603645963991463881757 28423351367236496798955659)
  ·
    refine ⟨42635027050854745198433489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28423351367236496798955659 42635027050854745198433489)
    ·
      refine ⟨31976270288141058898825117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42635027050854745198433489 31976270288141058898825117)
      ·
        refine ⟨11991101358052897087059419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31976270288141058898825117 11991101358052897087059419)
        ·
          refine ⟨17986652037079345630589129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11991101358052897087059419 17986652037079345630589129)
          ·
            refine ⟨13489989027809509222941847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17986652037079345630589129 13489989027809509222941847)
            ·
              refine ⟨20234983541714263834412771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13489989027809509222941847 20234983541714263834412771)
              ·
                refine ⟨30352475312571395751619157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20234983541714263834412771 30352475312571395751619157)
                ·
                  refine ⟨355693070069196043964287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30352475312571395751619157 355693070069196043964287)
                  ·
                    rfl

theorem cell22_3117194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_3117194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117194 prefixEnd_3117194 := by exact prefixLift 3117194
  have htrace : WordTrace (prefixWord ++ tailWord_3117194) baseStart_3117194 baseEnd_3117194 := by
    simpa [prefixWord, tailWord_3117194, baseEnd_3117194] using wordTrace_append hprefix tailTrace_3117194
  have hstable : (prefixWord ++ tailWord_3117194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117194).length < 2 ^ (prefixWord ++ tailWord_3117194).sum := by decide
  have hdescent : baseEnd_3117194 < baseStart_3117194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117213 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3117213 : Nat := 118140960795 + 3117213 * 2 ^ 59
def prefixEnd_3117213 : Nat := 4983230072969 + 3 ^ 40 * 3117213 * 2
def baseEnd_3117213 : Nat := 1067085714295878415667803

theorem tailTrace_3117213 : CollatzResearch.WordTrace tailWord_3117213 prefixEnd_3117213 1067085714295878415667803 := by
  unfold tailWord_3117213
  simp only [CollatzResearch.WordTrace]
  refine ⟨113694098455877153440764293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75796065637251435627176195 113694098455877153440764293)
  ·
    refine ⟨21317643460476966270143305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113694098455877153440764293 21317643460476966270143305)
    ·
      refine ⟨15988232595357724702607479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21317643460476966270143305 15988232595357724702607479)
      ·
        refine ⟨23982348893036587053911219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15988232595357724702607479 23982348893036587053911219)
        ·
          refine ⟨35973523339554880580866829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23982348893036587053911219 35973523339554880580866829)
          ·
            refine ⟨13490071252333080217825061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35973523339554880580866829 13490071252333080217825061)
            ·
              refine ⟨2529388359812452540842199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13490071252333080217825061 2529388359812452540842199)
              ·
                refine ⟨3794082539718678811263299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529388359812452540842199 3794082539718678811263299)
                ·
                  refine ⟨5691123809578018216894949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794082539718678811263299 5691123809578018216894949)
                  ·
                    refine ⟨1067085714295878415667803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691123809578018216894949 1067085714295878415667803)
                    ·
                      rfl

theorem cell22_3117213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3117213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117213 prefixEnd_3117213 := by exact prefixLift 3117213
  have htrace : WordTrace (prefixWord ++ tailWord_3117213) baseStart_3117213 baseEnd_3117213 := by
    simpa [prefixWord, tailWord_3117213, baseEnd_3117213] using wordTrace_append hprefix tailTrace_3117213
  have hstable : (prefixWord ++ tailWord_3117213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117213).length < 2 ^ (prefixWord ++ tailWord_3117213).sum := by decide
  have hdescent : baseEnd_3117213 < baseStart_3117213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117243 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 2, 3]
def baseStart_3117243 : Nat := 118140960795 + 3117243 * 2 ^ 59
def prefixEnd_3117243 : Nat := 4983230072969 + 3 ^ 40 * 3117243 * 2
def baseEnd_3117243 : Nat := 1067095983908968337417711

theorem tailTrace_3117243 : CollatzResearch.WordTrace tailWord_3117243 prefixEnd_3117243 1067095983908968337417711 := by
  unfold tailWord_3117243
  simp only [CollatzResearch.WordTrace]
  refine ⟨113695192645768468564356383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75796795097178979042904255 113695192645768468564356383)
  ·
    refine ⟨170542788968652702846534575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113695192645768468564356383 170542788968652702846534575)
    ·
      refine ⟨255814183452979054269801863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170542788968652702846534575 255814183452979054269801863)
      ·
        refine ⟨383721275179468581404702795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255814183452979054269801863 383721275179468581404702795)
        ·
          refine ⟨575581912769202872107054193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383721275179468581404702795 575581912769202872107054193)
          ·
            refine ⟨431686434576902154080290645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575581912769202872107054193 431686434576902154080290645)
            ·
              refine ⟨2529412702599036059064203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 431686434576902154080290645 2529412702599036059064203)
              ·
                refine ⟨3794119053898554088596305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529412702599036059064203 3794119053898554088596305)
                ·
                  refine ⟨2845589290423915566447229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3794119053898554088596305 2845589290423915566447229)
                  ·
                    refine ⟨1067095983908968337417711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845589290423915566447229 1067095983908968337417711)
                    ·
                      rfl

theorem cell22_3117243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 3].length) (baseStart_3117243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117243 prefixEnd_3117243 := by exact prefixLift 3117243
  have htrace : WordTrace (prefixWord ++ tailWord_3117243) baseStart_3117243 baseEnd_3117243 := by
    simpa [prefixWord, tailWord_3117243, baseEnd_3117243] using wordTrace_append hprefix tailTrace_3117243
  have hstable : (prefixWord ++ tailWord_3117243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117243).length < 2 ^ (prefixWord ++ tailWord_3117243).sum := by decide
  have hdescent : baseEnd_3117243 < baseStart_3117243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117288 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_3117288 : Nat := 118140960795 + 3117288 * 2 ^ 59
def prefixEnd_3117288 : Nat := 4983230072969 + 3 ^ 40 * 3117288 * 2
def baseEnd_3117288 : Nat := 1067111388328603220042573

theorem tailTrace_3117288 : CollatzResearch.WordTrace tailWord_3117288 prefixEnd_3117288 1067111388328603220042573 := by
  unfold tailWord_3117288
  simp only [CollatzResearch.WordTrace]
  refine ⟨56848416965302720624872259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75797889287070294166496345 56848416965302720624872259)
  ·
    refine ⟨85272625447954080937308389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56848416965302720624872259 85272625447954080937308389)
    ·
      refine ⟨15988617271491390175745323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85272625447954080937308389 15988617271491390175745323)
      ·
        refine ⟨23982925907237085263617985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15988617271491390175745323 23982925907237085263617985)
        ·
          refine ⟨17987194430427813947713489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23982925907237085263617985 17987194430427813947713489)
          ·
            refine ⟨13490395822820860460785117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17987194430427813947713489 13490395822820860460785117)
            ·
              refine ⟨5058898433557822672794419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13490395822820860460785117 5058898433557822672794419)
              ·
                refine ⟨7588347650336734009191629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058898433557822672794419 7588347650336734009191629)
                ·
                  refine ⟨2845630368876275253446861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7588347650336734009191629 2845630368876275253446861)
                  ·
                    refine ⟨1067111388328603220042573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845630368876275253446861 1067111388328603220042573)
                    ·
                      rfl

theorem cell22_3117288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_3117288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117288 prefixEnd_3117288 := by exact prefixLift 3117288
  have htrace : WordTrace (prefixWord ++ tailWord_3117288) baseStart_3117288 baseEnd_3117288 := by
    simpa [prefixWord, tailWord_3117288, baseEnd_3117288] using wordTrace_append hprefix tailTrace_3117288
  have hstable : (prefixWord ++ tailWord_3117288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117288).length < 2 ^ (prefixWord ++ tailWord_3117288).sum := by decide
  have hdescent : baseEnd_3117288 < baseStart_3117288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117299 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_3117299 : Nat := 118140960795 + 3117299 * 2 ^ 59
def prefixEnd_3117299 : Nat := 4983230072969 + 3 ^ 40 * 3117299 * 2
def baseEnd_3117299 : Nat := 1067115153853402858017539

theorem tailTrace_3117299 : CollatzResearch.WordTrace tailWord_3117299 prefixEnd_3117299 1067115153853402858017539 := by
  unfold tailWord_3117299
  simp only [CollatzResearch.WordTrace]
  refine ⟨113697235133565590128394951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75798156755710393418929967 113697235133565590128394951)
  ·
    refine ⟨170545852700348385192592427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113697235133565590128394951 170545852700348385192592427)
    ·
      refine ⟨255818779050522577788888641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170545852700348385192592427 255818779050522577788888641)
      ·
        refine ⟨191864084287891933341666481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255818779050522577788888641 191864084287891933341666481)
        ·
          refine ⟨143898063215918950006249861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191864084287891933341666481 143898063215918950006249861)
          ·
            refine ⟨26980886852984803126171849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143898063215918950006249861 26980886852984803126171849)
            ·
              refine ⟨20235665139738602344628887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26980886852984803126171849 20235665139738602344628887)
              ·
                refine ⟨30353497709607903516943331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20235665139738602344628887 30353497709607903516943331)
                ·
                  refine ⟨45530246564411855275414997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30353497709607903516943331 45530246564411855275414997)
                  ·
                    refine ⟨1067115153853402858017539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45530246564411855275414997 1067115153853402858017539)
                    ·
                      rfl

theorem cell22_3117299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_3117299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117299 prefixEnd_3117299 := by exact prefixLift 3117299
  have htrace : WordTrace (prefixWord ++ tailWord_3117299) baseStart_3117299 baseEnd_3117299 := by
    simpa [prefixWord, tailWord_3117299, baseEnd_3117299] using wordTrace_append hprefix tailTrace_3117299
  have hstable : (prefixWord ++ tailWord_3117299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117299).length < 2 ^ (prefixWord ++ tailWord_3117299).sum := by decide
  have hdescent : baseEnd_3117299 < baseStart_3117299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117331 : List Nat := [1, 1, 1, 2, 1, 3, 1, 7, 1, 4]
def baseStart_3117331 : Nat := 118140960795 + 3117331 * 2 ^ 59
def prefixEnd_3117331 : Nat := 4983230072969 + 3 ^ 40 * 3117331 * 2
def baseEnd_3117331 : Nat := 1067126108107365441217441

theorem tailTrace_3117331 : CollatzResearch.WordTrace tailWord_3117331 prefixEnd_3117331 1067126108107365441217441 := by
  unfold tailWord_3117331
  simp only [CollatzResearch.WordTrace]
  refine ⟨113698402269449659593559847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75798934846299773062373231 113698402269449659593559847)
  ·
    refine ⟨170547603404174489390339771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113698402269449659593559847 170547603404174489390339771)
    ·
      refine ⟨255821405106261734085509657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170547603404174489390339771 255821405106261734085509657)
      ·
        refine ⟨191866053829696300564132243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255821405106261734085509657 191866053829696300564132243)
        ·
          refine ⟨287799080744544450846198365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191866053829696300564132243 287799080744544450846198365)
          ·
            refine ⟨107924655279204169067324387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287799080744544450846198365 107924655279204169067324387)
            ·
              refine ⟨161886982918806253600986581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107924655279204169067324387 161886982918806253600986581)
              ·
                refine ⟨3794226162159521568773123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 161886982918806253600986581 3794226162159521568773123)
                ·
                  refine ⟨5691339243239282353159685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794226162159521568773123 5691339243239282353159685)
                  ·
                    refine ⟨1067126108107365441217441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691339243239282353159685 1067126108107365441217441)
                    ·
                      rfl

theorem cell22_3117331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 4].length) (baseStart_3117331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117331 prefixEnd_3117331 := by exact prefixLift 3117331
  have htrace : WordTrace (prefixWord ++ tailWord_3117331) baseStart_3117331 baseEnd_3117331 := by
    simpa [prefixWord, tailWord_3117331, baseEnd_3117331] using wordTrace_append hprefix tailTrace_3117331
  have hstable : (prefixWord ++ tailWord_3117331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117331).length < 2 ^ (prefixWord ++ tailWord_3117331).sum := by decide
  have hdescent : baseEnd_3117331 < baseStart_3117331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117376 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_3117376 : Nat := 118140960795 + 3117376 * 2 ^ 59
def prefixEnd_3117376 : Nat := 4983230072969 + 3 ^ 40 * 3117376 * 2
def baseEnd_3117376 : Nat := 1067141512527000323842303

theorem tailTrace_3117376 : CollatzResearch.WordTrace tailWord_3117376 prefixEnd_3117376 1067141512527000323842303 := by
  unfold tailWord_3117376
  simp only [CollatzResearch.WordTrace]
  refine ⟨56850021777143316139473991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75800029036191088185965321 56850021777143316139473991)
  ·
    refine ⟨85275032665714974209210987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56850021777143316139473991 85275032665714974209210987)
    ·
      refine ⟨127912548998572461313816481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85275032665714974209210987 127912548998572461313816481)
      ·
        refine ⟨95934411748929345985362361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127912548998572461313816481 95934411748929345985362361)
        ·
          refine ⟨71950808811697009489021771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95934411748929345985362361 71950808811697009489021771)
          ·
            refine ⟨107926213217545514233532657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71950808811697009489021771 107926213217545514233532657)
            ·
              refine ⟨80944659913159135675149493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107926213217545514233532657 80944659913159135675149493)
              ·
                refine ⟨7588561866858668969545265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80944659913159135675149493 7588561866858668969545265)
                ·
                  refine ⟨5691421400144001727158949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7588561866858668969545265 5691421400144001727158949)
                  ·
                    refine ⟨1067141512527000323842303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691421400144001727158949 1067141512527000323842303)
                    ·
                      rfl

theorem cell22_3117376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_3117376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117376 prefixEnd_3117376 := by exact prefixLift 3117376
  have htrace : WordTrace (prefixWord ++ tailWord_3117376) baseStart_3117376 baseEnd_3117376 := by
    simpa [prefixWord, tailWord_3117376, baseEnd_3117376] using wordTrace_append hprefix tailTrace_3117376
  have hstable : (prefixWord ++ tailWord_3117376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117376).length < 2 ^ (prefixWord ++ tailWord_3117376).sum := by decide
  have hdescent : baseEnd_3117376 < baseStart_3117376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117442 : List Nat := [3, 4, 2, 1, 3, 1, 8]
def baseStart_3117442 : Nat := 118140960795 + 3117442 * 2 ^ 59
def prefixEnd_3117442 : Nat := 4983230072969 + 3 ^ 40 * 3117442 * 2
def baseEnd_3117442 : Nat := 39524596506511042655263

theorem tailTrace_3117442 : CollatzResearch.WordTrace tailWord_3117442 prefixEnd_3117442 39524596506511042655263 := by
  unfold tailWord_3117442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28425612693011881387712645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75801633848031683700567053 28425612693011881387712645)
  ·
    refine ⟨5329802379939727760196121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28425612693011881387712645 5329802379939727760196121)
    ·
      refine ⟨3997351784954795820147091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5329802379939727760196121 3997351784954795820147091)
      ·
        refine ⟨5996027677432193730220637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997351784954795820147091 5996027677432193730220637)
        ·
          refine ⟨2248510379037072648832739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5996027677432193730220637 2248510379037072648832739)
          ·
            refine ⟨3372765568555608973249109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248510379037072648832739 3372765568555608973249109)
            ·
              refine ⟨39524596506511042655263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3372765568555608973249109 39524596506511042655263)
              ·
                rfl

theorem cell22_3117442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 8].length) (baseStart_3117442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117442 prefixEnd_3117442 := by exact prefixLift 3117442
  have htrace : WordTrace (prefixWord ++ tailWord_3117442) baseStart_3117442 baseEnd_3117442 := by
    simpa [prefixWord, tailWord_3117442, baseEnd_3117442] using wordTrace_append hprefix tailTrace_3117442
  have hstable : (prefixWord ++ tailWord_3117442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117442).length < 2 ^ (prefixWord ++ tailWord_3117442).sum := by decide
  have hdescent : baseEnd_3117442 < baseStart_3117442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117481 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 6]
def baseStart_3117481 : Nat := 118140960795 + 3117481 * 2 ^ 59
def prefixEnd_3117481 : Nat := 4983230072969 + 3 ^ 40 * 3117481 * 2
def baseEnd_3117481 : Nat := 355725818724271683322327

theorem tailTrace_3117481 : CollatzResearch.WordTrace tailWord_3117481 prefixEnd_3117481 355725818724271683322327 := by
  unfold tailWord_3117481
  simp only [CollatzResearch.WordTrace]
  refine ⟨113703873218906235211520297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75802582145937490141013531 113703873218906235211520297)
  ·
    refine ⟨85277904914179676408640223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113703873218906235211520297 85277904914179676408640223)
    ·
      refine ⟨127916857371269514612960335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85277904914179676408640223 127916857371269514612960335)
      ·
        refine ⟨191875286056904271919440503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127916857371269514612960335 191875286056904271919440503)
        ·
          refine ⟨287812929085356407879160755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191875286056904271919440503 287812929085356407879160755)
          ·
            refine ⟨431719393628034611818741133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287812929085356407879160755 431719393628034611818741133)
            ·
              refine ⟨161894772610512979432027925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431719393628034611818741133 161894772610512979432027925)
              ·
                refine ⟨7588817466117795910876309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161894772610512979432027925 7588817466117795910876309)
                ·
                  refine ⟨355725818724271683322327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7588817466117795910876309 355725818724271683322327)
                  ·
                    rfl

theorem cell22_3117481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_3117481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117481 prefixEnd_3117481 := by exact prefixLift 3117481
  have htrace : WordTrace (prefixWord ++ tailWord_3117481) baseStart_3117481 baseEnd_3117481 := by
    simpa [prefixWord, tailWord_3117481, baseEnd_3117481] using wordTrace_append hprefix tailTrace_3117481
  have hstable : (prefixWord ++ tailWord_3117481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117481).length < 2 ^ (prefixWord ++ tailWord_3117481).sum := by decide
  have hdescent : baseEnd_3117481 < baseStart_3117481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117508 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3117508 : Nat := 118140960795 + 3117508 * 2 ^ 59
def prefixEnd_3117508 : Nat := 4983230072969 + 3 ^ 40 * 3117508 * 2
def baseEnd_3117508 : Nat := 1067186698824595979541899

theorem tailTrace_3117508 : CollatzResearch.WordTrace tailWord_3117508 prefixEnd_3117508 1067186698824595979541899 := by
  unfold tailWord_3117508
  simp only [CollatzResearch.WordTrace]
  refine ⟨56852428994904209411376589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75803238659872279215168785 56852428994904209411376589)
  ·
    refine ⟨21319660873089078529266221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56852428994904209411376589 21319660873089078529266221)
    ·
      refine ⟨7994872827408404448474833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21319660873089078529266221 7994872827408404448474833)
      ·
        refine ⟨5996154620556303336356125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7994872827408404448474833 5996154620556303336356125)
        ·
          refine ⟨2248557982708613751133547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5996154620556303336356125 2248557982708613751133547)
          ·
            refine ⟨3372836974062920626700321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248557982708613751133547 3372836974062920626700321)
            ·
              refine ⟨2529627730547190470025241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372836974062920626700321 2529627730547190470025241)
              ·
                refine ⟨1897220797910392852518931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529627730547190470025241 1897220797910392852518931)
                ·
                  refine ⟨2845831196865589278778397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897220797910392852518931 2845831196865589278778397)
                  ·
                    refine ⟨1067186698824595979541899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845831196865589278778397 1067186698824595979541899)
                    ·
                      rfl

theorem cell22_3117508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3117508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117508 prefixEnd_3117508 := by exact prefixLift 3117508
  have htrace : WordTrace (prefixWord ++ tailWord_3117508) baseStart_3117508 baseEnd_3117508 := by
    simpa [prefixWord, tailWord_3117508, baseEnd_3117508] using wordTrace_append hprefix tailTrace_3117508
  have hstable : (prefixWord ++ tailWord_3117508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117508).length < 2 ^ (prefixWord ++ tailWord_3117508).sum := by decide
  have hdescent : baseEnd_3117508 < baseStart_3117508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117513 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_3117513 : Nat := 118140960795 + 3117513 * 2 ^ 59
def prefixEnd_3117513 : Nat := 4983230072969 + 3 ^ 40 * 3117513 * 2
def baseEnd_3117513 : Nat := 1067188410426777633166883

theorem tailTrace_3117513 : CollatzResearch.WordTrace tailWord_3117513 prefixEnd_3117513 1067188410426777633166883 := by
  unfold tailWord_3117513
  simp only [CollatzResearch.WordTrace]
  refine ⟨113705040354790304676685193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75803360236526869784456795 113705040354790304676685193)
  ·
    refine ⟨85278780266092728507513895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113705040354790304676685193 85278780266092728507513895)
    ·
      refine ⟨127918170399139092761270843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85278780266092728507513895 127918170399139092761270843)
      ·
        refine ⟨191877255598708639141906265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127918170399139092761270843 191877255598708639141906265)
        ·
          refine ⟨143907941699031479356429699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191877255598708639141906265 143907941699031479356429699)
          ·
            refine ⟨215861912548547219034644549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143907941699031479356429699 215861912548547219034644549)
            ·
              refine ⟨40474108602852603568995853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215861912548547219034644549 40474108602852603568995853)
              ·
                refine ⟨15177790726069726338373445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40474108602852603568995853 15177790726069726338373445)
                ·
                  refine ⟨2845835761138073688445021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15177790726069726338373445 2845835761138073688445021)
                  ·
                    refine ⟨1067188410426777633166883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845835761138073688445021 1067188410426777633166883)
                    ·
                      rfl

theorem cell22_3117513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_3117513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117513 prefixEnd_3117513 := by exact prefixLift 3117513
  have htrace : WordTrace (prefixWord ++ tailWord_3117513) baseStart_3117513 baseEnd_3117513 := by
    simpa [prefixWord, tailWord_3117513, baseEnd_3117513] using wordTrace_append hprefix tailTrace_3117513
  have hstable : (prefixWord ++ tailWord_3117513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117513).length < 2 ^ (prefixWord ++ tailWord_3117513).sum := by decide
  have hdescent : baseEnd_3117513 < baseStart_3117513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117530 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_3117530 : Nat := 118140960795 + 3117530 * 2 ^ 59
def prefixEnd_3117530 : Nat := 4983230072969 + 3 ^ 40 * 3117530 * 2
def baseEnd_3117530 : Nat := 1067194229874195255491831

theorem tailTrace_3117530 : CollatzResearch.WordTrace tailWord_3117530 prefixEnd_3117530 1067194229874195255491831 := by
  unfold tailWord_3117530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28426415098932179145013511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75803773597152477720036029 28426415098932179145013511)
  ·
    refine ⟨42639622648398268717520267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28426415098932179145013511 42639622648398268717520267)
    ·
      refine ⟨63959433972597403076280401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42639622648398268717520267 63959433972597403076280401)
      ·
        refine ⟨47969575479448052307210301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63959433972597403076280401 47969575479448052307210301)
        ·
          refine ⟨17988590804793019615203863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47969575479448052307210301 17988590804793019615203863)
          ·
            refine ⟨26982886207189529422805795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17988590804793019615203863 26982886207189529422805795)
            ·
              refine ⟨40474329310784294134208693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26982886207189529422805795 40474329310784294134208693)
              ·
                refine ⟨3794468372886027575082065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40474329310784294134208693 3794468372886027575082065)
                ·
                  refine ⟨2845851279664520681311549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3794468372886027575082065 2845851279664520681311549)
                  ·
                    refine ⟨1067194229874195255491831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2845851279664520681311549 1067194229874195255491831)
                    ·
                      rfl

theorem cell22_3117530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_3117530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117530 prefixEnd_3117530 := by exact prefixLift 3117530
  have htrace : WordTrace (prefixWord ++ tailWord_3117530) baseStart_3117530 baseEnd_3117530 := by
    simpa [prefixWord, tailWord_3117530, baseEnd_3117530] using wordTrace_append hprefix tailTrace_3117530
  have hstable : (prefixWord ++ tailWord_3117530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117530).length < 2 ^ (prefixWord ++ tailWord_3117530).sum := by decide
  have hdescent : baseEnd_3117530 < baseStart_3117530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117652 : List Nat := [2, 4, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3117652 : Nat := 118140960795 + 3117652 * 2 ^ 59
def prefixEnd_3117652 : Nat := 4983230072969 + 3 ^ 40 * 3117652 * 2
def baseEnd_3117652 : Nat := 1067235992967427603941457

theorem tailTrace_3117652 : CollatzResearch.WordTrace tailWord_3117652 prefixEnd_3117652 1067235992967427603941457 := by
  unfold tailWord_3117652
  simp only [CollatzResearch.WordTrace]
  refine ⟨56855055050643365707997605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75806740067524487610663473 56855055050643365707997605)
  ·
    refine ⟨10660322821995631070249551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56855055050643365707997605 10660322821995631070249551)
    ·
      refine ⟨15990484232993446605374327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10660322821995631070249551 15990484232993446605374327)
      ·
        refine ⟨23985726349490169908061491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15990484232993446605374327 23985726349490169908061491)
        ·
          refine ⟨35978589524235254862092237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23985726349490169908061491 35978589524235254862092237)
          ·
            refine ⟨13491971071588220573284589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35978589524235254862092237 13491971071588220573284589)
            ·
              refine ⟨5059489151845582714981721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13491971071588220573284589 5059489151845582714981721)
              ·
                refine ⟨3794616863884187036236291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5059489151845582714981721 3794616863884187036236291)
                ·
                  refine ⟨5691925295826280554354437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794616863884187036236291 5691925295826280554354437)
                  ·
                    refine ⟨1067235992967427603941457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691925295826280554354437 1067235992967427603941457)
                    ·
                      rfl

theorem cell22_3117652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3117652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117652 prefixEnd_3117652 := by exact prefixLift 3117652
  have htrace : WordTrace (prefixWord ++ tailWord_3117652) baseStart_3117652 baseEnd_3117652 := by
    simpa [prefixWord, tailWord_3117652, baseEnd_3117652] using wordTrace_append hprefix tailTrace_3117652
  have hstable : (prefixWord ++ tailWord_3117652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117652).length < 2 ^ (prefixWord ++ tailWord_3117652).sum := by decide
  have hdescent : baseEnd_3117652 < baseStart_3117652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117663 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_3117663 : Nat := 118140960795 + 3117663 * 2 ^ 59
def prefixEnd_3117663 : Nat := 4983230072969 + 3 ^ 40 * 3117663 * 2
def baseEnd_3117663 : Nat := 1067239758492227241916423

theorem tailTrace_3117663 : CollatzResearch.WordTrace tailWord_3117663 prefixEnd_3117663 1067239758492227241916423 := by
  unfold tailWord_3117663
  simp only [CollatzResearch.WordTrace]
  refine ⟨113710511304246880294645643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75807007536164586863097095 113710511304246880294645643)
  ·
    refine ⟨170565766956370320441968465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113710511304246880294645643 170565766956370320441968465)
    ·
      refine ⟨127924325217277740331476349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170565766956370320441968465 127924325217277740331476349)
      ·
        refine ⟨47971621956479152624303631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127924325217277740331476349 47971621956479152624303631)
        ·
          refine ⟨71957432934718728936455447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47971621956479152624303631 71957432934718728936455447)
          ·
            refine ⟨107936149402078093404683171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71957432934718728936455447 107936149402078093404683171)
            ·
              refine ⟨161904224103117140107024757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107936149402078093404683171 161904224103117140107024757)
              ·
                refine ⟨15178521009667231885033571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161904224103117140107024757 15178521009667231885033571)
                ·
                  refine ⟨22767781514500847827550357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15178521009667231885033571 22767781514500847827550357)
                  ·
                    refine ⟨1067239758492227241916423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22767781514500847827550357 1067239758492227241916423)
                    ·
                      rfl

theorem cell22_3117663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_3117663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117663 prefixEnd_3117663 := by exact prefixLift 3117663
  have htrace : WordTrace (prefixWord ++ tailWord_3117663) baseStart_3117663 baseEnd_3117663 := by
    simpa [prefixWord, tailWord_3117663, baseEnd_3117663] using wordTrace_append hprefix tailTrace_3117663
  have hstable : (prefixWord ++ tailWord_3117663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117663).length < 2 ^ (prefixWord ++ tailWord_3117663).sum := by decide
  have hdescent : baseEnd_3117663 < baseStart_3117663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117665 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3117665 : Nat := 118140960795 + 3117665 * 2 ^ 59
def prefixEnd_3117665 : Nat := 4983230072969 + 3 ^ 40 * 3117665 * 2
def baseEnd_3117665 : Nat := 1067240443133099903366417

theorem tailTrace_3117665 : CollatzResearch.WordTrace tailWord_3117665 prefixEnd_3117665 1067240443133099903366417 := by
  unfold tailWord_3117665
  simp only [CollatzResearch.WordTrace]
  refine ⟨113710584250239634636218449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75807056166826423090812299 113710584250239634636218449)
  ·
    refine ⟨85282938187679725977163837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113710584250239634636218449 85282938187679725977163837)
    ·
      refine ⟨31981101820379897241436439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85282938187679725977163837 31981101820379897241436439)
      ·
        refine ⟨47971652730569845862154659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31981101820379897241436439 47971652730569845862154659)
        ·
          refine ⟨71957479095854768793231989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47971652730569845862154659 71957479095854768793231989)
          ·
            refine ⟨6746013665236384574365499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71957479095854768793231989 6746013665236384574365499)
            ·
              refine ⟨10119020497854576861548249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746013665236384574365499 10119020497854576861548249)
              ·
                refine ⟨7589265373390932646161187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10119020497854576861548249 7589265373390932646161187)
                ·
                  refine ⟨11383898060086398969241781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7589265373390932646161187 11383898060086398969241781)
                  ·
                    refine ⟨1067240443133099903366417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11383898060086398969241781 1067240443133099903366417)
                    ·
                      rfl

theorem cell22_3117665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3117665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117665 prefixEnd_3117665 := by exact prefixLift 3117665
  have htrace : WordTrace (prefixWord ++ tailWord_3117665) baseStart_3117665 baseEnd_3117665 := by
    simpa [prefixWord, tailWord_3117665, baseEnd_3117665] using wordTrace_append hprefix tailTrace_3117665
  have hstable : (prefixWord ++ tailWord_3117665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117665).length < 2 ^ (prefixWord ++ tailWord_3117665).sum := by decide
  have hdescent : baseEnd_3117665 < baseStart_3117665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117669 : List Nat := [1, 3, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_3117669 : Nat := 118140960795 + 3117669 * 2 ^ 59
def prefixEnd_3117669 : Nat := 4983230072969 + 3 ^ 40 * 3117669 * 2
def baseEnd_3117669 : Nat := 1067241812414845226266405

theorem tailTrace_3117669 : CollatzResearch.WordTrace tailWord_3117669 prefixEnd_3117669 1067241812414845226266405 := by
  unfold tailWord_3117669
  simp only [CollatzResearch.WordTrace]
  refine ⟨113710730142225143319364061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75807153428150095546242707 113710730142225143319364061)
  ·
    refine ⟨42641523803334428744761523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113710730142225143319364061 42641523803334428744761523)
    ·
      refine ⟨63962285705001643117142285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42641523803334428744761523 63962285705001643117142285)
      ·
        refine ⟨23985857139375616168928357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63962285705001643117142285 23985857139375616168928357)
        ·
          refine ⟨4497348213632928031674067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23985857139375616168928357 4497348213632928031674067)
          ·
            refine ⟨6746022320449392047511101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497348213632928031674067 6746022320449392047511101)
            ·
              refine ⟨2529758370168522017816663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6746022320449392047511101 2529758370168522017816663)
              ·
                refine ⟨3794637555252783026724995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529758370168522017816663 3794637555252783026724995)
                ·
                  refine ⟨5691956332879174540087493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794637555252783026724995 5691956332879174540087493)
                  ·
                    refine ⟨1067241812414845226266405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691956332879174540087493 1067241812414845226266405)
                    ·
                      rfl

theorem cell22_3117669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_3117669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117669 prefixEnd_3117669 := by exact prefixLift 3117669
  have htrace : WordTrace (prefixWord ++ tailWord_3117669) baseStart_3117669 baseEnd_3117669 := by
    simpa [prefixWord, tailWord_3117669, baseEnd_3117669] using wordTrace_append hprefix tailTrace_3117669
  have hstable : (prefixWord ++ tailWord_3117669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117669).length < 2 ^ (prefixWord ++ tailWord_3117669).sum := by decide
  have hdescent : baseEnd_3117669 < baseStart_3117669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117714 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3117714 : Nat := 118140960795 + 3117714 * 2 ^ 59
def prefixEnd_3117714 : Nat := 4983230072969 + 3 ^ 40 * 3117714 * 2
def baseEnd_3117714 : Nat := 1067257216834480108891267

theorem tailTrace_3117714 : CollatzResearch.WordTrace tailWord_3117714 prefixEnd_3117714 1067257216834480108891267 := by
  unfold tailWord_3117714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28428092856765529001188049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75808247618041410669834797 28428092856765529001188049)
  ·
    refine ⟨21321069642574146750891037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28428092856765529001188049 21321069642574146750891037)
    ·
      refine ⟨7995401115965305031584139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21321069642574146750891037 7995401115965305031584139)
      ·
        refine ⟨11993101673947957547376209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7995401115965305031584139 11993101673947957547376209)
        ·
          refine ⟨8994826255460968160532157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11993101673947957547376209 8994826255460968160532157)
          ·
            refine ⟨3373059845797863060199559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8994826255460968160532157 3373059845797863060199559)
            ·
              refine ⟨5059589768696794590299339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373059845797863060199559 5059589768696794590299339)
              ·
                refine ⟨7589384653045191885449009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059589768696794590299339 7589384653045191885449009)
                ·
                  refine ⟨5692038489783893914086757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7589384653045191885449009 5692038489783893914086757)
                  ·
                    refine ⟨1067257216834480108891267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692038489783893914086757 1067257216834480108891267)
                    ·
                      rfl

theorem cell22_3117714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3117714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117714 prefixEnd_3117714 := by exact prefixLift 3117714
  have htrace : WordTrace (prefixWord ++ tailWord_3117714) baseStart_3117714 baseEnd_3117714 := by
    simpa [prefixWord, tailWord_3117714, baseEnd_3117714] using wordTrace_append hprefix tailTrace_3117714
  have hstable : (prefixWord ++ tailWord_3117714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117714).length < 2 ^ (prefixWord ++ tailWord_3117714).sum := by decide
  have hdescent : baseEnd_3117714 < baseStart_3117714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117778 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3117778 : Nat := 118140960795 + 3117778 * 2 ^ 59
def prefixEnd_3117778 : Nat := 4983230072969 + 3 ^ 40 * 3117778 * 2
def baseEnd_3117778 : Nat := 1067279125342405275291071

theorem tailTrace_3117778 : CollatzResearch.WordTrace tailWord_3117778 prefixEnd_3117778 1067279125342405275291071 := by
  unfold tailWord_3117778
  simp only [CollatzResearch.WordTrace]
  refine ⟨28428676424707563733770497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75809803799220169956721325 28428676424707563733770497)
  ·
    refine ⟨21321507318530672800327873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28428676424707563733770497 21321507318530672800327873)
    ·
      refine ⟨15991130488898004600245905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21321507318530672800327873 15991130488898004600245905)
      ·
        refine ⟨11993347866673503450184429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15991130488898004600245905 11993347866673503450184429)
        ·
          refine ⟨4497505450002563793819161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11993347866673503450184429 4497505450002563793819161)
          ·
            refine ⟨3373129087501922845364371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4497505450002563793819161 3373129087501922845364371)
            ·
              refine ⟨5059693631252884268046557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373129087501922845364371 5059693631252884268046557)
              ·
                refine ⟨1897385111719831600517459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5059693631252884268046557 1897385111719831600517459)
                ·
                  refine ⟨2846077667579747400776189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897385111719831600517459 2846077667579747400776189)
                  ·
                    refine ⟨1067279125342405275291071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846077667579747400776189 1067279125342405275291071)
                    ·
                      rfl

theorem cell22_3117778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3117778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117778 prefixEnd_3117778 := by exact prefixLift 3117778
  have htrace : WordTrace (prefixWord ++ tailWord_3117778) baseStart_3117778 baseEnd_3117778 := by
    simpa [prefixWord, tailWord_3117778, baseEnd_3117778] using wordTrace_append hprefix tailTrace_3117778
  have hstable : (prefixWord ++ tailWord_3117778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117778).length < 2 ^ (prefixWord ++ tailWord_3117778).sum := by decide
  have hdescent : baseEnd_3117778 < baseStart_3117778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117815 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 6, 4]
def baseStart_3117815 : Nat := 118140960795 + 3117815 * 2 ^ 59
def prefixEnd_3117815 : Nat := 4983230072969 + 3 ^ 40 * 3117815 * 2
def baseEnd_3117815 : Nat := 1067291791198549512115957

theorem tailTrace_3117815 : CollatzResearch.WordTrace tailWord_3117815 prefixEnd_3117815 1067291791198549512115957 := by
  unfold tailWord_3117815
  simp only [CollatzResearch.WordTrace]
  refine ⟨113716055199696210254178899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75810703466464140169452599 113716055199696210254178899)
  ·
    refine ⟨170574082799544315381268349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113716055199696210254178899 170574082799544315381268349)
    ·
      refine ⟨63965281049829118267975631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170574082799544315381268349 63965281049829118267975631)
      ·
        refine ⟨95947921574743677401963447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63965281049829118267975631 95947921574743677401963447)
        ·
          refine ⟨143921882362115516102945171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95947921574743677401963447 143921882362115516102945171)
          ·
            refine ⟨215882823543173274154417757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143921882362115516102945171 215882823543173274154417757)
            ·
              refine ⟨80956058828689977807906659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215882823543173274154417757 80956058828689977807906659)
              ·
                refine ⟨121434088243034966711859989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80956058828689977807906659 121434088243034966711859989)
                ·
                  refine ⟨5692222886392264064618437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121434088243034966711859989 5692222886392264064618437)
                  ·
                    refine ⟨1067291791198549512115957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692222886392264064618437 1067291791198549512115957)
                    ·
                      rfl

theorem cell22_3117815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_3117815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117815 prefixEnd_3117815 := by exact prefixLift 3117815
  have htrace : WordTrace (prefixWord ++ tailWord_3117815) baseStart_3117815 baseEnd_3117815 := by
    simpa [prefixWord, tailWord_3117815, baseEnd_3117815] using wordTrace_append hprefix tailTrace_3117815
  have hstable : (prefixWord ++ tailWord_3117815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117815).length < 2 ^ (prefixWord ++ tailWord_3117815).sum := by decide
  have hdescent : baseEnd_3117815 < baseStart_3117815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117832 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3117832 : Nat := 118140960795 + 3117832 * 2 ^ 59
def prefixEnd_3117832 : Nat := 4983230072969 + 3 ^ 40 * 3117832 * 2
def baseEnd_3117832 : Nat := 1067297610645967134440905

theorem tailTrace_3117832 : CollatzResearch.WordTrace tailWord_3117832 prefixEnd_3117832 1067297610645967134440905 := by
  unfold tailWord_3117832
  simp only [CollatzResearch.WordTrace]
  refine ⟨56858337620317311078773875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75811116827089748105031833 56858337620317311078773875)
  ·
    refine ⟨85287506430475966618160813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56858337620317311078773875 85287506430475966618160813)
    ·
      refine ⟨31982814911428487481810305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85287506430475966618160813 31982814911428487481810305)
      ·
        refine ⟨23987111183571365611357729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31982814911428487481810305 23987111183571365611357729)
        ·
          refine ⟨17990333387678524208518297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23987111183571365611357729 17990333387678524208518297)
          ·
            refine ⟨13492750040758893156388723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17990333387678524208518297 13492750040758893156388723)
            ·
              refine ⟨20239125061138339734583085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492750040758893156388723 20239125061138339734583085)
              ·
                refine ⟨7589671897926877400468657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20239125061138339734583085 7589671897926877400468657)
                ·
                  refine ⟨5692253923445158050351493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7589671897926877400468657 5692253923445158050351493)
                  ·
                    refine ⟨1067297610645967134440905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692253923445158050351493 1067297610645967134440905)
                    ·
                      rfl

theorem cell22_3117832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3117832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117832 prefixEnd_3117832 := by exact prefixLift 3117832
  have htrace : WordTrace (prefixWord ++ tailWord_3117832) baseStart_3117832 baseEnd_3117832 := by
    simpa [prefixWord, tailWord_3117832, baseEnd_3117832] using wordTrace_append hprefix tailTrace_3117832
  have hstable : (prefixWord ++ tailWord_3117832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117832).length < 2 ^ (prefixWord ++ tailWord_3117832).sum := by decide
  have hdescent : baseEnd_3117832 < baseStart_3117832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117847 : List Nat := [1, 1, 3, 4, 4, 9]
def baseStart_3117847 : Nat := 118140960795 + 3117847 * 2 ^ 59
def prefixEnd_3117847 : Nat := 4983230072969 + 3 ^ 40 * 3117847 * 2
def baseEnd_3117847 : Nat := 13176577104352001176739

theorem tailTrace_3117847 : CollatzResearch.WordTrace tailWord_3117847 prefixEnd_3117847 13176577104352001176739 := by
  unfold tailWord_3117847
  simp only [CollatzResearch.WordTrace]
  refine ⟨113717222335580279719343795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75811481557053519812895863 113717222335580279719343795)
  ·
    refine ⟨170575833503370419579015693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113717222335580279719343795 170575833503370419579015693)
    ·
      refine ⟨63965937563763907342130885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170575833503370419579015693 63965937563763907342130885)
      ·
        refine ⟨11993613293205732626649541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63965937563763907342130885 11993613293205732626649541)
        ·
          refine ⟨2248802492476074867496789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11993613293205732626649541 2248802492476074867496789)
          ·
            refine ⟨13176577104352001176739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2248802492476074867496789 13176577104352001176739)
            ·
              rfl

theorem cell22_3117847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 9].length) (baseStart_3117847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117847 prefixEnd_3117847 := by exact prefixLift 3117847
  have htrace : WordTrace (prefixWord ++ tailWord_3117847) baseStart_3117847 baseEnd_3117847 := by
    simpa [prefixWord, tailWord_3117847, baseEnd_3117847] using wordTrace_append hprefix tailTrace_3117847
  have hstable : (prefixWord ++ tailWord_3117847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117847).length < 2 ^ (prefixWord ++ tailWord_3117847).sum := by decide
  have hdescent : baseEnd_3117847 < baseStart_3117847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117896 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 1, 3]
def baseStart_3117896 : Nat := 118140960795 + 3117896 * 2 ^ 59
def prefixEnd_3117896 : Nat := 4983230072969 + 3 ^ 40 * 3117896 * 2
def baseEnd_3117896 : Nat := 1067319519153892300840709

theorem tailTrace_3117896 : CollatzResearch.WordTrace tailWord_3117896 prefixEnd_3117896 1067319519153892300840709 := by
  unfold tailWord_3117896
  simp only [CollatzResearch.WordTrace]
  refine ⟨56859504756201380543938771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75812673008268507391918361 56859504756201380543938771)
  ·
    refine ⟨85289257134302070815908157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56859504756201380543938771 85289257134302070815908157)
    ·
      refine ⟨31983471425363276555965559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85289257134302070815908157 31983471425363276555965559)
      ·
        refine ⟨47975207138044914833948339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31983471425363276555965559 47975207138044914833948339)
        ·
          refine ⟨71962810707067372250922509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47975207138044914833948339 71962810707067372250922509)
          ·
            refine ⟨26986054015150264594095941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71962810707067372250922509 26986054015150264594095941)
            ·
              refine ⟨5059885127840674611392989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26986054015150264594095941 5059885127840674611392989)
              ·
                refine ⟨1897456922940252979272371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5059885127840674611392989 1897456922940252979272371)
                ·
                  refine ⟨2846185384410379468908557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897456922940252979272371 2846185384410379468908557)
                  ·
                    refine ⟨1067319519153892300840709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846185384410379468908557 1067319519153892300840709)
                    ·
                      rfl

theorem cell22_3117896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_3117896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117896 prefixEnd_3117896 := by exact prefixLift 3117896
  have htrace : WordTrace (prefixWord ++ tailWord_3117896) baseStart_3117896 baseEnd_3117896 := by
    simpa [prefixWord, tailWord_3117896, baseEnd_3117896] using wordTrace_append hprefix tailTrace_3117896
  have hstable : (prefixWord ++ tailWord_3117896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117896).length < 2 ^ (prefixWord ++ tailWord_3117896).sum := by decide
  have hdescent : baseEnd_3117896 < baseStart_3117896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117937 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 6]
def baseStart_3117937 : Nat := 118140960795 + 3117937 * 2 ^ 59
def prefixEnd_3117937 : Nat := 4983230072969 + 3 ^ 40 * 3117937 * 2
def baseEnd_3117937 : Nat := 355777851430593953521861

theorem tailTrace_3117937 : CollatzResearch.WordTrace tailWord_3117937 prefixEnd_3117937 355777851430593953521861 := by
  unfold tailWord_3117937
  simp only [CollatzResearch.WordTrace]
  refine ⟨113720504905254225090120065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75813669936836150060080043 113720504905254225090120065)
  ·
    refine ⟨85290378678940668817590049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113720504905254225090120065 85290378678940668817590049)
    ·
      refine ⟨63967784009205501613192537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85290378678940668817590049 63967784009205501613192537)
      ·
        refine ⟨47975838006904126209894403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63967784009205501613192537 47975838006904126209894403)
        ·
          refine ⟨71963757010356189314841605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47975838006904126209894403 71963757010356189314841605)
          ·
            refine ⟨13493204439441785496532801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71963757010356189314841605 13493204439441785496532801)
            ·
              refine ⟨10119903329581339122399601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13493204439441785496532801 10119903329581339122399601)
              ·
                refine ⟨7589927497186004341799701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10119903329581339122399601 7589927497186004341799701)
                ·
                  refine ⟨355777851430593953521861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7589927497186004341799701 355777851430593953521861)
                  ·
                    rfl

theorem cell22_3117937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_3117937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117937 prefixEnd_3117937 := by exact prefixLift 3117937
  have htrace : WordTrace (prefixWord ++ tailWord_3117937) baseStart_3117937 baseEnd_3117937 := by
    simpa [prefixWord, tailWord_3117937, baseEnd_3117937] using wordTrace_append hprefix tailTrace_3117937
  have hstable : (prefixWord ++ tailWord_3117937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117937).length < 2 ^ (prefixWord ++ tailWord_3117937).sum := by decide
  have hdescent : baseEnd_3117937 < baseStart_3117937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3117969 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_3117969 : Nat := 118140960795 + 3117969 * 2 ^ 59
def prefixEnd_3117969 : Nat := 4983230072969 + 3 ^ 40 * 3117969 * 2
def baseEnd_3117969 : Nat := 1067344508545744443765485

theorem tailTrace_3117969 : CollatzResearch.WordTrace tailWord_3117969 prefixEnd_3117969 1067344508545744443765485 := by
  unfold tailWord_3117969
  simp only [CollatzResearch.WordTrace]
  refine ⟨113721672041138294555284961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75814448027425529703523307 113721672041138294555284961)
  ·
    refine ⟨85291254030853720916463721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113721672041138294555284961 85291254030853720916463721)
    ·
      refine ⟨63968440523140290687347791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85291254030853720916463721 63968440523140290687347791)
      ·
        refine ⟨95952660784710436031021687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63968440523140290687347791 95952660784710436031021687)
        ·
          refine ⟨143928991177065654046532531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95952660784710436031021687 143928991177065654046532531)
          ·
            refine ⟨215893486765598481069798797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143928991177065654046532531 215893486765598481069798797)
            ·
              refine ⟨80960057537099430401174549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215893486765598481069798797 80960057537099430401174549)
              ·
                refine ⟨3795002697051535800055057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80960057537099430401174549 3795002697051535800055057)
                ·
                  refine ⟨2846252022788651850041293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3795002697051535800055057 2846252022788651850041293)
                  ·
                    refine ⟨1067344508545744443765485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846252022788651850041293 1067344508545744443765485)
                    ·
                      rfl

theorem cell22_3117969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_3117969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3117969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3117969 prefixEnd_3117969 := by exact prefixLift 3117969
  have htrace : WordTrace (prefixWord ++ tailWord_3117969) baseStart_3117969 baseEnd_3117969 := by
    simpa [prefixWord, tailWord_3117969, baseEnd_3117969] using wordTrace_append hprefix tailTrace_3117969
  have hstable : (prefixWord ++ tailWord_3117969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3117969).length < 2 ^ (prefixWord ++ tailWord_3117969).sum := by decide
  have hdescent : baseEnd_3117969 < baseStart_3117969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3117969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118001 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3118001 : Nat := 118140960795 + 3118001 * 2 ^ 59
def prefixEnd_3118001 : Nat := 4983230072969 + 3 ^ 40 * 3118001 * 2
def baseEnd_3118001 : Nat := 1067355462799707026965387

theorem tailTrace_3118001 : CollatzResearch.WordTrace tailWord_3118001 prefixEnd_3118001 1067355462799707026965387 := by
  unfold tailWord_3118001
  simp only [CollatzResearch.WordTrace]
  refine ⟨113722839177022364020449857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75815226118014909346966571 113722839177022364020449857)
  ·
    refine ⟨85292129382766773015337393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113722839177022364020449857 85292129382766773015337393)
    ·
      refine ⟨63969097037075079761503045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85292129382766773015337393 63969097037075079761503045)
      ·
        refine ⟨11994205694451577455281821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63969097037075079761503045 11994205694451577455281821)
        ·
          refine ⟨4497827135419341545730683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11994205694451577455281821 4497827135419341545730683)
          ·
            refine ⟨6746740703129012318596025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497827135419341545730683 6746740703129012318596025)
            ·
              refine ⟨5060055527346759238947019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746740703129012318596025 5060055527346759238947019)
              ·
                refine ⟨7590083291020138858420529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060055527346759238947019 7590083291020138858420529)
                ·
                  refine ⟨5692562468265104143815397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590083291020138858420529 5692562468265104143815397)
                  ·
                    refine ⟨1067355462799707026965387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692562468265104143815397 1067355462799707026965387)
                    ·
                      rfl

theorem cell22_3118001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3118001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118001 prefixEnd_3118001 := by exact prefixLift 3118001
  have htrace : WordTrace (prefixWord ++ tailWord_3118001) baseStart_3118001 baseEnd_3118001 := by
    simpa [prefixWord, tailWord_3118001, baseEnd_3118001] using wordTrace_append hprefix tailTrace_3118001
  have hstable : (prefixWord ++ tailWord_3118001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118001).length < 2 ^ (prefixWord ++ tailWord_3118001).sum := by decide
  have hdescent : baseEnd_3118001 < baseStart_3118001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118020 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3118020 : Nat := 118140960795 + 3118020 * 2 ^ 59
def prefixEnd_3118020 : Nat := 4983230072969 + 3 ^ 40 * 3118020 * 2
def baseEnd_3118020 : Nat := 1067361966887997310740329

theorem tailTrace_3118020 : CollatzResearch.WordTrace tailWord_3118020 prefixEnd_3118020 1067361966887997310740329 := by
  unfold tailWord_3118020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56861766081976765132695757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75815688109302353510261009 56861766081976765132695757)
  ·
    refine ⟨21323162280741286924760909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56861766081976765132695757 21323162280741286924760909)
    ·
      refine ⟨7996185855277982596785341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21323162280741286924760909 7996185855277982596785341)
      ·
        refine ⟨2998569695729243473794503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7996185855277982596785341 2998569695729243473794503)
        ·
          refine ⟨4497854543593865210691755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2998569695729243473794503 4497854543593865210691755)
          ·
            refine ⟨6746781815390797816037633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497854543593865210691755 6746781815390797816037633)
            ·
              refine ⟨5060086361543098362028225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746781815390797816037633 5060086361543098362028225)
              ·
                refine ⟨3795064771157323771521169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060086361543098362028225 3795064771157323771521169)
                ·
                  refine ⟨2846298578367992828640877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3795064771157323771521169 2846298578367992828640877)
                  ·
                    refine ⟨1067361966887997310740329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846298578367992828640877 1067361966887997310740329)
                    ·
                      rfl

theorem cell22_3118020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3118020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118020 prefixEnd_3118020 := by exact prefixLift 3118020
  have htrace : WordTrace (prefixWord ++ tailWord_3118020) baseStart_3118020 baseEnd_3118020 := by
    simpa [prefixWord, tailWord_3118020, baseEnd_3118020] using wordTrace_append hprefix tailTrace_3118020
  have hstable : (prefixWord ++ tailWord_3118020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118020).length < 2 ^ (prefixWord ++ tailWord_3118020).sum := by decide
  have hdescent : baseEnd_3118020 < baseStart_3118020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118072 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_3118072 : Nat := 118140960795 + 3118072 * 2 ^ 59
def prefixEnd_3118072 : Nat := 4983230072969 + 3 ^ 40 * 3118072 * 2
def baseEnd_3118072 : Nat := 355793255850228836146723

theorem tailTrace_3118072 : CollatzResearch.WordTrace tailWord_3118072 prefixEnd_3118072 355793255850228836146723 := by
  unfold tailWord_3118072
  simp only [CollatzResearch.WordTrace]
  refine ⟨56862714379882571573142235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75816952506510095430856313 56862714379882571573142235)
  ·
    refine ⟨85294071569823857359713353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56862714379882571573142235 85294071569823857359713353)
    ·
      refine ⟨63970553677367893019785015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85294071569823857359713353 63970553677367893019785015)
      ·
        refine ⟨95955830516051839529677523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63970553677367893019785015 95955830516051839529677523)
        ·
          refine ⟨143933745774077759294516285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95955830516051839529677523 143933745774077759294516285)
          ·
            refine ⟨53975154665279159735443607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143933745774077759294516285 53975154665279159735443607)
            ·
              refine ⟨80962731997918739603165411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53975154665279159735443607 80962731997918739603165411)
              ·
                refine ⟨121444097996878109404748117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80962731997918739603165411 121444097996878109404748117)
                ·
                  refine ⟨355793255850228836146723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121444097996878109404748117 355793255850228836146723)
                  ·
                    rfl

theorem cell22_3118072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_3118072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118072 prefixEnd_3118072 := by exact prefixLift 3118072
  have htrace : WordTrace (prefixWord ++ tailWord_3118072) baseStart_3118072 baseEnd_3118072 := by
    simpa [prefixWord, tailWord_3118072, baseEnd_3118072] using wordTrace_append hprefix tailTrace_3118072
  have hstable : (prefixWord ++ tailWord_3118072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118072).length < 2 ^ (prefixWord ++ tailWord_3118072).sum := by decide
  have hdescent : baseEnd_3118072 < baseStart_3118072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118108 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3118108 : Nat := 118140960795 + 3118108 * 2 ^ 59
def prefixEnd_3118108 : Nat := 4983230072969 + 3 ^ 40 * 3118108 * 2
def baseEnd_3118108 : Nat := 1067392091086394414540059

theorem tailTrace_3118108 : CollatzResearch.WordTrace tailWord_3118108 prefixEnd_3118108 1067392091086394414540059 := by
  unfold tailWord_3118108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56863370893817360647297489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75817827858423147529729985 56863370893817360647297489)
  ·
    refine ⟨42647528170363020485473117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56863370893817360647297489 42647528170363020485473117)
    ·
      refine ⟨15992823063886132682052419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42647528170363020485473117 15992823063886132682052419)
      ·
        refine ⟨23989234595829199023078629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15992823063886132682052419 23989234595829199023078629)
        ·
          refine ⟨4497981486717974816827243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23989234595829199023078629 4497981486717974816827243)
          ·
            refine ⟨6746972230076962225240865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497981486717974816827243 6746972230076962225240865)
            ·
              refine ⟨5060229172557721668930649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746972230076962225240865 5060229172557721668930649)
              ·
                refine ⟨3795171879418291251697987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060229172557721668930649 3795171879418291251697987)
                ·
                  refine ⟨5692757819127436877546981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795171879418291251697987 5692757819127436877546981)
                  ·
                    refine ⟨1067392091086394414540059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692757819127436877546981 1067392091086394414540059)
                    ·
                      rfl

theorem cell22_3118108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3118108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118108 prefixEnd_3118108 := by exact prefixLift 3118108
  have htrace : WordTrace (prefixWord ++ tailWord_3118108) baseStart_3118108 baseEnd_3118108 := by
    simpa [prefixWord, tailWord_3118108, baseEnd_3118108] using wordTrace_append hprefix tailTrace_3118108
  have hstable : (prefixWord ++ tailWord_3118108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118108).length < 2 ^ (prefixWord ++ tailWord_3118108).sum := by decide
  have hdescent : baseEnd_3118108 < baseStart_3118108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118136 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_3118136 : Nat := 118140960795 + 3118136 * 2 ^ 59
def prefixEnd_3118136 : Nat := 4983230072969 + 3 ^ 40 * 3118136 * 2
def baseEnd_3118136 : Nat := 1067401676058611674839973

theorem tailTrace_3118136 : CollatzResearch.WordTrace tailWord_3118136 prefixEnd_3118136 1067401676058611674839973 := by
  unfold tailWord_3118136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56863881515766641038307131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75818508687688854717742841 56863881515766641038307131)
  ·
    refine ⟨85295822273649961557460697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56863881515766641038307131 85295822273649961557460697)
    ·
      refine ⟨63971866705237471168095523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85295822273649961557460697 63971866705237471168095523)
      ·
        refine ⟨95957800057856206752143285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63971866705237471168095523 95957800057856206752143285)
        ·
          refine ⟨8996043755424019383013433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95957800057856206752143285 8996043755424019383013433)
          ·
            refine ⟨6747032816568014537260075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8996043755424019383013433 6747032816568014537260075)
            ·
              refine ⟨10120549224852021805890113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747032816568014537260075 10120549224852021805890113)
              ·
                refine ⟨7590411918639016354417585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10120549224852021805890113 7590411918639016354417585)
                ·
                  refine ⟨5692808938979262265813189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590411918639016354417585 5692808938979262265813189)
                  ·
                    refine ⟨1067401676058611674839973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692808938979262265813189 1067401676058611674839973)
                    ·
                      rfl

theorem cell22_3118136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_3118136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118136 prefixEnd_3118136 := by exact prefixLift 3118136
  have htrace : WordTrace (prefixWord ++ tailWord_3118136) baseStart_3118136 baseEnd_3118136 := by
    simpa [prefixWord, tailWord_3118136, baseEnd_3118136] using wordTrace_append hprefix tailTrace_3118136
  have hstable : (prefixWord ++ tailWord_3118136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118136).length < 2 ^ (prefixWord ++ tailWord_3118136).sum := by decide
  have hdescent : baseEnd_3118136 < baseStart_3118136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118200 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 1, 3]
def baseStart_3118200 : Nat := 118140960795 + 3118200 * 2 ^ 59
def prefixEnd_3118200 : Nat := 4983230072969 + 3 ^ 40 * 3118200 * 2
def baseEnd_3118200 : Nat := 1067423584566536841239777

theorem tailTrace_3118200 : CollatzResearch.WordTrace tailWord_3118200 prefixEnd_3118200 1067423584566536841239777 := by
  unfold tailWord_3118200
  simp only [CollatzResearch.WordTrace]
  refine ⟨56865048651650710503472027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75820064868867614004629369 56865048651650710503472027)
  ·
    refine ⟨85297572977476065755208041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56865048651650710503472027 85297572977476065755208041)
    ·
      refine ⟨63973179733107049316406031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85297572977476065755208041 63973179733107049316406031)
      ·
        refine ⟨95959769599660573974609047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63973179733107049316406031 95959769599660573974609047)
        ·
          refine ⟨143939654399490860961913571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95959769599660573974609047 143939654399490860961913571)
          ·
            refine ⟨215909481599236291442870357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143939654399490860961913571 215909481599236291442870357)
            ·
              refine ⟨2530189237491050290346137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 215909481599236291442870357 2530189237491050290346137)
              ·
                refine ⟨1897641928118287717759603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530189237491050290346137 1897641928118287717759603)
                ·
                  refine ⟨2846462892177431576639405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897641928118287717759603 2846462892177431576639405)
                  ·
                    refine ⟨1067423584566536841239777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846462892177431576639405 1067423584566536841239777)
                    ·
                      rfl

theorem cell22_3118200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_3118200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118200 prefixEnd_3118200 := by exact prefixLift 3118200
  have htrace : WordTrace (prefixWord ++ tailWord_3118200) baseStart_3118200 baseEnd_3118200 := by
    simpa [prefixWord, tailWord_3118200, baseEnd_3118200] using wordTrace_append hprefix tailTrace_3118200
  have hstable : (prefixWord ++ tailWord_3118200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118200).length < 2 ^ (prefixWord ++ tailWord_3118200).sum := by decide
  have hdescent : baseEnd_3118200 < baseStart_3118200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118256 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_3118256 : Nat := 118140960795 + 3118256 * 2 ^ 59
def prefixEnd_3118256 : Nat := 4983230072969 + 3 ^ 40 * 3118256 * 2
def baseEnd_3118256 : Nat := 1067442754510971361839605

theorem tailTrace_3118256 : CollatzResearch.WordTrace tailWord_3118256 prefixEnd_3118256 1067442754510971361839605 := by
  unfold tailWord_3118256
  simp only [CollatzResearch.WordTrace]
  refine ⟨56866069895549271285491311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75821426527399028380655081 56866069895549271285491311)
  ·
    refine ⟨85299104843323906928236967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56866069895549271285491311 85299104843323906928236967)
    ·
      refine ⟨127948657264985860392355451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85299104843323906928236967 127948657264985860392355451)
      ·
        refine ⟨191922985897478790588533177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127948657264985860392355451 191922985897478790588533177)
        ·
          refine ⟨143942239423109092941399883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191922985897478790588533177 143942239423109092941399883)
          ·
            refine ⟨215913359134663639412099825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143942239423109092941399883 215913359134663639412099825)
            ·
              refine ⟨161935019350997729559074869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215913359134663639412099825 161935019350997729559074869)
              ·
                refine ⟨15181408064156037146163269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161935019350997729559074869 15181408064156037146163269)
                ·
                  refine ⟨2846514012029256964905613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15181408064156037146163269 2846514012029256964905613)
                  ·
                    refine ⟨1067442754510971361839605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846514012029256964905613 1067442754510971361839605)
                    ·
                      rfl

theorem cell22_3118256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_3118256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118256 prefixEnd_3118256 := by exact prefixLift 3118256
  have htrace : WordTrace (prefixWord ++ tailWord_3118256) baseStart_3118256 baseEnd_3118256 := by
    simpa [prefixWord, tailWord_3118256, baseEnd_3118256] using wordTrace_append hprefix tailTrace_3118256
  have hstable : (prefixWord ++ tailWord_3118256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118256).length < 2 ^ (prefixWord ++ tailWord_3118256).sum := by decide
  have hdescent : baseEnd_3118256 < baseStart_3118256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118258 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3118258 : Nat := 118140960795 + 3118258 * 2 ^ 59
def prefixEnd_3118258 : Nat := 4983230072969 + 3 ^ 40 * 3118258 * 2
def baseEnd_3118258 : Nat := 355814479717281341096533

theorem tailTrace_3118258 : CollatzResearch.WordTrace tailWord_3118258 prefixEnd_3118258 355814479717281341096533 := by
  unfold tailWord_3118258
  simp only [CollatzResearch.WordTrace]
  refine ⟨28433053184272824228138857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75821475158060864608370285 28433053184272824228138857)
  ·
    refine ⟨21324789888204618171104143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28433053184272824228138857 21324789888204618171104143)
    ·
      refine ⟨31987184832306927256656215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21324789888204618171104143 31987184832306927256656215)
      ·
        refine ⟨47980777248460390884984323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31987184832306927256656215 47980777248460390884984323)
        ·
          refine ⟨71971165872690586327476485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47980777248460390884984323 71971165872690586327476485)
          ·
            refine ⟨13494593601129484936401841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71971165872690586327476485 13494593601129484936401841)
            ·
              refine ⟨10120945200847113702301381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13494593601129484936401841 10120945200847113702301381)
              ·
                refine ⟨1897677225158833819181509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10120945200847113702301381 1897677225158833819181509)
                ·
                  refine ⟨355814479717281341096533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1897677225158833819181509 355814479717281341096533)
                  ·
                    rfl

theorem cell22_3118258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3118258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118258 prefixEnd_3118258 := by exact prefixLift 3118258
  have htrace : WordTrace (prefixWord ++ tailWord_3118258) baseStart_3118258 baseEnd_3118258 := by
    simpa [prefixWord, tailWord_3118258, baseEnd_3118258] using wordTrace_append hprefix tailTrace_3118258
  have hstable : (prefixWord ++ tailWord_3118258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118258).length < 2 ^ (prefixWord ++ tailWord_3118258).sum := by decide
  have hdescent : baseEnd_3118258 < baseStart_3118258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118346 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3118346 : Nat := 118140960795 + 3118346 * 2 ^ 59
def prefixEnd_3118346 : Nat := 4983230072969 + 3 ^ 40 * 3118346 * 2
def baseEnd_3118346 : Nat := 1067473563350241127089329

theorem tailTrace_3118346 : CollatzResearch.WordTrace tailWord_3118346 prefixEnd_3118346 1067473563350241127089329 := by
  unfold tailWord_3118346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28433855590193121985439723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75823614907181658627839261 28433855590193121985439723)
  ·
    refine ⟨42650783385289682978159585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28433855590193121985439723 42650783385289682978159585)
    ·
      refine ⟨31988087538967262233619689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42650783385289682978159585 31988087538967262233619689)
      ·
        refine ⟨23991065654225446675214767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31988087538967262233619689 23991065654225446675214767)
        ·
          refine ⟨35986598481338170012822151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23991065654225446675214767 35986598481338170012822151)
          ·
            refine ⟨53979897722007255019233227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35986598481338170012822151 53979897722007255019233227)
            ·
              refine ⟨80969846583010882528849841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53979897722007255019233227 80969846583010882528849841)
              ·
                refine ⟨60727384937258161896637381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80969846583010882528849841 60727384937258161896637381)
                ·
                  refine ⟨11386384675735905355619509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60727384937258161896637381 11386384675735905355619509)
                  ·
                    refine ⟨1067473563350241127089329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11386384675735905355619509 1067473563350241127089329)
                    ·
                      rfl

theorem cell22_3118346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3118346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118346 prefixEnd_3118346 := by exact prefixLift 3118346
  have htrace : WordTrace (prefixWord ++ tailWord_3118346) baseStart_3118346 baseEnd_3118346 := by
    simpa [prefixWord, tailWord_3118346, baseEnd_3118346] using wordTrace_append hprefix tailTrace_3118346
  have hstable : (prefixWord ++ tailWord_3118346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118346).length < 2 ^ (prefixWord ++ tailWord_3118346).sum := by decide
  have hdescent : baseEnd_3118346 < baseStart_3118346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118365 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3118365 : Nat := 118140960795 + 3118365 * 2 ^ 59
def prefixEnd_3118365 : Nat := 4983230072969 + 3 ^ 40 * 3118365 * 2
def baseEnd_3118365 : Nat := 355826689146177136954757

theorem tailTrace_3118365 : CollatzResearch.WordTrace tailWord_3118365 prefixEnd_3118365 355826689146177136954757 := by
  unfold tailWord_3118365
  simp only [CollatzResearch.WordTrace]
  refine ⟨113736115347703654186700549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75824076898469102791133699 113736115347703654186700549)
  ·
    refine ⟨21325521627694435160006353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113736115347703654186700549 21325521627694435160006353)
    ·
      refine ⟨15994141220770826370004765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21325521627694435160006353 15994141220770826370004765)
      ·
        refine ⟨5997802957789059888751787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15994141220770826370004765 5997802957789059888751787)
        ·
          refine ⟨8996704436683589833127681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5997802957789059888751787 8996704436683589833127681)
          ·
            refine ⟨6747528327512692374845761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8996704436683589833127681 6747528327512692374845761)
            ·
              refine ⟨5060646245634519281134321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6747528327512692374845761 5060646245634519281134321)
              ·
                refine ⟨3795484684225889460850741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060646245634519281134321 3795484684225889460850741)
                ·
                  refine ⟨355826689146177136954757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3795484684225889460850741 355826689146177136954757)
                  ·
                    rfl

theorem cell22_3118365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3118365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118365 prefixEnd_3118365 := by exact prefixLift 3118365
  have htrace : WordTrace (prefixWord ++ tailWord_3118365) baseStart_3118365 baseEnd_3118365 := by
    simpa [prefixWord, tailWord_3118365, baseEnd_3118365] using wordTrace_append hprefix tailTrace_3118365
  have hstable : (prefixWord ++ tailWord_3118365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118365).length < 2 ^ (prefixWord ++ tailWord_3118365).sum := by decide
  have hdescent : baseEnd_3118365 < baseStart_3118365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118408 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_3118408 : Nat := 118140960795 + 3118408 * 2 ^ 59
def prefixEnd_3118408 : Nat := 4983230072969 + 3 ^ 40 * 3118408 * 2
def baseEnd_3118408 : Nat := 1067494787217293632039139

theorem tailTrace_3118408 : CollatzResearch.WordTrace tailWord_3118408 prefixEnd_3118408 1067494787217293632039139 := by
  unfold tailWord_3118408
  simp only [CollatzResearch.WordTrace]
  refine ⟨56868841843273936265257939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75825122457698581687010585 56868841843273936265257939)
  ·
    refine ⟨85303262764910904397886909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56868841843273936265257939 85303262764910904397886909)
    ·
      refine ⟨31988723536841589149207591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85303262764910904397886909 31988723536841589149207591)
      ·
        refine ⟨47983085305262383723811387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31988723536841589149207591 47983085305262383723811387)
        ·
          refine ⟨71974627957893575585717081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47983085305262383723811387 71974627957893575585717081)
          ·
            refine ⟨53980970968420181689287811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71974627957893575585717081 53980970968420181689287811)
            ·
              refine ⟨80971456452630272533931717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53980970968420181689287811 80971456452630272533931717)
              ·
                refine ⟨15182148084868176100112197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80971456452630272533931717 15182148084868176100112197)
                ·
                  refine ⟨2846652765912783018771037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15182148084868176100112197 2846652765912783018771037)
                  ·
                    refine ⟨1067494787217293632039139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846652765912783018771037 1067494787217293632039139)
                    ·
                      rfl

theorem cell22_3118408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_3118408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118408 prefixEnd_3118408 := by exact prefixLift 3118408
  have htrace : WordTrace (prefixWord ++ tailWord_3118408) baseStart_3118408 baseEnd_3118408 := by
    simpa [prefixWord, tailWord_3118408, baseEnd_3118408] using wordTrace_append hprefix tailTrace_3118408
  have hstable : (prefixWord ++ tailWord_3118408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118408).length < 2 ^ (prefixWord ++ tailWord_3118408).sum := by decide
  have hdescent : baseEnd_3118408 < baseStart_3118408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118412 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_3118412 : Nat := 118140960795 + 3118412 * 2 ^ 59
def prefixEnd_3118412 : Nat := 4983230072969 + 3 ^ 40 * 3118412 * 2
def baseEnd_3118412 : Nat := 1067496156499038954939127

theorem tailTrace_3118412 : CollatzResearch.WordTrace tailWord_3118412 prefixEnd_3118412 1067496156499038954939127 := by
  unfold tailWord_3118412
  simp only [CollatzResearch.WordTrace]
  refine ⟨56868914789266690606830745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75825219719022254142440993 56868914789266690606830745)
  ·
    refine ⟨42651686091950017955123059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56868914789266690606830745 42651686091950017955123059)
    ·
      refine ⟨63977529137925026932684589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42651686091950017955123059 63977529137925026932684589)
      ·
        refine ⟨23991573426721885099756721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63977529137925026932684589 23991573426721885099756721)
        ·
          refine ⟨17993680070041413824817541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23991573426721885099756721 17993680070041413824817541)
          ·
            refine ⟨3373815013132765092153289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17993680070041413824817541 3373815013132765092153289)
            ·
              refine ⟨2530361259849573819114967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373815013132765092153289 2530361259849573819114967)
              ·
                refine ⟨3795541889774360728672451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530361259849573819114967 3795541889774360728672451)
                ·
                  refine ⟨5693312834661541093008677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795541889774360728672451 5693312834661541093008677)
                  ·
                    refine ⟨1067496156499038954939127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693312834661541093008677 1067496156499038954939127)
                    ·
                      rfl

theorem cell22_3118412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_3118412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118412 prefixEnd_3118412 := by exact prefixLift 3118412
  have htrace : WordTrace (prefixWord ++ tailWord_3118412) baseStart_3118412 baseEnd_3118412 := by
    simpa [prefixWord, tailWord_3118412, baseEnd_3118412] using wordTrace_append hprefix tailTrace_3118412
  have hstable : (prefixWord ++ tailWord_3118412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118412).length < 2 ^ (prefixWord ++ tailWord_3118412).sum := by decide
  have hdescent : baseEnd_3118412 < baseStart_3118412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118425 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_3118425 : Nat := 118140960795 + 3118425 * 2 ^ 59
def prefixEnd_3118425 : Nat := 4983230072969 + 3 ^ 40 * 3118425 * 2
def baseEnd_3118425 : Nat := 1067500606664711254364087

theorem tailTrace_3118425 : CollatzResearch.WordTrace tailWord_3118425 prefixEnd_3118425 1067500606664711254364087 := by
  unfold tailWord_3118425
  simp only [CollatzResearch.WordTrace]
  refine ⟨113738303727486284433884729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75825535818324189622589819 113738303727486284433884729)
  ·
    refine ⟨85303727795614713325413547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113738303727486284433884729 85303727795614713325413547)
    ·
      refine ⟨127955591693422069988120321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85303727795614713325413547 127955591693422069988120321)
      ·
        refine ⟨95966693770066552491090241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127955591693422069988120321 95966693770066552491090241)
        ·
          refine ⟨71975020327549914368317681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95966693770066552491090241 71975020327549914368317681)
          ·
            refine ⟨53981265245662435776238261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71975020327549914368317681 53981265245662435776238261)
            ·
              refine ⟨5060743616780853354022337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53981265245662435776238261 5060743616780853354022337)
              ·
                refine ⟨3795557712585640015516753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060743616780853354022337 3795557712585640015516753)
                ·
                  refine ⟨2846668284439230011637565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3795557712585640015516753 2846668284439230011637565)
                  ·
                    refine ⟨1067500606664711254364087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846668284439230011637565 1067500606664711254364087)
                    ·
                      rfl

theorem cell22_3118425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_3118425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118425 prefixEnd_3118425 := by exact prefixLift 3118425
  have htrace : WordTrace (prefixWord ++ tailWord_3118425) baseStart_3118425 baseEnd_3118425 := by
    simpa [prefixWord, tailWord_3118425, baseEnd_3118425] using wordTrace_append hprefix tailTrace_3118425
  have hstable : (prefixWord ++ tailWord_3118425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118425).length < 2 ^ (prefixWord ++ tailWord_3118425).sum := by decide
  have hdescent : baseEnd_3118425 < baseStart_3118425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118442 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3118442 : Nat := 118140960795 + 3118442 * 2 ^ 59
def prefixEnd_3118442 : Nat := 4983230072969 + 3 ^ 40 * 3118442 * 2
def baseEnd_3118442 : Nat := 1067506426112128876689035

theorem tailTrace_3118442 : CollatzResearch.WordTrace tailWord_3118442 prefixEnd_3118442 1067506426112128876689035 := by
  unfold tailWord_3118442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434730942106174084313395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75825949178949797558169053 28434730942106174084313395)
  ·
    refine ⟨42652096413159261126470093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28434730942106174084313395 42652096413159261126470093)
    ·
      refine ⟨15994536154934722922426285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42652096413159261126470093 15994536154934722922426285)
      ·
        refine ⟨5997951058100521095909857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15994536154934722922426285 5997951058100521095909857)
        ·
          refine ⟨4498463293575390821932393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5997951058100521095909857 4498463293575390821932393)
          ·
            refine ⟨3373847470181543116449295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4498463293575390821932393 3373847470181543116449295)
            ·
              refine ⟨5060771205272314674673943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3373847470181543116449295 5060771205272314674673943)
              ·
                refine ⟨7591156807908472012010915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060771205272314674673943 7591156807908472012010915)
                ·
                  refine ⟨11386735211862708018016373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591156807908472012010915 11386735211862708018016373)
                  ·
                    refine ⟨1067506426112128876689035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11386735211862708018016373 1067506426112128876689035)
                    ·
                      rfl

theorem cell22_3118442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3118442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118442 prefixEnd_3118442 := by exact prefixLift 3118442
  have htrace : WordTrace (prefixWord ++ tailWord_3118442) baseStart_3118442 baseEnd_3118442 := by
    simpa [prefixWord, tailWord_3118442, baseEnd_3118442] using wordTrace_append hprefix tailTrace_3118442
  have hstable : (prefixWord ++ tailWord_3118442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118442).length < 2 ^ (prefixWord ++ tailWord_3118442).sum := by decide
  have hdescent : baseEnd_3118442 < baseStart_3118442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118575 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 2, 4]
def baseStart_3118575 : Nat := 118140960795 + 3118575 * 2 ^ 59
def prefixEnd_3118575 : Nat := 4983230072969 + 3 ^ 40 * 3118575 * 2
def baseEnd_3118575 : Nat := 1067551954730160863113627

theorem tailTrace_3118575 : CollatzResearch.WordTrace tailWord_3118575 prefixEnd_3118575 1067551954730160863113627 := by
  unfold tailWord_3118575
  simp only [CollatzResearch.WordTrace]
  refine ⟨113743774676942860051845179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75829183117961906701230119 113743774676942860051845179)
  ·
    refine ⟨170615662015414290077767769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113743774676942860051845179 170615662015414290077767769)
    ·
      refine ⟨127961746511560717558325827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170615662015414290077767769 127961746511560717558325827)
      ·
        refine ⟨191942619767341076337488741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127961746511560717558325827 191942619767341076337488741)
        ·
          refine ⟨35989241206376451813279139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191942619767341076337488741 35989241206376451813279139)
          ·
            refine ⟨53983861809564677719918709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35989241206376451813279139 53983861809564677719918709)
            ·
              refine ⟨5060987044646688536242379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53983861809564677719918709 5060987044646688536242379)
              ·
                refine ⟨7591480566970032804363569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060987044646688536242379 7591480566970032804363569)
                ·
                  refine ⟨5693610425227524603272677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7591480566970032804363569 5693610425227524603272677)
                  ·
                    refine ⟨1067551954730160863113627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693610425227524603272677 1067551954730160863113627)
                    ·
                      rfl

theorem cell22_3118575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_3118575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118575 prefixEnd_3118575 := by exact prefixLift 3118575
  have htrace : WordTrace (prefixWord ++ tailWord_3118575) baseStart_3118575 baseEnd_3118575 := by
    simpa [prefixWord, tailWord_3118575, baseEnd_3118575] using wordTrace_append hprefix tailTrace_3118575
  have hstable : (prefixWord ++ tailWord_3118575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118575).length < 2 ^ (prefixWord ++ tailWord_3118575).sum := by decide
  have hdescent : baseEnd_3118575 < baseStart_3118575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118581 : List Nat := [1, 3, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3118581 : Nat := 118140960795 + 3118581 * 2 ^ 59
def prefixEnd_3118581 : Nat := 4983230072969 + 3 ^ 40 * 3118581 * 2
def baseEnd_3118581 : Nat := 1067554008652778847463609

theorem tailTrace_3118581 : CollatzResearch.WordTrace tailWord_3118581 prefixEnd_3118581 1067554008652778847463609 := by
  unfold tailWord_3118581
  simp only [CollatzResearch.WordTrace]
  refine ⟨113743993514921123076563597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75829329009947415384375731 113743993514921123076563597)
  ·
    refine ⟨42653997568095421153711349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113743993514921123076563597 42653997568095421153711349)
    ·
      refine ⟨3998812272008945733160439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42653997568095421153711349 3998812272008945733160439)
      ·
        refine ⟨5998218408013418599740659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998812272008945733160439 5998218408013418599740659)
        ·
          refine ⟨8997327612020127899610989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5998218408013418599740659 8997327612020127899610989)
          ·
            refine ⟨3373997854507547962354121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8997327612020127899610989 3373997854507547962354121)
            ·
              refine ⟨2530498390880660971765591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3373997854507547962354121 2530498390880660971765591)
              ·
                refine ⟨3795747586320991457648387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530498390880660971765591 3795747586320991457648387)
                ·
                  refine ⟨5693621379481487186472581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795747586320991457648387 5693621379481487186472581)
                  ·
                    refine ⟨1067554008652778847463609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693621379481487186472581 1067554008652778847463609)
                    ·
                      rfl

theorem cell22_3118581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3118581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118581 prefixEnd_3118581 := by exact prefixLift 3118581
  have htrace : WordTrace (prefixWord ++ tailWord_3118581) baseStart_3118581 baseEnd_3118581 := by
    simpa [prefixWord, tailWord_3118581, baseEnd_3118581] using wordTrace_append hprefix tailTrace_3118581
  have hstable : (prefixWord ++ tailWord_3118581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118581).length < 2 ^ (prefixWord ++ tailWord_3118581).sum := by decide
  have hdescent : baseEnd_3118581 < baseStart_3118581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118594 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3118594 : Nat := 118140960795 + 3118594 * 2 ^ 59
def prefixEnd_3118594 : Nat := 4983230072969 + 3 ^ 40 * 3118594 * 2
def baseEnd_3118594 : Nat := 1067558458818451146888569

theorem tailTrace_3118594 : CollatzResearch.WordTrace tailWord_3118594 prefixEnd_3118594 1067558458818451146888569 := by
  unfold tailWord_3118594
  simp only [CollatzResearch.WordTrace]
  refine ⟨28436116915968506574196709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75829645109249350864524557 28436116915968506574196709)
  ·
    refine ⟨5331771921744094982661883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28436116915968506574196709 5331771921744094982661883)
    ·
      refine ⟨7997657882616142473992825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331771921744094982661883 7997657882616142473992825)
      ·
        refine ⟨5998243411962106855494619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7997657882616142473992825 5998243411962106855494619)
        ·
          refine ⟨8997365117943160283241929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5998243411962106855494619 8997365117943160283241929)
          ·
            refine ⟨6748023838457370212431447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8997365117943160283241929 6748023838457370212431447)
            ·
              refine ⟨10122035757686055318647171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748023838457370212431447 10122035757686055318647171)
              ·
                refine ⟨15183053636529082977970757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10122035757686055318647171 15183053636529082977970757)
                ·
                  refine ⟨2846822556849203058369517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15183053636529082977970757 2846822556849203058369517)
                  ·
                    refine ⟨1067558458818451146888569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2846822556849203058369517 1067558458818451146888569)
                    ·
                      rfl

theorem cell22_3118594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3118594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118594 prefixEnd_3118594 := by exact prefixLift 3118594
  have htrace : WordTrace (prefixWord ++ tailWord_3118594) baseStart_3118594 baseEnd_3118594 := by
    simpa [prefixWord, tailWord_3118594, baseEnd_3118594] using wordTrace_append hprefix tailTrace_3118594
  have hstable : (prefixWord ++ tailWord_3118594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118594).length < 2 ^ (prefixWord ++ tailWord_3118594).sum := by decide
  have hdescent : baseEnd_3118594 < baseStart_3118594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118669 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3118669 : Nat := 118140960795 + 3118669 * 2 ^ 59
def prefixEnd_3118669 : Nat := 4983230072969 + 3 ^ 40 * 3118669 * 2
def baseEnd_3118669 : Nat := 355861377617058650421113

theorem tailTrace_3118669 : CollatzResearch.WordTrace tailWord_3118669 prefixEnd_3118669 355861377617058650421113 := by
  unfold tailWord_3118669
  simp only [CollatzResearch.WordTrace]
  refine ⟨113747203138602314105767061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75831468759068209403844707 113747203138602314105767061)
  ·
    refine ⟨5331900147121983473707831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113747203138602314105767061 5331900147121983473707831)
    ·
      refine ⟨7997850220682975210561747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331900147121983473707831 7997850220682975210561747)
      ·
        refine ⟨11996775331024462815842621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7997850220682975210561747 11996775331024462815842621)
        ·
          refine ⟨4498790749134173555940983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11996775331024462815842621 4498790749134173555940983)
          ·
            refine ⟨6748186123701260333911475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498790749134173555940983 6748186123701260333911475)
            ·
              refine ⟨10122279185551890500867213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748186123701260333911475 10122279185551890500867213)
              ·
                refine ⟨3795854694581958937825205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10122279185551890500867213 3795854694581958937825205)
                ·
                  refine ⟨355861377617058650421113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3795854694581958937825205 355861377617058650421113)
                  ·
                    rfl

theorem cell22_3118669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3118669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118669 prefixEnd_3118669 := by exact prefixLift 3118669
  have htrace : WordTrace (prefixWord ++ tailWord_3118669) baseStart_3118669 baseEnd_3118669 := by
    simpa [prefixWord, tailWord_3118669, baseEnd_3118669] using wordTrace_append hprefix tailTrace_3118669
  have hstable : (prefixWord ++ tailWord_3118669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118669).length < 2 ^ (prefixWord ++ tailWord_3118669).sum := by decide
  have hdescent : baseEnd_3118669 < baseStart_3118669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118695 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3118695 : Nat := 118140960795 + 3118695 * 2 ^ 59
def prefixEnd_3118695 : Nat := 4983230072969 + 3 ^ 40 * 3118695 * 2
def baseEnd_3118695 : Nat := 1067593033182520550113259

theorem tailTrace_3118695 : CollatzResearch.WordTrace tailWord_3118695 prefixEnd_3118695 1067593033182520550113259 := by
  unfold tailWord_3118695
  simp only [CollatzResearch.WordTrace]
  refine ⟨113748151436508120546213539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75832100957672080364142359 113748151436508120546213539)
  ·
    refine ⟨170622227154762180819320309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113748151436508120546213539 170622227154762180819320309)
    ·
      refine ⟨15995833795758954451811279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170622227154762180819320309 15995833795758954451811279)
      ·
        refine ⟨23993750693638431677716919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15995833795758954451811279 23993750693638431677716919)
        ·
          refine ⟨35990626040457647516575379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23993750693638431677716919 35990626040457647516575379)
          ·
            refine ⟨53985939060686471274863069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35990626040457647516575379 53985939060686471274863069)
            ·
              refine ⟨20244727147757426728073651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53985939060686471274863069 20244727147757426728073651)
              ·
                refine ⟨30367090721636140092110477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20244727147757426728073651 30367090721636140092110477)
                ·
                  refine ⟨11387659020613552534541429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30367090721636140092110477 11387659020613552534541429)
                  ·
                    refine ⟨1067593033182520550113259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11387659020613552534541429 1067593033182520550113259)
                    ·
                      rfl

theorem cell22_3118695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3118695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118695 prefixEnd_3118695 := by exact prefixLift 3118695
  have htrace : WordTrace (prefixWord ++ tailWord_3118695) baseStart_3118695 baseEnd_3118695 := by
    simpa [prefixWord, tailWord_3118695, baseEnd_3118695] using wordTrace_append hprefix tailTrace_3118695
  have hstable : (prefixWord ++ tailWord_3118695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118695).length < 2 ^ (prefixWord ++ tailWord_3118695).sum := by decide
  have hdescent : baseEnd_3118695 < baseStart_3118695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118744 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_3118744 : Nat := 118140960795 + 3118744 * 2 ^ 59
def prefixEnd_3118744 : Nat := 4983230072969 + 3 ^ 40 * 3118744 * 2
def baseEnd_3118744 : Nat := 1067609806883900755638109

theorem tailTrace_3118744 : CollatzResearch.WordTrace tailWord_3118744 prefixEnd_3118744 1067609806883900755638109 := by
  unfold tailWord_3118744
  simp only [CollatzResearch.WordTrace]
  refine ⟨56874969306665300957373643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75833292408887067943164857 56874969306665300957373643)
  ·
    refine ⟨85312453959997951436060465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56874969306665300957373643 85312453959997951436060465)
    ·
      refine ⟨63984340469998463577045349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85312453959997951436060465 63984340469998463577045349)
      ·
        refine ⟨11997063838124711920696003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63984340469998463577045349 11997063838124711920696003)
        ·
          refine ⟨17995595757187067881044005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11997063838124711920696003 17995595757187067881044005)
          ·
            refine ⟨3374174204472575227695751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17995595757187067881044005 3374174204472575227695751)
            ·
              refine ⟨5061261306708862841543627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374174204472575227695751 5061261306708862841543627)
              ·
                refine ⟨7591891960063294262315441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061261306708862841543627 7591891960063294262315441)
                ·
                  refine ⟨5693918970047470696736581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7591891960063294262315441 5693918970047470696736581)
                  ·
                    refine ⟨1067609806883900755638109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693918970047470696736581 1067609806883900755638109)
                    ·
                      rfl

theorem cell22_3118744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_3118744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118744 prefixEnd_3118744 := by exact prefixLift 3118744
  have htrace : WordTrace (prefixWord ++ tailWord_3118744) baseStart_3118744 baseEnd_3118744 := by
    simpa [prefixWord, tailWord_3118744, baseEnd_3118744] using wordTrace_append hprefix tailTrace_3118744
  have hstable : (prefixWord ++ tailWord_3118744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118744).length < 2 ^ (prefixWord ++ tailWord_3118744).sum := by decide
  have hdescent : baseEnd_3118744 < baseStart_3118744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118862 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3118862 : Nat := 118140960795 + 3118862 * 2 ^ 59
def prefixEnd_3118862 : Nat := 4983230072969 + 3 ^ 40 * 3118862 * 2
def baseEnd_3118862 : Nat := 1067650200695387781187747

theorem tailTrace_3118862 : CollatzResearch.WordTrace tailWord_3118862 prefixEnd_3118862 1067650200695387781187747 := by
  unfold tailWord_3118862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219280303362888508442855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75836161617935405378361893 14219280303362888508442855)
  ·
    refine ⟨21328920455044332762664283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14219280303362888508442855 21328920455044332762664283)
    ·
      refine ⟨31993380682566499143996425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21328920455044332762664283 31993380682566499143996425)
      ·
        refine ⟨23995035511924874357997319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31993380682566499143996425 23995035511924874357997319)
        ·
          refine ⟨35992553267887311536995979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23995035511924874357997319 35992553267887311536995979)
          ·
            refine ⟨53988829901830967305493969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35992553267887311536995979 53988829901830967305493969)
            ·
              refine ⟨40491622426373225479120477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53988829901830967305493969 40491622426373225479120477)
              ·
                refine ⟨15184358409889959554670179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40491622426373225479120477 15184358409889959554670179)
                ·
                  refine ⟨22776537614834939332005269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15184358409889959554670179 22776537614834939332005269)
                  ·
                    refine ⟨1067650200695387781187747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22776537614834939332005269 1067650200695387781187747)
                    ·
                      rfl

theorem cell22_3118862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3118862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118862 prefixEnd_3118862 := by exact prefixLift 3118862
  have htrace : WordTrace (prefixWord ++ tailWord_3118862) baseStart_3118862 baseEnd_3118862 := by
    simpa [prefixWord, tailWord_3118862, baseEnd_3118862] using wordTrace_append hprefix tailTrace_3118862
  have hstable : (prefixWord ++ tailWord_3118862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118862).length < 2 ^ (prefixWord ++ tailWord_3118862).sum := by decide
  have hdescent : baseEnd_3118862 < baseStart_3118862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118881 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3118881 : Nat := 118140960795 + 3118881 * 2 ^ 59
def prefixEnd_3118881 : Nat := 4983230072969 + 3 ^ 40 * 3118881 * 2
def baseEnd_3118881 : Nat := 1067656704783678064962689

theorem tailTrace_3118881 : CollatzResearch.WordTrace tailWord_3118881 prefixEnd_3118881 1067656704783678064962689 := by
  unfold tailWord_3118881
  simp only [CollatzResearch.WordTrace]
  refine ⟨113754935413834274312484497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75836623609222849541656331 113754935413834274312484497)
  ·
    refine ⟨85316201560375705734363373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113754935413834274312484497 85316201560375705734363373)
    ·
      refine ⟨31993575585140889650386265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85316201560375705734363373 31993575585140889650386265)
      ·
        refine ⟨23995181688855667237789699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31993575585140889650386265 23995181688855667237789699)
        ·
          refine ⟨35992772533283500856684549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23995181688855667237789699 35992772533283500856684549)
          ·
            refine ⟨6748644849990656410628353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35992772533283500856684549 6748644849990656410628353)
            ·
              refine ⟨5061483637492992307971265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6748644849990656410628353 5061483637492992307971265)
              ·
                refine ⟨3796112728119744230978449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061483637492992307971265 3796112728119744230978449)
                ·
                  refine ⟨2847084546089808173233837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3796112728119744230978449 2847084546089808173233837)
                  ·
                    refine ⟨1067656704783678064962689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2847084546089808173233837 1067656704783678064962689)
                    ·
                      rfl

theorem cell22_3118881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3118881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118881 prefixEnd_3118881 := by exact prefixLift 3118881
  have htrace : WordTrace (prefixWord ++ tailWord_3118881) baseStart_3118881 baseEnd_3118881 := by
    simpa [prefixWord, tailWord_3118881, baseEnd_3118881] using wordTrace_append hprefix tailTrace_3118881
  have hstable : (prefixWord ++ tailWord_3118881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118881).length < 2 ^ (prefixWord ++ tailWord_3118881).sum := by decide
  have hdescent : baseEnd_3118881 < baseStart_3118881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118922 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_3118922 : Nat := 118140960795 + 3118922 * 2 ^ 59
def prefixEnd_3118922 : Nat := 4983230072969 + 3 ^ 40 * 3118922 * 2
def baseEnd_3118922 : Nat := 355890246640522541562521

theorem tailTrace_3118922 : CollatzResearch.WordTrace tailWord_3118922 prefixEnd_3118922 355890246640522541562521 := by
  unfold tailWord_3118922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28439107701671434578681755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75837620537790492209818013 28439107701671434578681755)
  ·
    refine ⟨42658661552507151868022633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28439107701671434578681755 42658661552507151868022633)
    ·
      refine ⟨31993996164380363901016975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42658661552507151868022633 31993996164380363901016975)
      ·
        refine ⟨47990994246570545851525463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31993996164380363901016975 47990994246570545851525463)
        ·
          refine ⟨71986491369855818777288195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47990994246570545851525463 71986491369855818777288195)
          ·
            refine ⟨107979737054783728165932293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71986491369855818777288195 107979737054783728165932293)
            ·
              refine ⟨20246200697771949031112305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107979737054783728165932293 20246200697771949031112305)
              ·
                refine ⟨15184650523328961773334229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20246200697771949031112305 15184650523328961773334229)
                ·
                  refine ⟨355890246640522541562521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15184650523328961773334229 355890246640522541562521)
                  ·
                    rfl

theorem cell22_3118922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_3118922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118922 prefixEnd_3118922 := by exact prefixLift 3118922
  have htrace : WordTrace (prefixWord ++ tailWord_3118922) baseStart_3118922 baseEnd_3118922 := by
    simpa [prefixWord, tailWord_3118922, baseEnd_3118922] using wordTrace_append hprefix tailTrace_3118922
  have hstable : (prefixWord ++ tailWord_3118922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118922).length < 2 ^ (prefixWord ++ tailWord_3118922).sum := by decide
  have hdescent : baseEnd_3118922 < baseStart_3118922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118937 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_3118937 : Nat := 118140960795 + 3118937 * 2 ^ 59
def prefixEnd_3118937 : Nat := 4983230072969 + 3 ^ 40 * 3118937 * 2
def baseEnd_3118937 : Nat := 1067675874728112585562517

theorem tailTrace_3118937 : CollatzResearch.WordTrace tailWord_3118937 prefixEnd_3118937 1067675874728112585562517 := by
  unfold tailWord_3118937
  simp only [CollatzResearch.WordTrace]
  refine ⟨113756977901631395876523065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75837985267754263917682043 113756977901631395876523065)
  ·
    refine ⟨85317733426223546907392299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113756977901631395876523065 85317733426223546907392299)
    ·
      refine ⟨127976600139335320361088449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85317733426223546907392299 127976600139335320361088449)
      ·
        refine ⟨95982450104501490270816337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127976600139335320361088449 95982450104501490270816337)
        ·
          refine ⟨71986837578376117703112253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95982450104501490270816337 71986837578376117703112253)
          ·
            refine ⟨26995064091891044138667095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71986837578376117703112253 26995064091891044138667095)
            ·
              refine ⟨40492596137836566208000643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26995064091891044138667095 40492596137836566208000643)
              ·
                refine ⟨60738894206754849312000965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40492596137836566208000643 60738894206754849312000965)
                ·
                  refine ⟨11388542663766534246000181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60738894206754849312000965 11388542663766534246000181)
                  ·
                    refine ⟨1067675874728112585562517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11388542663766534246000181 1067675874728112585562517)
                    ·
                      rfl

theorem cell22_3118937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_3118937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118937 prefixEnd_3118937 := by exact prefixLift 3118937
  have htrace : WordTrace (prefixWord ++ tailWord_3118937) baseStart_3118937 baseEnd_3118937 := by
    simpa [prefixWord, tailWord_3118937, baseEnd_3118937] using wordTrace_append hprefix tailTrace_3118937
  have hstable : (prefixWord ++ tailWord_3118937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118937).length < 2 ^ (prefixWord ++ tailWord_3118937).sum := by decide
  have hdescent : baseEnd_3118937 < baseStart_3118937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118956 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 5]
def baseStart_3118956 : Nat := 118140960795 + 3118956 * 2 ^ 59
def prefixEnd_3118956 : Nat := 4983230072969 + 3 ^ 40 * 3118956 * 2
def baseEnd_3118956 : Nat := 355894126272134289779153

theorem tailTrace_3118956 : CollatzResearch.WordTrace tailWord_3118956 prefixEnd_3118956 355894126272134289779153 := by
  unfold tailWord_3118956
  simp only [CollatzResearch.WordTrace]
  refine ⟨56878835444281281060732361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75838447259041708080976481 56878835444281281060732361)
  ·
    refine ⟨42659126583210960795549271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56878835444281281060732361 42659126583210960795549271)
    ·
      refine ⟨63988689874816441193323907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42659126583210960795549271 63988689874816441193323907)
      ·
        refine ⟨95983034812224661789985861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63988689874816441193323907 95983034812224661789985861)
        ·
          refine ⟨17996819027292124085622349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95983034812224661789985861 17996819027292124085622349)
          ·
            refine ⟨6748807135234546532108381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17996819027292124085622349 6748807135234546532108381)
            ·
              refine ⟨2530802675712954949540643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6748807135234546532108381 2530802675712954949540643)
              ·
                refine ⟨3796204013569432424310965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530802675712954949540643 3796204013569432424310965)
                ·
                  refine ⟨355894126272134289779153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3796204013569432424310965 355894126272134289779153)
                  ·
                    rfl

theorem cell22_3118956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_3118956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118956 prefixEnd_3118956 := by exact prefixLift 3118956
  have htrace : WordTrace (prefixWord ++ tailWord_3118956) baseStart_3118956 baseEnd_3118956 := by
    simpa [prefixWord, tailWord_3118956, baseEnd_3118956] using wordTrace_append hprefix tailTrace_3118956
  have hstable : (prefixWord ++ tailWord_3118956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118956).length < 2 ^ (prefixWord ++ tailWord_3118956).sum := by decide
  have hdescent : baseEnd_3118956 < baseStart_3118956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3118977 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3118977 : Nat := 118140960795 + 3118977 * 2 ^ 59
def prefixEnd_3118977 : Nat := 4983230072969 + 3 ^ 40 * 3118977 * 2
def baseEnd_3118977 : Nat := 1067689567545565814562395

theorem tailTrace_3118977 : CollatzResearch.WordTrace tailWord_3118977 prefixEnd_3118977 1067689567545565814562395 := by
  unfold tailWord_3118977
  simp only [CollatzResearch.WordTrace]
  refine ⟨113758436821486482707979185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75838957880990988471986123 113758436821486482707979185)
  ·
    refine ⟨85318827616114862030984389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113758436821486482707979185 85318827616114862030984389)
    ·
      refine ⟨15997280178021536630809573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85318827616114862030984389 15997280178021536630809573)
      ·
        refine ⟨2999490033379038118276795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15997280178021536630809573 2999490033379038118276795)
        ·
          refine ⟨4499235050068557177415193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999490033379038118276795 4499235050068557177415193)
          ·
            refine ⟨3374426287551417883061395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4499235050068557177415193 3374426287551417883061395)
            ·
              refine ⟨5061639431327126824592093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374426287551417883061395 5061639431327126824592093)
              ·
                refine ⟨1898114786747672559222035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5061639431327126824592093 1898114786747672559222035)
                ·
                  refine ⟨2847172180121508838833053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898114786747672559222035 2847172180121508838833053)
                  ·
                    refine ⟨1067689567545565814562395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2847172180121508838833053 1067689567545565814562395)
                    ·
                      rfl

theorem cell22_3118977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3118977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3118977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3118977 prefixEnd_3118977 := by exact prefixLift 3118977
  have htrace : WordTrace (prefixWord ++ tailWord_3118977) baseStart_3118977 baseEnd_3118977 := by
    simpa [prefixWord, tailWord_3118977, baseEnd_3118977] using wordTrace_append hprefix tailTrace_3118977
  have hstable : (prefixWord ++ tailWord_3118977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3118977).length < 2 ^ (prefixWord ++ tailWord_3118977).sum := by decide
  have hdescent : baseEnd_3118977 < baseStart_3118977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3118977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119029 : List Nat := [1, 3, 3, 2, 1, 2, 2, 8]
def baseStart_3119029 : Nat := 118140960795 + 3119029 * 2 ^ 59
def prefixEnd_3119029 : Nat := 4983230072969 + 3 ^ 40 * 3119029 * 2
def baseEnd_3119029 : Nat := 118634152023139445806915

theorem tailTrace_3119029 : CollatzResearch.WordTrace tailWord_3119029 prefixEnd_3119029 118634152023139445806915 := by
  unfold tailWord_3119029
  simp only [CollatzResearch.WordTrace]
  refine ⟨113760333417298095588872141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75840222278198730392581427 113760333417298095588872141)
  ·
    refine ⟨42660125031486785845827053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113760333417298095588872141 42660125031486785845827053)
    ·
      refine ⟨15997546886807544692185145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42660125031486785845827053 15997546886807544692185145)
      ·
        refine ⟨11998160165105658519138859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15997546886807544692185145 11998160165105658519138859)
        ·
          refine ⟨17997240247658487778708289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11998160165105658519138859 17997240247658487778708289)
          ·
            refine ⟨13497930185743865834031217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17997240247658487778708289 13497930185743865834031217)
            ·
              refine ⟨10123447639307899375523413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13497930185743865834031217 10123447639307899375523413)
              ·
                refine ⟨118634152023139445806915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10123447639307899375523413 118634152023139445806915)
                ·
                  rfl

theorem cell22_3119029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 8].length) (baseStart_3119029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119029 prefixEnd_3119029 := by exact prefixLift 3119029
  have htrace : WordTrace (prefixWord ++ tailWord_3119029) baseStart_3119029 baseEnd_3119029 := by
    simpa [prefixWord, tailWord_3119029, baseEnd_3119029] using wordTrace_append hprefix tailTrace_3119029
  have hstable : (prefixWord ++ tailWord_3119029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119029).length < 2 ^ (prefixWord ++ tailWord_3119029).sum := by decide
  have hdescent : baseEnd_3119029 < baseStart_3119029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119104 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_3119104 : Nat := 118140960795 + 3119104 * 2 ^ 59
def prefixEnd_3119104 : Nat := 4983230072969 + 3 ^ 40 * 3119104 * 2
def baseEnd_3119104 : Nat := 1067733042240979816637005

theorem tailTrace_3119104 : CollatzResearch.WordTrace tailWord_3119104 prefixEnd_3119104 1067733042240979816637005 := by
  unfold tailWord_3119104
  simp only [CollatzResearch.WordTrace]
  refine ⟨56881534446013191698926183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75842045928017588931901577 56881534446013191698926183)
  ·
    refine ⟨85322301669019787548389275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56881534446013191698926183 85322301669019787548389275)
    ·
      refine ⟨127983452503529681322583913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85322301669019787548389275 127983452503529681322583913)
      ·
        refine ⟨95987589377647260991937935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127983452503529681322583913 95987589377647260991937935)
        ·
          refine ⟨143981384066470891487906903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95987589377647260991937935 143981384066470891487906903)
          ·
            refine ⟨215972076099706337231860355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143981384066470891487906903 215972076099706337231860355)
            ·
              refine ⟨323958114149559505847790533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215972076099706337231860355 323958114149559505847790533)
              ·
                refine ⟨60742146403042407346460725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323958114149559505847790533 60742146403042407346460725)
                ·
                  refine ⟨5694576225285225688730693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60742146403042407346460725 5694576225285225688730693)
                  ·
                    refine ⟨1067733042240979816637005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5694576225285225688730693 1067733042240979816637005)
                    ·
                      rfl

theorem cell22_3119104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_3119104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119104 prefixEnd_3119104 := by exact prefixLift 3119104
  have htrace : WordTrace (prefixWord ++ tailWord_3119104) baseStart_3119104 baseEnd_3119104 := by
    simpa [prefixWord, tailWord_3119104, baseEnd_3119104] using wordTrace_append hprefix tailTrace_3119104
  have hstable : (prefixWord ++ tailWord_3119104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119104).length < 2 ^ (prefixWord ++ tailWord_3119104).sum := by decide
  have hdescent : baseEnd_3119104 < baseStart_3119104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119108 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 7]
def baseStart_3119108 : Nat := 118140960795 + 3119108 * 2 ^ 59
def prefixEnd_3119108 : Nat := 4983230072969 + 3 ^ 40 * 3119108 * 2
def baseEnd_3119108 : Nat := 355911470507575046512331

theorem tailTrace_3119108 : CollatzResearch.WordTrace tailWord_3119108 prefixEnd_3119108 355911470507575046512331 := by
  unfold tailWord_3119108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56881607392005946040498989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75842143189341261387331985 56881607392005946040498989)
  ·
    refine ⟨21330602772002229765187121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56881607392005946040498989 21330602772002229765187121)
    ·
      refine ⟨15997952079001672323890341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21330602772002229765187121 15997952079001672323890341)
      ·
        refine ⟨2999616014812813560729439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15997952079001672323890341 2999616014812813560729439)
        ·
          refine ⟨4499424022219220341094159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999616014812813560729439 4499424022219220341094159)
          ·
            refine ⟨6749136033328830511641239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499424022219220341094159 6749136033328830511641239)
            ·
              refine ⟨10123704049993245767461859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749136033328830511641239 10123704049993245767461859)
              ·
                refine ⟨15185556074989868651192789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10123704049993245767461859 15185556074989868651192789)
                ·
                  refine ⟨355911470507575046512331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15185556074989868651192789 355911470507575046512331)
                  ·
                    rfl

theorem cell22_3119108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_3119108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119108 prefixEnd_3119108 := by exact prefixLift 3119108
  have htrace : WordTrace (prefixWord ++ tailWord_3119108) baseStart_3119108 baseEnd_3119108 := by
    simpa [prefixWord, tailWord_3119108, baseEnd_3119108] using wordTrace_append hprefix tailTrace_3119108
  have hstable : (prefixWord ++ tailWord_3119108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119108).length < 2 ^ (prefixWord ++ tailWord_3119108).sum := by decide
  have hdescent : baseEnd_3119108 < baseStart_3119108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119138 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3119138 : Nat := 118140960795 + 3119138 * 2 ^ 59
def prefixEnd_3119138 : Nat := 4983230072969 + 3 ^ 40 * 3119138 * 2
def baseEnd_3119138 : Nat := 1067744681135815061286901

theorem tailTrace_3119138 : CollatzResearch.WordTrace tailWord_3119138 prefixEnd_3119138 1067744681135815061286901 := by
  unfold tailWord_3119138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28441077243475801801147517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75842872649268804803060045 28441077243475801801147517)
  ·
    refine ⟨10665403966303425675430319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28441077243475801801147517 10665403966303425675430319)
    ·
      refine ⟨15998105949455138513145479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10665403966303425675430319 15998105949455138513145479)
      ·
        refine ⟨23997158924182707769718219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15998105949455138513145479 23997158924182707769718219)
        ·
          refine ⟨35995738386274061654577329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23997158924182707769718219 35995738386274061654577329)
          ·
            refine ⟨26996803789705546240932997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35995738386274061654577329 26996803789705546240932997)
            ·
              refine ⟨5061900710569789920174937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26996803789705546240932997 5061900710569789920174937)
              ·
                refine ⟨3796425532927342440131203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061900710569789920174937 3796425532927342440131203)
                ·
                  refine ⟨5694638299391013660196805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796425532927342440131203 5694638299391013660196805)
                  ·
                    refine ⟨1067744681135815061286901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5694638299391013660196805 1067744681135815061286901)
                    ·
                      rfl

theorem cell22_3119138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3119138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119138 prefixEnd_3119138 := by exact prefixLift 3119138
  have htrace : WordTrace (prefixWord ++ tailWord_3119138) baseStart_3119138 baseEnd_3119138 := by
    simpa [prefixWord, tailWord_3119138, baseEnd_3119138] using wordTrace_append hprefix tailTrace_3119138
  have hstable : (prefixWord ++ tailWord_3119138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119138).length < 2 ^ (prefixWord ++ tailWord_3119138).sum := by decide
  have hdescent : baseEnd_3119138 < baseStart_3119138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119153 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 4]
def baseStart_3119153 : Nat := 118140960795 + 3119153 * 2 ^ 59
def prefixEnd_3119153 : Nat := 4983230072969 + 3 ^ 40 * 3119153 * 2
def baseEnd_3119153 : Nat := 355916605314120007387285

theorem tailTrace_3119153 : CollatzResearch.WordTrace tailWord_3119153 prefixEnd_3119153 355916605314120007387285 := by
  unfold tailWord_3119153
  simp only [CollatzResearch.WordTrace]
  refine ⟨113764856068848864766386113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75843237379232576510924075 113764856068848864766386113)
  ·
    refine ⟨85323642051636648574789585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113764856068848864766386113 85323642051636648574789585)
    ·
      refine ⟨63992731538727486431092189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85323642051636648574789585 63992731538727486431092189)
      ·
        refine ⟨23997274327022807411659571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63992731538727486431092189 23997274327022807411659571)
        ·
          refine ⟨35995911490534211117489357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23997274327022807411659571 35995911490534211117489357)
          ·
            refine ⟨13498466808950329169058509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35995911490534211117489357 13498466808950329169058509)
            ·
              refine ⟨5061925053356373438396941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13498466808950329169058509 5061925053356373438396941)
              ·
                refine ⟨1898221895008640039398853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5061925053356373438396941 1898221895008640039398853)
                ·
                  refine ⟨355916605314120007387285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898221895008640039398853 355916605314120007387285)
                  ·
                    rfl

theorem cell22_3119153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_3119153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119153 prefixEnd_3119153 := by exact prefixLift 3119153
  have htrace : WordTrace (prefixWord ++ tailWord_3119153) baseStart_3119153 baseEnd_3119153 := by
    simpa [prefixWord, tailWord_3119153, baseEnd_3119153] using wordTrace_append hprefix tailTrace_3119153
  have hstable : (prefixWord ++ tailWord_3119153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119153).length < 2 ^ (prefixWord ++ tailWord_3119153).sum := by decide
  have hdescent : baseEnd_3119153 < baseStart_3119153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119241 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_3119241 : Nat := 118140960795 + 3119241 * 2 ^ 59
def prefixEnd_3119241 : Nat := 4983230072969 + 3 ^ 40 * 3119241 * 2
def baseEnd_3119241 : Nat := 1067779940140757125961585

theorem tailTrace_3119241 : CollatzResearch.WordTrace tailWord_3119241 prefixEnd_3119241 1067779940140757125961585 := by
  unfold tailWord_3119241
  simp only [CollatzResearch.WordTrace]
  refine ⟨113768065692530055795589577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75845377128353370530393051 113768065692530055795589577)
  ·
    refine ⟨85326049269397541846692183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113768065692530055795589577 85326049269397541846692183)
    ·
      refine ⟨127989073904096312770038275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85326049269397541846692183 127989073904096312770038275)
      ·
        refine ⟨191983610856144469155057413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127989073904096312770038275 191983610856144469155057413)
        ·
          refine ⟨35996927035527087966573265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191983610856144469155057413 35996927035527087966573265)
          ·
            refine ⟨26997695276645315974929949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35996927035527087966573265 26997695276645315974929949)
            ·
              refine ⟨10124135728741993490598731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26997695276645315974929949 10124135728741993490598731)
              ·
                refine ⟨15186203593112990235898097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10124135728741993490598731 15186203593112990235898097)
                ·
                  refine ⟨11389652694834742676923573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15186203593112990235898097 11389652694834742676923573)
                  ·
                    refine ⟨1067779940140757125961585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11389652694834742676923573 1067779940140757125961585)
                    ·
                      rfl

theorem cell22_3119241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_3119241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119241 prefixEnd_3119241 := by exact prefixLift 3119241
  have htrace : WordTrace (prefixWord ++ tailWord_3119241) baseStart_3119241 baseEnd_3119241 := by
    simpa [prefixWord, tailWord_3119241, baseEnd_3119241] using wordTrace_append hprefix tailTrace_3119241
  have hstable : (prefixWord ++ tailWord_3119241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119241).length < 2 ^ (prefixWord ++ tailWord_3119241).sum := by decide
  have hdescent : baseEnd_3119241 < baseStart_3119241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119288 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 4]
def baseStart_3119288 : Nat := 118140960795 + 3119288 * 2 ^ 59
def prefixEnd_3119288 : Nat := 4983230072969 + 3 ^ 40 * 3119288 * 2
def baseEnd_3119288 : Nat := 355932009733754890012147

theorem tailTrace_3119288 : CollatzResearch.WordTrace tailWord_3119288 prefixEnd_3119288 355932009733754890012147 := by
  unfold tailWord_3119288
  simp only [CollatzResearch.WordTrace]
  refine ⟨56884889961679891411275259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75846519948906521881700345 56884889961679891411275259)
  ·
    refine ⟨85327334942519837116912889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56884889961679891411275259 85327334942519837116912889)
    ·
      refine ⟨63995501206889877837684667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85327334942519837116912889 63995501206889877837684667)
      ·
        refine ⟨95993251810334816756527001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63995501206889877837684667 95993251810334816756527001)
        ·
          refine ⟨71994938857751112567395251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95993251810334816756527001 71994938857751112567395251)
          ·
            refine ⟨107992408286626668851092877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71994938857751112567395251 107992408286626668851092877)
            ·
              refine ⟨40497153107485000819159829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107992408286626668851092877 40497153107485000819159829)
              ·
                refine ⟨1898304051913359413398117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40497153107485000819159829 1898304051913359413398117)
                ·
                  refine ⟨355932009733754890012147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898304051913359413398117 355932009733754890012147)
                  ·
                    rfl

theorem cell22_3119288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_3119288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119288 prefixEnd_3119288 := by exact prefixLift 3119288
  have htrace : WordTrace (prefixWord ++ tailWord_3119288) baseStart_3119288 baseEnd_3119288 := by
    simpa [prefixWord, tailWord_3119288, baseEnd_3119288] using wordTrace_append hprefix tailTrace_3119288
  have hstable : (prefixWord ++ tailWord_3119288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119288).length < 2 ^ (prefixWord ++ tailWord_3119288).sum := by decide
  have hdescent : baseEnd_3119288 < baseStart_3119288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119301 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_3119301 : Nat := 118140960795 + 3119301 * 2 ^ 59
def prefixEnd_3119301 : Nat := 4983230072969 + 3 ^ 40 * 3119301 * 2
def baseEnd_3119301 : Nat := 1067800479366936969461401

theorem tailTrace_3119301 : CollatzResearch.WordTrace tailWord_3119301 prefixEnd_3119301 1067800479366936969461401 := by
  unfold tailWord_3119301
  simp only [CollatzResearch.WordTrace]
  refine ⟨113770254072312686042773757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75846836048208457361849171 113770254072312686042773757)
  ·
    refine ⟨42663845277117257266040159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113770254072312686042773757 42663845277117257266040159)
    ·
      refine ⟨63995767915675885899060239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42663845277117257266040159 63995767915675885899060239)
      ·
        refine ⟨95993651873513828848590359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63995767915675885899060239 95993651873513828848590359)
        ·
          refine ⟨143990477810270743272885539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95993651873513828848590359 143990477810270743272885539)
          ·
            refine ⟨215985716715406114909328309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143990477810270743272885539 215985716715406114909328309)
            ·
              refine ⟨20248660942069323272749529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215985716715406114909328309 20248660942069323272749529)
              ·
                refine ⟨15186495706551992454562147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20248660942069323272749529 15186495706551992454562147)
                ·
                  refine ⟨22779743559827988681843221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15186495706551992454562147 22779743559827988681843221)
                  ·
                    refine ⟨1067800479366936969461401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22779743559827988681843221 1067800479366936969461401)
                    ·
                      rfl

theorem cell22_3119301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_3119301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119301 prefixEnd_3119301 := by exact prefixLift 3119301
  have htrace : WordTrace (prefixWord ++ tailWord_3119301) baseStart_3119301 baseEnd_3119301 := by
    simpa [prefixWord, tailWord_3119301, baseEnd_3119301] using wordTrace_append hprefix tailTrace_3119301
  have hstable : (prefixWord ++ tailWord_3119301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119301).length < 2 ^ (prefixWord ++ tailWord_3119301).sum := by decide
  have hdescent : baseEnd_3119301 < baseStart_3119301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119333 : List Nat := [1, 3, 1, 4, 2, 3, 8]
def baseStart_3119333 : Nat := 118140960795 + 3119333 * 2 ^ 59
def prefixEnd_3119333 : Nat := 4983230072969 + 3 ^ 40 * 3119333 * 2
def baseEnd_3119333 : Nat := 39548571615588872320789

theorem tailTrace_3119333 : CollatzResearch.WordTrace tailWord_3119333 prefixEnd_3119333 39548571615588872320789 := by
  unfold tailWord_3119333
  simp only [CollatzResearch.WordTrace]
  refine ⟨113771421208196755507938653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75847614138797837005292435 113771421208196755507938653)
  ·
    refine ⟨42664282953073783315476995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113771421208196755507938653 42664282953073783315476995)
    ·
      refine ⟨63996424429610674973215493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42664282953073783315476995 63996424429610674973215493)
      ·
        refine ⟨11999329580552001557477905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63996424429610674973215493 11999329580552001557477905)
        ·
          refine ⟨8999497185414001168108429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11999329580552001557477905 8999497185414001168108429)
          ·
            refine ⟨3374811444530250438040661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8999497185414001168108429 3374811444530250438040661)
            ·
              refine ⟨39548571615588872320789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3374811444530250438040661 39548571615588872320789)
              ·
                rfl

theorem cell22_3119333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 8].length) (baseStart_3119333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119333 prefixEnd_3119333 := by exact prefixLift 3119333
  have htrace : WordTrace (prefixWord ++ tailWord_3119333) baseStart_3119333 baseEnd_3119333 := by
    simpa [prefixWord, tailWord_3119333, baseEnd_3119333] using wordTrace_append hprefix tailTrace_3119333
  have hstable : (prefixWord ++ tailWord_3119333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119333).length < 2 ^ (prefixWord ++ tailWord_3119333).sum := by decide
  have hdescent : baseEnd_3119333 < baseStart_3119333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119335 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3119335 : Nat := 118140960795 + 3119335 * 2 ^ 59
def prefixEnd_3119335 : Nat := 4983230072969 + 3 ^ 40 * 3119335 * 2
def baseEnd_3119335 : Nat := 1067812118261772214111297

theorem tailTrace_3119335 : CollatzResearch.WordTrace tailWord_3119335 prefixEnd_3119335 1067812118261772214111297 := by
  unfold tailWord_3119335
  simp only [CollatzResearch.WordTrace]
  refine ⟨113771494154189509849511459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75847662769459673233007639 113771494154189509849511459)
  ·
    refine ⟨170657241231284264774267189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113771494154189509849511459 170657241231284264774267189)
    ·
      refine ⟨15999116365432899822587549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170657241231284264774267189 15999116365432899822587549)
      ·
        refine ⟨5999668637037337433470331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15999116365432899822587549 5999668637037337433470331)
        ·
          refine ⟨8999502955556006150205497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5999668637037337433470331 8999502955556006150205497)
          ·
            refine ⟨6749627216667004612654123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8999502955556006150205497 6749627216667004612654123)
            ·
              refine ⟨10124440825000506918981185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749627216667004612654123 10124440825000506918981185)
              ·
                refine ⟨7593330618750380189235889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10124440825000506918981185 7593330618750380189235889)
                ·
                  refine ⟨5694997964062785141926917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7593330618750380189235889 5694997964062785141926917)
                  ·
                    refine ⟨1067812118261772214111297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5694997964062785141926917 1067812118261772214111297)
                    ·
                      rfl

theorem cell22_3119335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3119335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119335 prefixEnd_3119335 := by exact prefixLift 3119335
  have htrace : WordTrace (prefixWord ++ tailWord_3119335) baseStart_3119335 baseEnd_3119335 := by
    simpa [prefixWord, tailWord_3119335, baseEnd_3119335] using wordTrace_append hprefix tailTrace_3119335
  have hstable : (prefixWord ++ tailWord_3119335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119335).length < 2 ^ (prefixWord ++ tailWord_3119335).sum := by decide
  have hdescent : baseEnd_3119335 < baseStart_3119335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119410 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3119410 : Nat := 118140960795 + 3119410 * 2 ^ 59
def prefixEnd_3119410 : Nat := 4983230072969 + 3 ^ 40 * 3119410 * 2
def baseEnd_3119410 : Nat := 1067837792294497018486067

theorem tailTrace_3119410 : CollatzResearch.WordTrace tailWord_3119410 prefixEnd_3119410 1067837792294497018486067 := by
  unfold tailWord_3119410
  simp only [CollatzResearch.WordTrace]
  refine ⟨28443557407229449414622921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75849486419278531772327789 28443557407229449414622921)
  ·
    refine ⟨21332668055422087060967191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28443557407229449414622921 21332668055422087060967191)
    ·
      refine ⟨31999002083133130591450787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21332668055422087060967191 31999002083133130591450787)
      ·
        refine ⟨47998503124699695887176181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31999002083133130591450787 47998503124699695887176181)
        ·
          refine ⟨4499859667940596489422767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47998503124699695887176181 4499859667940596489422767)
          ·
            refine ⟨6749789501910894734134151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499859667940596489422767 6749789501910894734134151)
            ·
              refine ⟨10124684252866342101201227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749789501910894734134151 10124684252866342101201227)
              ·
                refine ⟨15187026379299513151801841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10124684252866342101201227 15187026379299513151801841)
                ·
                  refine ⟨11390269784474634863851381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15187026379299513151801841 11390269784474634863851381)
                  ·
                    refine ⟨1067837792294497018486067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11390269784474634863851381 1067837792294497018486067)
                    ·
                      rfl

theorem cell22_3119410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3119410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119410 prefixEnd_3119410 := by exact prefixLift 3119410
  have htrace : WordTrace (prefixWord ++ tailWord_3119410) baseStart_3119410 baseEnd_3119410 := by
    simpa [prefixWord, tailWord_3119410, baseEnd_3119410] using wordTrace_append hprefix tailTrace_3119410
  have hstable : (prefixWord ++ tailWord_3119410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119410).length < 2 ^ (prefixWord ++ tailWord_3119410).sum := by decide
  have hdescent : baseEnd_3119410 < baseStart_3119410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119423 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 6]
def baseStart_3119423 : Nat := 118140960795 + 3119423 * 2 ^ 59
def prefixEnd_3119423 : Nat := 4983230072969 + 3 ^ 40 * 3119423 * 2
def baseEnd_3119423 : Nat := 355947414153389772637009

theorem tailTrace_3119423 : CollatzResearch.WordTrace tailWord_3119423 prefixEnd_3119423 355947414153389772637009 := by
  unfold tailWord_3119423
  simp only [CollatzResearch.WordTrace]
  refine ⟨113774703777870700878714923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75849802518580467252476615 113774703777870700878714923)
  ·
    refine ⟨170662055666806051318072385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113774703777870700878714923 170662055666806051318072385)
    ·
      refine ⟨127996541750104538488554289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170662055666806051318072385 127996541750104538488554289)
      ·
        refine ⟨95997406312578403866415717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127996541750104538488554289 95997406312578403866415717)
        ·
          refine ⟨17999513683608450724952947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95997406312578403866415717 17999513683608450724952947)
          ·
            refine ⟨26999270525412676087429421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17999513683608450724952947 26999270525412676087429421)
            ·
              refine ⟨10124726447029753532786033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26999270525412676087429421 10124726447029753532786033)
              ·
                refine ⟨7593544835272315149589525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10124726447029753532786033 7593544835272315149589525)
                ·
                  refine ⟨355947414153389772637009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7593544835272315149589525 355947414153389772637009)
                  ·
                    rfl

theorem cell22_3119423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 6].length) (baseStart_3119423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119423 prefixEnd_3119423 := by exact prefixLift 3119423
  have htrace : WordTrace (prefixWord ++ tailWord_3119423) baseStart_3119423 baseEnd_3119423 := by
    simpa [prefixWord, tailWord_3119423, baseEnd_3119423] using wordTrace_append hprefix tailTrace_3119423
  have hstable : (prefixWord ++ tailWord_3119423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119423).length < 2 ^ (prefixWord ++ tailWord_3119423).sum := by decide
  have hdescent : baseEnd_3119423 < baseStart_3119423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119438 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3119438 : Nat := 118140960795 + 3119438 * 2 ^ 59
def prefixEnd_3119438 : Nat := 4983230072969 + 3 ^ 40 * 3119438 * 2
def baseEnd_3119438 : Nat := 1067847377266714278785981

theorem tailTrace_3119438 : CollatzResearch.WordTrace tailWord_3119438 prefixEnd_3119438 1067847377266714278785981 := by
  unfold tailWord_3119438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14221906359102044805063871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75850167248544238960340645 14221906359102044805063871)
  ·
    refine ⟨21332859538653067207595807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14221906359102044805063871 21332859538653067207595807)
    ·
      refine ⟨31999289307979600811393711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21332859538653067207595807 31999289307979600811393711)
      ·
        refine ⟨47998933961969401217090567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31999289307979600811393711 47998933961969401217090567)
        ·
          refine ⟨71998400942954101825635851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47998933961969401217090567 71998400942954101825635851)
          ·
            refine ⟨107997601414431152738453777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71998400942954101825635851 107997601414431152738453777)
            ·
              refine ⟨80998201060823364553840333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107997601414431152738453777 80998201060823364553840333)
              ·
                refine ⟨30374325397808761707690125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80998201060823364553840333 30374325397808761707690125)
                ·
                  refine ⟨11390372024178285640383797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30374325397808761707690125 11390372024178285640383797)
                  ·
                    refine ⟨1067847377266714278785981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11390372024178285640383797 1067847377266714278785981)
                    ·
                      rfl

theorem cell22_3119438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3119438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119438 prefixEnd_3119438 := by exact prefixLift 3119438
  have htrace : WordTrace (prefixWord ++ tailWord_3119438) baseStart_3119438 baseEnd_3119438 := by
    simpa [prefixWord, tailWord_3119438, baseEnd_3119438] using wordTrace_append hprefix tailTrace_3119438
  have hstable : (prefixWord ++ tailWord_3119438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119438).length < 2 ^ (prefixWord ++ tailWord_3119438).sum := by decide
  have hdescent : baseEnd_3119438 < baseStart_3119438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119440 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 4]
def baseStart_3119440 : Nat := 118140960795 + 3119440 * 2 ^ 59
def prefixEnd_3119440 : Nat := 4983230072969 + 3 ^ 40 * 3119440 * 2
def baseEnd_3119440 : Nat := 355949353969195646745325

theorem tailTrace_3119440 : CollatzResearch.WordTrace tailWord_3119440 prefixEnd_3119440 355949353969195646745325 := by
  unfold tailWord_3119440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56887661909404556391041887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75850215879206075188055849 56887661909404556391041887)
  ·
    refine ⟨85331492864106834586562831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56887661909404556391041887 85331492864106834586562831)
    ·
      refine ⟨127997239296160251879844247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85331492864106834586562831 127997239296160251879844247)
      ·
        refine ⟨191995858944240377819766371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127997239296160251879844247 191995858944240377819766371)
        ·
          refine ⟨287993788416360566729649557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191995858944240377819766371 287993788416360566729649557)
          ·
            refine ⟨13499708832016901565452323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 287993788416360566729649557 13499708832016901565452323)
            ·
              refine ⟨20249563248025352348178485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13499708832016901565452323 20249563248025352348178485)
              ·
                refine ⟨1898396554502376782641733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20249563248025352348178485 1898396554502376782641733)
                ·
                  refine ⟨355949353969195646745325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898396554502376782641733 355949353969195646745325)
                  ·
                    rfl

theorem cell22_3119440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_3119440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119440 prefixEnd_3119440 := by exact prefixLift 3119440
  have htrace : WordTrace (prefixWord ++ tailWord_3119440) baseStart_3119440 baseEnd_3119440 := by
    simpa [prefixWord, tailWord_3119440, baseEnd_3119440] using wordTrace_append hprefix tailTrace_3119440
  have hstable : (prefixWord ++ tailWord_3119440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119440).length < 2 ^ (prefixWord ++ tailWord_3119440).sum := by decide
  have hdescent : baseEnd_3119440 < baseStart_3119440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119442 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3119442 : Nat := 118140960795 + 3119442 * 2 ^ 59
def prefixEnd_3119442 : Nat := 4983230072969 + 3 ^ 40 * 3119442 * 2
def baseEnd_3119442 : Nat := 1067848746548459601685969

theorem tailTrace_3119442 : CollatzResearch.WordTrace tailWord_3119442 prefixEnd_3119442 1067848746548459601685969 := by
  unfold tailWord_3119442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28443849191200466780914145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75850264509867911415771053 28443849191200466780914145)
  ·
    refine ⟨21332886893400350085685609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28443849191200466780914145 21332886893400350085685609)
    ·
      refine ⟨15999665170050262564264207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21332886893400350085685609 15999665170050262564264207)
      ·
        refine ⟨23999497755075393846396311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999665170050262564264207 23999497755075393846396311)
        ·
          refine ⟨35999246632613090769594467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23999497755075393846396311 35999246632613090769594467)
          ·
            refine ⟨53998869948919636154391701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35999246632613090769594467 53998869948919636154391701)
            ·
              refine ⟨2531197028855607944737111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53998869948919636154391701 2531197028855607944737111)
              ·
                refine ⟨3796795543283411917105667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531197028855607944737111 3796795543283411917105667)
                ·
                  refine ⟨5695193314925117875658501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796795543283411917105667 5695193314925117875658501)
                  ·
                    refine ⟨1067848746548459601685969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5695193314925117875658501 1067848746548459601685969)
                    ·
                      rfl

theorem cell22_3119442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3119442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119442 prefixEnd_3119442 := by exact prefixLift 3119442
  have htrace : WordTrace (prefixWord ++ tailWord_3119442) baseStart_3119442 baseEnd_3119442 := by
    simpa [prefixWord, tailWord_3119442, baseEnd_3119442] using wordTrace_append hprefix tailTrace_3119442
  have hstable : (prefixWord ++ tailWord_3119442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119442).length < 2 ^ (prefixWord ++ tailWord_3119442).sum := by decide
  have hdescent : baseEnd_3119442 < baseStart_3119442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119485 : List Nat := [1, 4, 1, 1, 2, 3, 4, 6]
def baseStart_3119485 : Nat := 118140960795 + 3119485 * 2 ^ 59
def prefixEnd_3119485 : Nat := 4983230072969 + 3 ^ 40 * 3119485 * 2
def baseEnd_3119485 : Nat := 118651496258580202540093

theorem tailTrace_3119485 : CollatzResearch.WordTrace tailWord_3119485 prefixEnd_3119485 118651496258580202540093 := by
  unfold tailWord_3119485
  simp only [CollatzResearch.WordTrace]
  refine ⟨113776965103646085467471909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75851310069097390311647939 113776965103646085467471909)
  ·
    refine ⟨21333180956933641025150983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113776965103646085467471909 21333180956933641025150983)
    ·
      refine ⟨31999771435400461537726475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21333180956933641025150983 31999771435400461537726475)
      ·
        refine ⟨47999657153100692306589713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31999771435400461537726475 47999657153100692306589713)
        ·
          refine ⟨35999742864825519229942285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47999657153100692306589713 35999742864825519229942285)
          ·
            refine ⟨13499903574309569711228357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35999742864825519229942285 13499903574309569711228357)
            ·
              refine ⟨2531231920183044320855317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13499903574309569711228357 2531231920183044320855317)
              ·
                refine ⟨118651496258580202540093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2531231920183044320855317 118651496258580202540093)
                ·
                  rfl

theorem cell22_3119485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 6].length) (baseStart_3119485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119485 prefixEnd_3119485 := by exact prefixLift 3119485
  have htrace : WordTrace (prefixWord ++ tailWord_3119485) baseStart_3119485 baseEnd_3119485 := by
    simpa [prefixWord, tailWord_3119485, baseEnd_3119485] using wordTrace_append hprefix tailTrace_3119485
  have hstable : (prefixWord ++ tailWord_3119485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119485).length < 2 ^ (prefixWord ++ tailWord_3119485).sum := by decide
  have hdescent : baseEnd_3119485 < baseStart_3119485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119513 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 7]
def baseStart_3119513 : Nat := 118140960795 + 3119513 * 2 ^ 59
def prefixEnd_3119513 : Nat := 4983230072969 + 3 ^ 40 * 3119513 * 2
def baseEnd_3119513 : Nat := 355957683766479694386917

theorem tailTrace_3119513 : CollatzResearch.WordTrace tailWord_3119513 prefixEnd_3119513 355957683766479694386917 := by
  unfold tailWord_3119513
  simp only [CollatzResearch.WordTrace]
  refine ⟨113777986347544646249491193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75851990898363097499660795 113777986347544646249491193)
  ·
    refine ⟨85333489760658484687118395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113777986347544646249491193 85333489760658484687118395)
    ·
      refine ⟨128000234640987727030677593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85333489760658484687118395 128000234640987727030677593)
      ·
        refine ⟨96000175980740795273008195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128000234640987727030677593 96000175980740795273008195)
        ·
          refine ⟨144000263971111192909512293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96000175980740795273008195 144000263971111192909512293)
          ·
            refine ⟨27000049494583348670533555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144000263971111192909512293 27000049494583348670533555)
            ·
              refine ⟨40500074241875023005800333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27000049494583348670533555 40500074241875023005800333)
              ·
                refine ⟨15187527840703133627175125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40500074241875023005800333 15187527840703133627175125)
                ·
                  refine ⟨355957683766479694386917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15187527840703133627175125 355957683766479694386917)
                  ·
                    rfl

theorem cell22_3119513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_3119513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119513 prefixEnd_3119513 := by exact prefixLift 3119513
  have htrace : WordTrace (prefixWord ++ tailWord_3119513) baseStart_3119513 baseEnd_3119513 := by
    simpa [prefixWord, tailWord_3119513, baseEnd_3119513] using wordTrace_append hprefix tailTrace_3119513
  have hstable : (prefixWord ++ tailWord_3119513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119513).length < 2 ^ (prefixWord ++ tailWord_3119513).sum := by decide
  have hdescent : baseEnd_3119513 < baseStart_3119513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119665 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 7]
def baseStart_3119665 : Nat := 118140960795 + 3119665 * 2 ^ 59
def prefixEnd_3119665 : Nat := 4983230072969 + 3 ^ 40 * 3119665 * 2
def baseEnd_3119665 : Nat := 355975028001920451120095

theorem tailTrace_3119665 : CollatzResearch.WordTrace tailWord_3119665 prefixEnd_3119665 355975028001920451120095 := by
  unfold tailWord_3119665
  simp only [CollatzResearch.WordTrace]
  refine ⟨113783530242993976209024449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75855686828662650806016299 113783530242993976209024449)
  ·
    refine ⟨85337647682245482156768337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113783530242993976209024449 85337647682245482156768337)
    ·
      refine ⟨64003235761684111617576253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85337647682245482156768337 64003235761684111617576253)
      ·
        refine ⟨24001213410631541856591095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64003235761684111617576253 24001213410631541856591095)
        ·
          refine ⟨36001820115947312784886643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24001213410631541856591095 36001820115947312784886643)
          ·
            refine ⟨54002730173920969177329965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36001820115947312784886643 54002730173920969177329965)
            ·
              refine ⟨20251023815220363441498737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54002730173920969177329965 20251023815220363441498737)
              ·
                refine ⟨15188267861415272581124053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20251023815220363441498737 15188267861415272581124053)
                ·
                  refine ⟨355975028001920451120095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15188267861415272581124053 355975028001920451120095)
                  ·
                    rfl

theorem cell22_3119665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_3119665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119665 prefixEnd_3119665 := by exact prefixLift 3119665
  have htrace : WordTrace (prefixWord ++ tailWord_3119665) baseStart_3119665 baseEnd_3119665 := by
    simpa [prefixWord, tailWord_3119665, baseEnd_3119665] using wordTrace_append hprefix tailTrace_3119665
  have hstable : (prefixWord ++ tailWord_3119665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119665).length < 2 ^ (prefixWord ++ tailWord_3119665).sum := by decide
  have hdescent : baseEnd_3119665 < baseStart_3119665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119680 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_3119680 : Nat := 118140960795 + 3119680 * 2 ^ 59
def prefixEnd_3119680 : Nat := 4983230072969 + 3 ^ 40 * 3119680 * 2
def baseEnd_3119680 : Nat := 1067930218812306314235239

theorem tailTrace_3119680 : CollatzResearch.WordTrace tailWord_3119680 prefixEnd_3119680 1067930218812306314235239 := by
  unfold tailWord_3119680
  simp only [CollatzResearch.WordTrace]
  refine ⟨56892038668969816885410247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75856051558626422513880329 56892038668969816885410247)
  ·
    refine ⟨85338058003454725328115371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56892038668969816885410247 85338058003454725328115371)
    ·
      refine ⟨128007087005182087992173057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85338058003454725328115371 128007087005182087992173057)
      ·
        refine ⟨96005315253886565994129793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128007087005182087992173057 96005315253886565994129793)
        ·
          refine ⟨72003986440414924495597345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96005315253886565994129793 72003986440414924495597345)
          ·
            refine ⟨54002989830311193371698009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72003986440414924495597345 54002989830311193371698009)
            ·
              refine ⟨40502242372733395028773507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54002989830311193371698009 40502242372733395028773507)
              ·
                refine ⟨60753363559100092543160261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40502242372733395028773507 60753363559100092543160261)
                ·
                  refine ⟨11391255667331267351842549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60753363559100092543160261 11391255667331267351842549)
                  ·
                    refine ⟨1067930218812306314235239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11391255667331267351842549 1067930218812306314235239)
                    ·
                      rfl

theorem cell22_3119680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_3119680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119680 prefixEnd_3119680 := by exact prefixLift 3119680
  have htrace : WordTrace (prefixWord ++ tailWord_3119680) baseStart_3119680 baseEnd_3119680 := by
    simpa [prefixWord, tailWord_3119680, baseEnd_3119680] using wordTrace_append hprefix tailTrace_3119680
  have hstable : (prefixWord ++ tailWord_3119680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119680).length < 2 ^ (prefixWord ++ tailWord_3119680).sum := by decide
  have hdescent : baseEnd_3119680 < baseStart_3119680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119744 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 4]
def baseStart_3119744 : Nat := 118140960795 + 3119744 * 2 ^ 59
def prefixEnd_3119744 : Nat := 4983230072969 + 3 ^ 40 * 3119744 * 2
def baseEnd_3119744 : Nat := 355984042440077160211681

theorem tailTrace_3119744 : CollatzResearch.WordTrace tailWord_3119744 prefixEnd_3119744 355984042440077160211681 := by
  unfold tailWord_3119744
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893205804853886350575143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75857607739805181800766857 56893205804853886350575143)
  ·
    refine ⟨85339808707280829525862715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56893205804853886350575143 85339808707280829525862715)
    ·
      refine ⟨128009713060921244288794073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85339808707280829525862715 128009713060921244288794073)
      ·
        refine ⟨96007284795690933216595555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128009713060921244288794073 96007284795690933216595555)
        ·
          refine ⟨144010927193536399824893333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96007284795690933216595555 144010927193536399824893333)
          ·
            refine ⟨6750512212197018741791875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144010927193536399824893333 6750512212197018741791875)
            ·
              refine ⟨10125768318295528112687813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750512212197018741791875 10125768318295528112687813)
              ·
                refine ⟨1898581559680411521128965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10125768318295528112687813 1898581559680411521128965)
                ·
                  refine ⟨355984042440077160211681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898581559680411521128965 355984042440077160211681)
                  ·
                    rfl

theorem cell22_3119744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_3119744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119744 prefixEnd_3119744 := by exact prefixLift 3119744
  have htrace : WordTrace (prefixWord ++ tailWord_3119744) baseStart_3119744 baseEnd_3119744 := by
    simpa [prefixWord, tailWord_3119744, baseEnd_3119744] using wordTrace_append hprefix tailTrace_3119744
  have hstable : (prefixWord ++ tailWord_3119744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119744).length < 2 ^ (prefixWord ++ tailWord_3119744).sum := by decide
  have hdescent : baseEnd_3119744 < baseStart_3119744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119755 : List Nat := [1, 1, 1, 1, 4, 1, 2, 11]
def baseStart_3119755 : Nat := 118140960795 + 3119755 * 2 ^ 59
def prefixEnd_3119755 : Nat := 4983230072969 + 3 ^ 40 * 3119755 * 2
def baseEnd_3119755 : Nat := 118661765871670124290001

theorem tailTrace_3119755 : CollatzResearch.WordTrace tailWord_3119755 prefixEnd_3119755 118661765871670124290001 := by
  unfold tailWord_3119755
  simp only [CollatzResearch.WordTrace]
  refine ⟨113786812812667921579800719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75857875208445281053200479 113786812812667921579800719)
  ·
    refine ⟨170680219219001882369701079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113786812812667921579800719 170680219219001882369701079)
    ·
      refine ⟨256020328828502823554551619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170680219219001882369701079 256020328828502823554551619)
      ·
        refine ⟨384030493242754235331827429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256020328828502823554551619 384030493242754235331827429)
        ·
          refine ⟨72005717483016419124717643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384030493242754235331827429 72005717483016419124717643)
          ·
            refine ⟨108008576224524628687076465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72005717483016419124717643 108008576224524628687076465)
            ·
              refine ⟨81006432168393471515307349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108008576224524628687076465 81006432168393471515307349)
              ·
                refine ⟨118661765871670124290001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 81006432168393471515307349 118661765871670124290001)
                ·
                  rfl

theorem cell22_3119755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 11].length) (baseStart_3119755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119755 prefixEnd_3119755 := by exact prefixLift 3119755
  have htrace : WordTrace (prefixWord ++ tailWord_3119755) baseStart_3119755 baseEnd_3119755 := by
    simpa [prefixWord, tailWord_3119755, baseEnd_3119755] using wordTrace_append hprefix tailTrace_3119755
  have hstable : (prefixWord ++ tailWord_3119755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119755).length < 2 ^ (prefixWord ++ tailWord_3119755).sum := by decide
  have hdescent : baseEnd_3119755 < baseStart_3119755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119774 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3119774 : Nat := 118140960795 + 3119774 * 2 ^ 59
def prefixEnd_3119774 : Nat := 4983230072969 + 3 ^ 40 * 3119774 * 2
def baseEnd_3119774 : Nat := 1067962396933321402384951

theorem tailTrace_3119774 : CollatzResearch.WordTrace tailWord_3119774 prefixEnd_3119774 1067962396933321402384951 := by
  unfold tailWord_3119774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223438224949885978092797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75858337199732725216494917 14223438224949885978092797)
  ·
    refine ⟨5333789334356207241784799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14223438224949885978092797 5333789334356207241784799)
    ·
      refine ⟨8000684001534310862677199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333789334356207241784799 8000684001534310862677199)
      ·
        refine ⟨12001026002301466294015799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000684001534310862677199 12001026002301466294015799)
        ·
          refine ⟨18001539003452199441023699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12001026002301466294015799 18001539003452199441023699)
          ·
            refine ⟨27002308505178299161535549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18001539003452199441023699 27002308505178299161535549)
            ·
              refine ⟨10125865689441862185575831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27002308505178299161535549 10125865689441862185575831)
              ·
                refine ⟨15188798534162793278363747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10125865689441862185575831 15188798534162793278363747)
                ·
                  refine ⟨22783197801244189917545621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15188798534162793278363747 22783197801244189917545621)
                  ·
                    refine ⟨1067962396933321402384951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22783197801244189917545621 1067962396933321402384951)
                    ·
                      rfl

theorem cell22_3119774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3119774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119774 prefixEnd_3119774 := by exact prefixLift 3119774
  have htrace : WordTrace (prefixWord ++ tailWord_3119774) baseStart_3119774 baseEnd_3119774 := by
    simpa [prefixWord, tailWord_3119774, baseEnd_3119774] using wordTrace_append hprefix tailTrace_3119774
  have hstable : (prefixWord ++ tailWord_3119774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119774).length < 2 ^ (prefixWord ++ tailWord_3119774).sum := by decide
  have hdescent : baseEnd_3119774 < baseStart_3119774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119877 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_3119877 : Nat := 118140960795 + 3119877 * 2 ^ 59
def prefixEnd_3119877 : Nat := 4983230072969 + 3 ^ 40 * 3119877 * 2
def baseEnd_3119877 : Nat := 1067997655938263467059635

theorem tailTrace_3119877 : CollatzResearch.WordTrace tailWord_3119877 prefixEnd_3119877 1067997655938263467059635 := by
  unfold tailWord_3119877
  simp only [CollatzResearch.WordTrace]
  refine ⟨113791262518225936415741885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75860841678817290943827923 113791262518225936415741885)
  ·
    refine ⟨42671723444334726155903207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113791262518225936415741885 42671723444334726155903207)
    ·
      refine ⟨64007585166502089233854811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42671723444334726155903207 64007585166502089233854811)
      ·
        refine ⟨96011377749753133850782217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64007585166502089233854811 96011377749753133850782217)
        ·
          refine ⟨72008533312314850388086663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96011377749753133850782217 72008533312314850388086663)
          ·
            refine ⟨108012799968472275582129995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72008533312314850388086663 108012799968472275582129995)
            ·
              refine ⟨162019199952708413373194993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108012799968472275582129995 162019199952708413373194993)
              ·
                refine ⟨121514399964531310029896245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162019199952708413373194993 121514399964531310029896245)
                ·
                  refine ⟨11391974996674810315302773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121514399964531310029896245 11391974996674810315302773)
                  ·
                    refine ⟨1067997655938263467059635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11391974996674810315302773 1067997655938263467059635)
                    ·
                      rfl

theorem cell22_3119877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_3119877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119877 prefixEnd_3119877 := by exact prefixLift 3119877
  have htrace : WordTrace (prefixWord ++ tailWord_3119877) baseStart_3119877 baseEnd_3119877 := by
    simpa [prefixWord, tailWord_3119877, baseEnd_3119877] using wordTrace_append hprefix tailTrace_3119877
  have hstable : (prefixWord ++ tailWord_3119877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119877).length < 2 ^ (prefixWord ++ tailWord_3119877).sum := by decide
  have hdescent : baseEnd_3119877 < baseStart_3119877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119909 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_3119909 : Nat := 118140960795 + 3119909 * 2 ^ 59
def prefixEnd_3119909 : Nat := 4983230072969 + 3 ^ 40 * 3119909 * 2
def baseEnd_3119909 : Nat := 1068008610192226050259537

theorem tailTrace_3119909 : CollatzResearch.WordTrace tailWord_3119909 prefixEnd_3119909 1068008610192226050259537 := by
  unfold tailWord_3119909
  simp only [CollatzResearch.WordTrace]
  refine ⟨113792429654110005880906781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75861619769406670587271187 113792429654110005880906781)
  ·
    refine ⟨42672161120291252205340043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113792429654110005880906781 42672161120291252205340043)
    ·
      refine ⟨64008241680436878308010065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42672161120291252205340043 64008241680436878308010065)
      ·
        refine ⟨48006181260327658731007549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64008241680436878308010065 48006181260327658731007549)
        ·
          refine ⟨18002317972622872024127831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48006181260327658731007549 18002317972622872024127831)
          ·
            refine ⟨27003476958934308036191747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18002317972622872024127831 27003476958934308036191747)
            ·
              refine ⟨40505215438401462054287621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27003476958934308036191747 40505215438401462054287621)
              ·
                refine ⟨7594727894700274135178929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40505215438401462054287621 7594727894700274135178929)
                ·
                  refine ⟨5696045921025205601384197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7594727894700274135178929 5696045921025205601384197)
                  ·
                    refine ⟨1068008610192226050259537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696045921025205601384197 1068008610192226050259537)
                    ·
                      rfl

theorem cell22_3119909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_3119909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119909 prefixEnd_3119909 := by exact prefixLift 3119909
  have htrace : WordTrace (prefixWord ++ tailWord_3119909) baseStart_3119909 baseEnd_3119909 := by
    simpa [prefixWord, tailWord_3119909, baseEnd_3119909] using wordTrace_append hprefix tailTrace_3119909
  have hstable : (prefixWord ++ tailWord_3119909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119909).length < 2 ^ (prefixWord ++ tailWord_3119909).sum := by decide
  have hdescent : baseEnd_3119909 < baseStart_3119909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119969 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 5]
def baseStart_3119969 : Nat := 118140960795 + 3119969 * 2 ^ 59
def prefixEnd_3119969 : Nat := 4983230072969 + 3 ^ 40 * 3119969 * 2
def baseEnd_3119969 : Nat := 356009716472801964586451

theorem tailTrace_3119969 : CollatzResearch.WordTrace tailWord_3119969 prefixEnd_3119969 356009716472801964586451 := by
  unfold tailWord_3119969
  simp only [CollatzResearch.WordTrace]
  refine ⟨113794618033892636128090961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75863078689261757418727307 113794618033892636128090961)
  ·
    refine ⟨85345963525419477096068221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113794618033892636128090961 85345963525419477096068221)
    ·
      refine ⟨32004736322032303911025583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85345963525419477096068221 32004736322032303911025583)
      ·
        refine ⟨48007104483048455866538375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32004736322032303911025583 48007104483048455866538375)
        ·
          refine ⟨72010656724572683799807563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48007104483048455866538375 72010656724572683799807563)
          ·
            refine ⟨108015985086859025699711345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72010656724572683799807563 108015985086859025699711345)
            ·
              refine ⟨81011988815144269274783509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108015985086859025699711345 81011988815144269274783509)
              ·
                refine ⟨3797436975709887622255477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81011988815144269274783509 3797436975709887622255477)
                ·
                  refine ⟨356009716472801964586451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3797436975709887622255477 356009716472801964586451)
                  ·
                    rfl

theorem cell22_3119969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_3119969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119969 prefixEnd_3119969 := by exact prefixLift 3119969
  have htrace : WordTrace (prefixWord ++ tailWord_3119969) baseStart_3119969 baseEnd_3119969 := by
    simpa [prefixWord, tailWord_3119969, baseEnd_3119969] using wordTrace_append hprefix tailTrace_3119969
  have hstable : (prefixWord ++ tailWord_3119969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119969).length < 2 ^ (prefixWord ++ tailWord_3119969).sum := by decide
  have hdescent : baseEnd_3119969 < baseStart_3119969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119973 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_3119973 : Nat := 118140960795 + 3119973 * 2 ^ 59
def prefixEnd_3119973 : Nat := 4983230072969 + 3 ^ 40 * 3119973 * 2
def baseEnd_3119973 : Nat := 1068030518700151216659341

theorem tailTrace_3119973 : CollatzResearch.WordTrace tailWord_3119973 prefixEnd_3119973 1068030518700151216659341 := by
  unfold tailWord_3119973
  simp only [CollatzResearch.WordTrace]
  refine ⟨113794763925878144811236573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75863175950585429874157715 113794763925878144811236573)
  ·
    refine ⟨42673036472204304304213715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113794763925878144811236573 42673036472204304304213715)
    ·
      refine ⟨64009554708306456456320573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42673036472204304304213715 64009554708306456456320573)
      ·
        refine ⟨24003583015614921171120215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64009554708306456456320573 24003583015614921171120215)
        ·
          refine ⟨36005374523422381756680323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24003583015614921171120215 36005374523422381756680323)
          ·
            refine ⟨54008061785133572635020485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36005374523422381756680323 54008061785133572635020485)
            ·
              refine ⟨10126511584712544869066341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54008061785133572635020485 10126511584712544869066341)
              ·
                refine ⟨1898720922133602162949939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10126511584712544869066341 1898720922133602162949939)
                ·
                  refine ⟨2848081383200403244424909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898720922133602162949939 2848081383200403244424909)
                  ·
                    refine ⟨1068030518700151216659341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2848081383200403244424909 1068030518700151216659341)
                    ·
                      rfl

theorem cell22_3119973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_3119973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119973 prefixEnd_3119973 := by exact prefixLift 3119973
  have htrace : WordTrace (prefixWord ++ tailWord_3119973) baseStart_3119973 baseEnd_3119973 := by
    simpa [prefixWord, tailWord_3119973, baseEnd_3119973] using wordTrace_append hprefix tailTrace_3119973
  have hstable : (prefixWord ++ tailWord_3119973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119973).length < 2 ^ (prefixWord ++ tailWord_3119973).sum := by decide
  have hdescent : baseEnd_3119973 < baseStart_3119973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119984 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_3119984 : Nat := 118140960795 + 3119984 * 2 ^ 59
def prefixEnd_3119984 : Nat := 4983230072969 + 3 ^ 40 * 3119984 * 2
def baseEnd_3119984 : Nat := 1068034284224950854634307

theorem tailTrace_3119984 : CollatzResearch.WordTrace tailWord_3119984 prefixEnd_3119984 1068034284224950854634307 := by
  unfold tailWord_3119984
  simp only [CollatzResearch.WordTrace]
  refine ⟨56897582564419146844943503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75863443419225529126591337 56897582564419146844943503)
  ·
    refine ⟨85346373846628720267415255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56897582564419146844943503 85346373846628720267415255)
    ·
      refine ⟨128019560769943080401122883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85346373846628720267415255 128019560769943080401122883)
      ·
        refine ⟨192029341154914620601684325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128019560769943080401122883 192029341154914620601684325)
        ·
          refine ⟨36005501466546491362815811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192029341154914620601684325 36005501466546491362815811)
          ·
            refine ⟨54008252199819737044223717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36005501466546491362815811 54008252199819737044223717)
            ·
              refine ⟨10126547287466200695791947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54008252199819737044223717 10126547287466200695791947)
              ·
                refine ⟨15189820931199301043687921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10126547287466200695791947 15189820931199301043687921)
                ·
                  refine ⟨11392365698399475782765941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15189820931199301043687921 11392365698399475782765941)
                  ·
                    refine ⟨1068034284224950854634307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11392365698399475782765941 1068034284224950854634307)
                    ·
                      rfl

theorem cell22_3119984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_3119984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119984 prefixEnd_3119984 := by exact prefixLift 3119984
  have htrace : WordTrace (prefixWord ++ tailWord_3119984) baseStart_3119984 baseEnd_3119984 := by
    simpa [prefixWord, tailWord_3119984, baseEnd_3119984] using wordTrace_append hprefix tailTrace_3119984
  have hstable : (prefixWord ++ tailWord_3119984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119984).length < 2 ^ (prefixWord ++ tailWord_3119984).sum := by decide
  have hdescent : baseEnd_3119984 < baseStart_3119984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3119999 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 3, 4]
def baseStart_3119999 : Nat := 118140960795 + 3119999 * 2 ^ 59
def prefixEnd_3119999 : Nat := 4983230072969 + 3 ^ 40 * 3119999 * 2
def baseEnd_3119999 : Nat := 1068039419031495815509261

theorem tailTrace_3119999 : CollatzResearch.WordTrace tailWord_3119999 prefixEnd_3119999 1068039419031495815509261 := by
  unfold tailWord_3119999
  simp only [CollatzResearch.WordTrace]
  refine ⟨113795712223783951251683051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75863808149189300834455367 113795712223783951251683051)
  ·
    refine ⟨170693568335675926877524577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113795712223783951251683051 170693568335675926877524577)
    ·
      refine ⟨128020176251756945158143433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170693568335675926877524577 128020176251756945158143433)
      ·
        refine ⟨96015132188817708868607575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128020176251756945158143433 96015132188817708868607575)
        ·
          refine ⟨144022698283226563302911363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96015132188817708868607575 144022698283226563302911363)
          ·
            refine ⟨216034047424839844954367045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144022698283226563302911363 216034047424839844954367045)
            ·
              refine ⟨40506383892157470928943821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216034047424839844954367045 40506383892157470928943821)
              ·
                refine ⟨15189893959559051598353933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40506383892157470928943821 15189893959559051598353933)
                ·
                  refine ⟨5696210234834644349382725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15189893959559051598353933 5696210234834644349382725)
                  ·
                    refine ⟨1068039419031495815509261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696210234834644349382725 1068039419031495815509261)
                    ·
                      rfl

theorem cell22_3119999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_3119999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3119999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3119999 prefixEnd_3119999 := by exact prefixLift 3119999
  have htrace : WordTrace (prefixWord ++ tailWord_3119999) baseStart_3119999 baseEnd_3119999 := by
    simpa [prefixWord, tailWord_3119999, baseEnd_3119999] using wordTrace_append hprefix tailTrace_3119999
  have hstable : (prefixWord ++ tailWord_3119999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3119999).length < 2 ^ (prefixWord ++ tailWord_3119999).sum := by decide
  have hdescent : baseEnd_3119999 < baseStart_3119999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3119999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120031 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 6]
def baseStart_3120031 : Nat := 118140960795 + 3120031 * 2 ^ 59
def prefixEnd_3120031 : Nat := 4983230072969 + 3 ^ 40 * 3120031 * 2
def baseEnd_3120031 : Nat := 356016791095152799569721

theorem tailTrace_3120031 : CollatzResearch.WordTrace tailWord_3120031 prefixEnd_3120031 356016791095152799569721 := by
  unfold tailWord_3120031
  simp only [CollatzResearch.WordTrace]
  refine ⟨113796879359668020716847947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75864586239778680477898631 113796879359668020716847947)
  ·
    refine ⟨170695319039502031075271921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113796879359668020716847947 170695319039502031075271921)
    ·
      refine ⟨128021489279626523306453941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170695319039502031075271921 128021489279626523306453941)
      ·
        refine ⟨12002014619964986559980057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128021489279626523306453941 12002014619964986559980057)
        ·
          refine ⟨9001510964973739919985043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12002014619964986559980057 9001510964973739919985043)
          ·
            refine ⟨13502266447460609879977565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9001510964973739919985043 13502266447460609879977565)
            ·
              refine ⟨5063349917797728704991587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13502266447460609879977565 5063349917797728704991587)
              ·
                refine ⟨7595024876696593057487381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5063349917797728704991587 7595024876696593057487381)
                ·
                  refine ⟨356016791095152799569721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7595024876696593057487381 356016791095152799569721)
                  ·
                    rfl

theorem cell22_3120031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 6].length) (baseStart_3120031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120031 prefixEnd_3120031 := by exact prefixLift 3120031
  have htrace : WordTrace (prefixWord ++ tailWord_3120031) baseStart_3120031 baseEnd_3120031 := by
    simpa [prefixWord, tailWord_3120031, baseEnd_3120031] using wordTrace_append hprefix tailTrace_3120031
  have hstable : (prefixWord ++ tailWord_3120031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120031).length < 2 ^ (prefixWord ++ tailWord_3120031).sum := by decide
  have hdescent : baseEnd_3120031 < baseStart_3120031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120082 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3120082 : Nat := 118140960795 + 3120082 * 2 ^ 59
def prefixEnd_3120082 : Nat := 4983230072969 + 3 ^ 40 * 3120082 * 2
def baseEnd_3120082 : Nat := 356022610542570421894669

theorem tailTrace_3120082 : CollatzResearch.WordTrace tailWord_3120082 prefixEnd_3120082 356022610542570421894669 := by
  unfold tailWord_3120082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28449684870620814106738625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75865826321655504284636333 28449684870620814106738625)
  ·
    refine ⟨21337263652965610580053969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28449684870620814106738625 21337263652965610580053969)
    ·
      refine ⟨16002947739724207935040477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21337263652965610580053969 16002947739724207935040477)
      ·
        refine ⟨6001105402396577975640179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16002947739724207935040477 6001105402396577975640179)
        ·
          refine ⟨9001658103594866963460269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6001105402396577975640179 9001658103594866963460269)
          ·
            refine ⟨3375621788848075111297601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9001658103594866963460269 3375621788848075111297601)
            ·
              refine ⟨2531716341636056333473201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375621788848075111297601 2531716341636056333473201)
              ·
                refine ⟨1898787256227042250104901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531716341636056333473201 1898787256227042250104901)
                ·
                  refine ⟨356022610542570421894669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898787256227042250104901 356022610542570421894669)
                  ·
                    rfl

theorem cell22_3120082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3120082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120082 prefixEnd_3120082 := by exact prefixLift 3120082
  have htrace : WordTrace (prefixWord ++ tailWord_3120082) baseStart_3120082 baseEnd_3120082 := by
    simpa [prefixWord, tailWord_3120082, baseEnd_3120082] using wordTrace_append hprefix tailTrace_3120082
  have hstable : (prefixWord ++ tailWord_3120082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120082).length < 2 ^ (prefixWord ++ tailWord_3120082).sum := by decide
  have hdescent : baseEnd_3120082 < baseStart_3120082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120093 : List Nat := [1, 4, 3, 1, 2, 3, 1, 7]
def baseStart_3120093 : Nat := 118140960795 + 3120093 * 2 ^ 59
def prefixEnd_3120093 : Nat := 4983230072969 + 3 ^ 40 * 3120093 * 2
def baseEnd_3120093 : Nat := 118674621905834544850997

theorem tailTrace_3120093 : CollatzResearch.WordTrace tailWord_3120093 prefixEnd_3120093 118674621905834544850997 := by
  unfold tailWord_3120093
  simp only [CollatzResearch.WordTrace]
  refine ⟨113799140685443405305604933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75866093790295603537069955 113799140685443405305604933)
  ·
    refine ⟨21337338878520638494800925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113799140685443405305604933 21337338878520638494800925)
    ·
      refine ⟨8001502079445239435550347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21337338878520638494800925 8001502079445239435550347)
      ·
        refine ⟨12002253119167859153325521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001502079445239435550347 12002253119167859153325521)
        ·
          refine ⟨9001689839375894364994141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12002253119167859153325521 9001689839375894364994141)
          ·
            refine ⟨3375633689765960386872803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9001689839375894364994141 3375633689765960386872803)
            ·
              refine ⟨5063450534648940580309205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375633689765960386872803 5063450534648940580309205)
              ·
                refine ⟨118674621905834544850997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5063450534648940580309205 118674621905834544850997)
                ·
                  rfl

theorem cell22_3120093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 7].length) (baseStart_3120093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120093 prefixEnd_3120093 := by exact prefixLift 3120093
  have htrace : WordTrace (prefixWord ++ tailWord_3120093) baseStart_3120093 baseEnd_3120093 := by
    simpa [prefixWord, tailWord_3120093, baseEnd_3120093] using wordTrace_append hprefix tailTrace_3120093
  have hstable : (prefixWord ++ tailWord_3120093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120093).length < 2 ^ (prefixWord ++ tailWord_3120093).sum := by decide
  have hdescent : baseEnd_3120093 < baseStart_3120093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120116 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3120116 : Nat := 118140960795 + 3120116 * 2 ^ 59
def prefixEnd_3120116 : Nat := 4983230072969 + 3 ^ 40 * 3120116 * 2
def baseEnd_3120116 : Nat := 356026490174182170111301

theorem tailTrace_3120116 : CollatzResearch.WordTrace tailWord_3120116 prefixEnd_3120116 356026490174182170111301 := by
  unfold tailWord_3120116
  simp only [CollatzResearch.WordTrace]
  refine ⟨56899989782180040116846101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75866653042906720155794801 56899989782180040116846101)
  ·
    refine ⟨2667187021039689380477161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56899989782180040116846101 2667187021039689380477161)
    ·
      refine ⟨2000390265779767035357871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2667187021039689380477161 2000390265779767035357871)
      ·
        refine ⟨3000585398669650553036807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000390265779767035357871 3000585398669650553036807)
        ·
          refine ⟨4500878098004475829555211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000585398669650553036807 4500878098004475829555211)
          ·
            refine ⟨6751317147006713744332817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500878098004475829555211 6751317147006713744332817)
            ·
              refine ⟨5063487860255035308249613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6751317147006713744332817 5063487860255035308249613)
              ·
                refine ⟨1898807947595638240593605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063487860255035308249613 1898807947595638240593605)
                ·
                  refine ⟨356026490174182170111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898807947595638240593605 356026490174182170111301)
                  ·
                    rfl

theorem cell22_3120116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3120116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120116 prefixEnd_3120116 := by exact prefixLift 3120116
  have htrace : WordTrace (prefixWord ++ tailWord_3120116) baseStart_3120116 baseEnd_3120116 := by
    simpa [prefixWord, tailWord_3120116, baseEnd_3120116] using wordTrace_append hprefix tailTrace_3120116
  have hstable : (prefixWord ++ tailWord_3120116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120116).length < 2 ^ (prefixWord ++ tailWord_3120116).sum := by decide
  have hdescent : baseEnd_3120116 < baseStart_3120116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120136 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3120136 : Nat := 118140960795 + 3120136 * 2 ^ 59
def prefixEnd_3120136 : Nat := 4983230072969 + 3 ^ 40 * 3120136 * 2
def baseEnd_3120136 : Nat := 1068086316931273124833841

theorem tailTrace_3120136 : CollatzResearch.WordTrace tailWord_3120136 prefixEnd_3120136 1068086316931273124833841 := by
  unfold tailWord_3120136
  simp only [CollatzResearch.WordTrace]
  refine ⟨56900354512143811824710131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75867139349525082432946841 56900354512143811824710131)
  ·
    refine ⟨85350531768215717737065197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56900354512143811824710131 85350531768215717737065197)
    ·
      refine ⟨32006449413080894151399449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85350531768215717737065197 32006449413080894151399449)
      ·
        refine ⟨24004837059810670613549587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32006449413080894151399449 24004837059810670613549587)
        ·
          refine ⟨36007255589716005920324381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24004837059810670613549587 36007255589716005920324381)
          ·
            refine ⟨13502720846143502220121643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36007255589716005920324381 13502720846143502220121643)
            ·
              refine ⟨20254081269215253330182465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13502720846143502220121643 20254081269215253330182465)
              ·
                refine ⟨15190560951911439997636849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20254081269215253330182465 15190560951911439997636849)
                ·
                  refine ⟨11392920713933579998227637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15190560951911439997636849 11392920713933579998227637)
                  ·
                    refine ⟨1068086316931273124833841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11392920713933579998227637 1068086316931273124833841)
                    ·
                      rfl

theorem cell22_3120136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3120136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120136 prefixEnd_3120136 := by exact prefixLift 3120136
  have htrace : WordTrace (prefixWord ++ tailWord_3120136) baseStart_3120136 baseEnd_3120136 := by
    simpa [prefixWord, tailWord_3120136, baseEnd_3120136] using wordTrace_append hprefix tailTrace_3120136
  have hstable : (prefixWord ++ tailWord_3120136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120136).length < 2 ^ (prefixWord ++ tailWord_3120136).sum := by decide
  have hdescent : baseEnd_3120136 < baseStart_3120136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120138 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_3120138 : Nat := 118140960795 + 3120138 * 2 ^ 59
def prefixEnd_3120138 : Nat := 4983230072969 + 3 ^ 40 * 3120138 * 2
def baseEnd_3120138 : Nat := 356029000524048595427945

theorem tailTrace_3120138 : CollatzResearch.WordTrace tailWord_3120138 prefixEnd_3120138 356029000524048595427945 := by
  unfold tailWord_3120138
  simp only [CollatzResearch.WordTrace]
  refine ⟨28450195492570094497748267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75867187980186918660662045 28450195492570094497748267)
  ·
    refine ⟨42675293238855141746622401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28450195492570094497748267 42675293238855141746622401)
    ·
      refine ⟨32006469929141356309966801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42675293238855141746622401 32006469929141356309966801)
      ·
        refine ⟨24004852446856017232475101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32006469929141356309966801 24004852446856017232475101)
        ·
          refine ⟨9001819667571006462178163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24004852446856017232475101 9001819667571006462178163)
          ·
            refine ⟨13502729501356509693267245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9001819667571006462178163 13502729501356509693267245)
            ·
              refine ⟨5063523563008691134975217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13502729501356509693267245 5063523563008691134975217)
              ·
                refine ⟨3797642672256518351231413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5063523563008691134975217 3797642672256518351231413)
                ·
                  refine ⟨356029000524048595427945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3797642672256518351231413 356029000524048595427945)
                  ·
                    rfl

theorem cell22_3120138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_3120138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120138 prefixEnd_3120138 := by exact prefixLift 3120138
  have htrace : WordTrace (prefixWord ++ tailWord_3120138) baseStart_3120138 baseEnd_3120138 := by
    simpa [prefixWord, tailWord_3120138, baseEnd_3120138] using wordTrace_append hprefix tailTrace_3120138
  have hstable : (prefixWord ++ tailWord_3120138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120138).length < 2 ^ (prefixWord ++ tailWord_3120138).sum := by decide
  have hdescent : baseEnd_3120138 < baseStart_3120138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120181 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3120181 : Nat := 118140960795 + 3120181 * 2 ^ 59
def prefixEnd_3120181 : Nat := 4983230072969 + 3 ^ 40 * 3120181 * 2
def baseEnd_3120181 : Nat := 1068101721350908007458703

theorem tailTrace_3120181 : CollatzResearch.WordTrace tailWord_3120181 prefixEnd_3120181 1068101721350908007458703 := by
  unfold tailWord_3120181
  simp only [CollatzResearch.WordTrace]
  refine ⟨113802350309124596334808397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75868233539416397556538931 113802350309124596334808397)
  ·
    refine ⟨42675881365921723625553149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113802350309124596334808397 42675881365921723625553149)
    ·
      refine ⟨16003455512220646359582431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42675881365921723625553149 16003455512220646359582431)
      ·
        refine ⟨24005183268330969539373647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16003455512220646359582431 24005183268330969539373647)
        ·
          refine ⟨36007774902496454309060471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24005183268330969539373647 36007774902496454309060471)
          ·
            refine ⟨54011662353744681463590707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36007774902496454309060471 54011662353744681463590707)
            ·
              refine ⟨81017493530617022195386061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54011662353744681463590707 81017493530617022195386061)
              ·
                refine ⟨30381560073981383323269773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81017493530617022195386061 30381560073981383323269773)
                ·
                  refine ⟨11393085027743018746226165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30381560073981383323269773 11393085027743018746226165)
                  ·
                    refine ⟨1068101721350908007458703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11393085027743018746226165 1068101721350908007458703)
                    ·
                      rfl

theorem cell22_3120181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3120181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120181 prefixEnd_3120181 := by exact prefixLift 3120181
  have htrace : WordTrace (prefixWord ++ tailWord_3120181) baseStart_3120181 baseEnd_3120181 := by
    simpa [prefixWord, tailWord_3120181, baseEnd_3120181] using wordTrace_append hprefix tailTrace_3120181
  have hstable : (prefixWord ++ tailWord_3120181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120181).length < 2 ^ (prefixWord ++ tailWord_3120181).sum := by decide
  have hdescent : baseEnd_3120181 < baseStart_3120181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120200 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 4]
def baseStart_3120200 : Nat := 118140960795 + 3120200 * 2 ^ 59
def prefixEnd_3120200 : Nat := 4983230072969 + 3 ^ 40 * 3120200 * 2
def baseEnd_3120200 : Nat := 356036075146399430411215

theorem tailTrace_3120200 : CollatzResearch.WordTrace tailWord_3120200 prefixEnd_3120200 356036075146399430411215 := by
  unfold tailWord_3120200
  simp only [CollatzResearch.WordTrace]
  refine ⟨56901521648027881289875027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75868695530703841719833369 56901521648027881289875027)
  ·
    refine ⟨85352282472041821934812541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56901521648027881289875027 85352282472041821934812541)
    ·
      refine ⟨32007105927015683225554703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85352282472041821934812541 32007105927015683225554703)
      ·
        refine ⟨48010658890523524838332055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32007105927015683225554703 48010658890523524838332055)
        ·
          refine ⟨72015988335785287257498083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48010658890523524838332055 72015988335785287257498083)
          ·
            refine ⟨108023982503677930886247125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72015988335785287257498083 108023982503677930886247125)
            ·
              refine ⟨2531812089929951505146417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 108023982503677930886247125 2531812089929951505146417)
              ·
                refine ⟨1898859067447463628859813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2531812089929951505146417 1898859067447463628859813)
                ·
                  refine ⟨356036075146399430411215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898859067447463628859813 356036075146399430411215)
                  ·
                    rfl

theorem cell22_3120200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_3120200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120200 prefixEnd_3120200 := by exact prefixLift 3120200
  have htrace : WordTrace (prefixWord ++ tailWord_3120200) baseStart_3120200 baseEnd_3120200 := by
    simpa [prefixWord, tailWord_3120200, baseEnd_3120200] using wordTrace_append hprefix tailTrace_3120200
  have hstable : (prefixWord ++ tailWord_3120200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120200).length < 2 ^ (prefixWord ++ tailWord_3120200).sum := by decide
  have hdescent : baseEnd_3120200 < baseStart_3120200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120245 : List Nat := [1, 3, 4, 3, 2, 9]
def baseStart_3120245 : Nat := 118140960795 + 3120245 * 2 ^ 59
def prefixEnd_3120245 : Nat := 4983230072969 + 3 ^ 40 * 3120245 * 2
def baseEnd_3120245 : Nat := 13186711479738681158747

theorem tailTrace_3120245 : CollatzResearch.WordTrace tailWord_3120245 prefixEnd_3120245 13186711479738681158747 := by
  unfold tailWord_3120245
  simp only [CollatzResearch.WordTrace]
  refine ⟨113804684580892735265138189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75869789720595156843425459 113804684580892735265138189)
  ·
    refine ⟨42676756717834775724426821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113804684580892735265138189 42676756717834775724426821)
    ·
      refine ⟨8001891884594020448330029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42676756717834775724426821 8001891884594020448330029)
      ·
        refine ⟨3000709456722757668123761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8001891884594020448330029 3000709456722757668123761)
        ·
          refine ⟨2250532092542068251092821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000709456722757668123761 2250532092542068251092821)
          ·
            refine ⟨13186711479738681158747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2250532092542068251092821 13186711479738681158747)
            ·
              rfl

theorem cell22_3120245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 9].length) (baseStart_3120245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120245 prefixEnd_3120245 := by exact prefixLift 3120245
  have htrace : WordTrace (prefixWord ++ tailWord_3120245) baseStart_3120245 baseEnd_3120245 := by
    simpa [prefixWord, tailWord_3120245, baseEnd_3120245] using wordTrace_append hprefix tailTrace_3120245
  have hstable : (prefixWord ++ tailWord_3120245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120245).length < 2 ^ (prefixWord ++ tailWord_3120245).sum := by decide
  have hdescent : baseEnd_3120245 < baseStart_3120245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120256 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_3120256 : Nat := 118140960795 + 3120256 * 2 ^ 59
def prefixEnd_3120256 : Nat := 4983230072969 + 3 ^ 40 * 3120256 * 2
def baseEnd_3120256 : Nat := 356042465127877603944491

theorem tailTrace_3120256 : CollatzResearch.WordTrace tailWord_3120256 prefixEnd_3120256 356042465127877603944491 := by
  unfold tailWord_3120256
  simp only [CollatzResearch.WordTrace]
  refine ⟨56902542891926442071894311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75870057189235256095859081 56902542891926442071894311)
  ·
    refine ⟨85353814337889663107841467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56902542891926442071894311 85353814337889663107841467)
    ·
      refine ⟨128030721506834494661762201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85353814337889663107841467 128030721506834494661762201)
      ·
        refine ⟨96023041130125870996321651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128030721506834494661762201 96023041130125870996321651)
        ·
          refine ⟨144034561695188806494482477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96023041130125870996321651 144034561695188806494482477)
          ·
            refine ⟨54012960635695802435430929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144034561695188806494482477 54012960635695802435430929)
            ·
              refine ⟨40509720476771851826573197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54012960635695802435430929 40509720476771851826573197)
              ·
                refine ⟨15191145178789444434964949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40509720476771851826573197 15191145178789444434964949)
                ·
                  refine ⟨356042465127877603944491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15191145178789444434964949 356042465127877603944491)
                  ·
                    rfl

theorem cell22_3120256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_3120256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120256 prefixEnd_3120256 := by exact prefixLift 3120256
  have htrace : WordTrace (prefixWord ++ tailWord_3120256) baseStart_3120256 baseEnd_3120256 := by
    simpa [prefixWord, tailWord_3120256, baseEnd_3120256] using wordTrace_append hprefix tailTrace_3120256
  have hstable : (prefixWord ++ tailWord_3120256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120256).length < 2 ^ (prefixWord ++ tailWord_3120256).sum := by decide
  have hdescent : baseEnd_3120256 < baseStart_3120256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120352 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 4]
def baseStart_3120352 : Nat := 118140960795 + 3120352 * 2 ^ 59
def prefixEnd_3120352 : Nat := 4983230072969 + 3 ^ 40 * 3120352 * 2
def baseEnd_3120352 : Nat := 356053419381840187144393

theorem tailTrace_3120352 : CollatzResearch.WordTrace tailWord_3120352 prefixEnd_3120352 356053419381840187144393 := by
  unfold tailWord_3120352
  simp only [CollatzResearch.WordTrace]
  refine ⟨56904293595752546269641655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75872391461003395026188873 56904293595752546269641655)
  ·
    refine ⟨85356440393628819404462483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56904293595752546269641655 85356440393628819404462483)
    ·
      refine ⟨128034660590443229106693725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85356440393628819404462483 128034660590443229106693725)
      ·
        refine ⟨48012997721416210915010147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128034660590443229106693725 48012997721416210915010147)
        ·
          refine ⟨72019496582124316372515221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48012997721416210915010147 72019496582124316372515221)
          ·
            refine ⟨3375913902287077329961651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72019496582124316372515221 3375913902287077329961651)
            ·
              refine ⟨5063870853430615994942477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375913902287077329961651 5063870853430615994942477)
              ·
                refine ⟨1898951570036480998103429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063870853430615994942477 1898951570036480998103429)
                ·
                  refine ⟨356053419381840187144393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1898951570036480998103429 356053419381840187144393)
                  ·
                    rfl

theorem cell22_3120352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_3120352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120352 prefixEnd_3120352 := by exact prefixLift 3120352
  have htrace : WordTrace (prefixWord ++ tailWord_3120352) baseStart_3120352 baseEnd_3120352 := by
    simpa [prefixWord, tailWord_3120352, baseEnd_3120352] using wordTrace_append hprefix tailTrace_3120352
  have hstable : (prefixWord ++ tailWord_3120352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120352).length < 2 ^ (prefixWord ++ tailWord_3120352).sum := by decide
  have hdescent : baseEnd_3120352 < baseStart_3120352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120363 : List Nat := [1, 1, 1, 1, 2, 8, 8]
def baseStart_3120363 : Nat := 118140960795 + 3120363 * 2 ^ 59
def prefixEnd_3120363 : Nat := 4983230072969 + 3 ^ 40 * 3120363 * 2
def baseEnd_3120363 : Nat := 39561630506308155533635

theorem tailTrace_3120363 : CollatzResearch.WordTrace tailWord_3120363 prefixEnd_3120363 39561630506308155533635 := by
  unfold tailWord_3120363
  simp only [CollatzResearch.WordTrace]
  refine ⟨113808988394465241417933743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75872658929643494278622495 113808988394465241417933743)
  ·
    refine ⟨170713482591697862126900615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113808988394465241417933743 170713482591697862126900615)
    ·
      refine ⟨256070223887546793190350923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170713482591697862126900615 256070223887546793190350923)
      ·
        refine ⟨384105335831320189785526385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256070223887546793190350923 384105335831320189785526385)
        ·
          refine ⟨288079001873490142339144789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384105335831320189785526385 288079001873490142339144789)
          ·
            refine ⟨3375925803204962605536853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 288079001873490142339144789 3375925803204962605536853)
            ·
              refine ⟨39561630506308155533635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3375925803204962605536853 39561630506308155533635)
              ·
                rfl

theorem cell22_3120363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 8].length) (baseStart_3120363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120363 prefixEnd_3120363 := by exact prefixLift 3120363
  have htrace : WordTrace (prefixWord ++ tailWord_3120363) baseStart_3120363 baseEnd_3120363 := by
    simpa [prefixWord, tailWord_3120363, baseEnd_3120363] using wordTrace_append hprefix tailTrace_3120363
  have hstable : (prefixWord ++ tailWord_3120363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120363).length < 2 ^ (prefixWord ++ tailWord_3120363).sum := by decide
  have hdescent : baseEnd_3120363 < baseStart_3120363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120365 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3120365 : Nat := 118140960795 + 3120365 * 2 ^ 59
def prefixEnd_3120365 : Nat := 4983230072969 + 3 ^ 40 * 3120365 * 2
def baseEnd_3120365 : Nat := 1068164708311192860858139

theorem tailTrace_3120365 : CollatzResearch.WordTrace tailWord_3120365 prefixEnd_3120365 1068164708311192860858139 := by
  unfold tailWord_3120365
  simp only [CollatzResearch.WordTrace]
  refine ⟨113809061340457995759506549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75872707560305330506337699 113809061340457995759506549)
  ·
    refine ⟨10669599500667937102453739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113809061340457995759506549 10669599500667937102453739)
    ·
      refine ⟨16004399251001905653680609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10669599500667937102453739 16004399251001905653680609)
      ·
        refine ⟨12003299438251429240260457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16004399251001905653680609 12003299438251429240260457)
        ·
          refine ⟨9002474578688571930195343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12003299438251429240260457 9002474578688571930195343)
          ·
            refine ⟨13503711868032857895293015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002474578688571930195343 13503711868032857895293015)
            ·
              refine ⟨20255567802049286842939523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13503711868032857895293015 20255567802049286842939523)
              ·
                refine ⟨30383351703073930264409285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20255567802049286842939523 30383351703073930264409285)
                ·
                  refine ⟨5696878444326361924576741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30383351703073930264409285 5696878444326361924576741)
                  ·
                    refine ⟨1068164708311192860858139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696878444326361924576741 1068164708311192860858139)
                    ·
                      rfl

theorem cell22_3120365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3120365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120365 prefixEnd_3120365 := by exact prefixLift 3120365
  have htrace : WordTrace (prefixWord ++ tailWord_3120365) baseStart_3120365 baseEnd_3120365 := by
    simpa [prefixWord, tailWord_3120365, baseEnd_3120365] using wordTrace_append hprefix tailTrace_3120365
  have hstable : (prefixWord ++ tailWord_3120365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120365).length < 2 ^ (prefixWord ++ tailWord_3120365).sum := by decide
  have hdescent : baseEnd_3120365 < baseStart_3120365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120380 : List Nat := [2, 2, 2, 1, 5, 1, 2, 7]
def baseStart_3120380 : Nat := 118140960795 + 3120380 * 2 ^ 59
def prefixEnd_3120380 : Nat := 4983230072969 + 3 ^ 40 * 3120380 * 2
def baseEnd_3120380 : Nat := 118685538124193091303677

theorem tailTrace_3120380 : CollatzResearch.WordTrace tailWord_3120380 prefixEnd_3120380 118685538124193091303677 := by
  unfold tailWord_3120380
  simp only [CollatzResearch.WordTrace]
  refine ⟨56904804217701826660651297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75873072290269102214201729 56904804217701826660651297)
  ·
    refine ⟨42678603163276369995488473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56904804217701826660651297 42678603163276369995488473)
    ·
      refine ⟨32008952372457277496616355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42678603163276369995488473 32008952372457277496616355)
      ·
        refine ⟨48013428558685916244924533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32008952372457277496616355 48013428558685916244924533)
        ·
          refine ⟨4501258927376804647961675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48013428558685916244924533 4501258927376804647961675)
          ·
            refine ⟨6751888391065206971942513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501258927376804647961675 6751888391065206971942513)
            ·
              refine ⟨5063916293298905228956885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6751888391065206971942513 5063916293298905228956885)
              ·
                refine ⟨118685538124193091303677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5063916293298905228956885 118685538124193091303677)
                ·
                  rfl

theorem cell22_3120380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_3120380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120380 prefixEnd_3120380 := by exact prefixLift 3120380
  have htrace : WordTrace (prefixWord ++ tailWord_3120380) baseStart_3120380 baseEnd_3120380 := by
    simpa [prefixWord, tailWord_3120380, baseEnd_3120380] using wordTrace_append hprefix tailTrace_3120380
  have hstable : (prefixWord ++ tailWord_3120380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120380).length < 2 ^ (prefixWord ++ tailWord_3120380).sum := by decide
  have hdescent : baseEnd_3120380 < baseStart_3120380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120455 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3120455 : Nat := 118140960795 + 3120455 * 2 ^ 59
def prefixEnd_3120455 : Nat := 4983230072969 + 3 ^ 40 * 3120455 * 2
def baseEnd_3120455 : Nat := 1068195517150462626107863

theorem tailTrace_3120455 : CollatzResearch.WordTrace tailWord_3120455 prefixEnd_3120455 1068195517150462626107863 := by
  unfold tailWord_3120455
  simp only [CollatzResearch.WordTrace]
  refine ⟨113812343910131941130282819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75874895940087960753521879 113812343910131941130282819)
  ·
    refine ⟨170718515865197911695424229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113812343910131941130282819 170718515865197911695424229)
    ·
      refine ⟨32009721724724608442892043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170718515865197911695424229 32009721724724608442892043)
      ·
        refine ⟨48014582587086912664338065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32009721724724608442892043 48014582587086912664338065)
        ·
          refine ⟨36010936940315184498253549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48014582587086912664338065 36010936940315184498253549)
          ·
            refine ⟨13504101352618194186845081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36010936940315184498253549 13504101352618194186845081)
            ·
              refine ⟨10128076014463645640133811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13504101352618194186845081 10128076014463645640133811)
              ·
                refine ⟨15192114021695468460200717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10128076014463645640133811 15192114021695468460200717)
                ·
                  refine ⟨5697042758135800672575269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15192114021695468460200717 5697042758135800672575269)
                  ·
                    refine ⟨1068195517150462626107863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5697042758135800672575269 1068195517150462626107863)
                    ·
                      rfl

theorem cell22_3120455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3120455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120455 prefixEnd_3120455 := by exact prefixLift 3120455
  have htrace : WordTrace (prefixWord ++ tailWord_3120455) baseStart_3120455 baseEnd_3120455 := by
    simpa [prefixWord, tailWord_3120455, baseEnd_3120455] using wordTrace_append hprefix tailTrace_3120455
  have hstable : (prefixWord ++ tailWord_3120455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120455).length < 2 ^ (prefixWord ++ tailWord_3120455).sum := by decide
  have hdescent : baseEnd_3120455 < baseStart_3120455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120487 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 6]
def baseStart_3120487 : Nat := 118140960795 + 3120487 * 2 ^ 59
def prefixEnd_3120487 : Nat := 4983230072969 + 3 ^ 40 * 3120487 * 2
def baseEnd_3120487 : Nat := 356068823801475069769255

theorem tailTrace_3120487 : CollatzResearch.WordTrace tailWord_3120487 prefixEnd_3120487 356068823801475069769255 := by
  unfold tailWord_3120487
  simp only [CollatzResearch.WordTrace]
  refine ⟨113813511046016010595447715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75875674030677340396965143 113813511046016010595447715)
  ·
    refine ⟨170720266569024015893171573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113813511046016010595447715 170720266569024015893171573)
    ·
      refine ⟨16005024990846001489984835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170720266569024015893171573 16005024990846001489984835)
      ·
        refine ⟨24007537486269002234977253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16005024990846001489984835 24007537486269002234977253)
        ·
          refine ⟨4501413278675437919058235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24007537486269002234977253 4501413278675437919058235)
          ·
            refine ⟨6752119918013156878587353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4501413278675437919058235 6752119918013156878587353)
            ·
              refine ⟨5064089938509867658940515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6752119918013156878587353 5064089938509867658940515)
              ·
                refine ⟨7596134907764801488410773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064089938509867658940515 7596134907764801488410773)
                ·
                  refine ⟨356068823801475069769255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7596134907764801488410773 356068823801475069769255)
                  ·
                    rfl

theorem cell22_3120487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 6].length) (baseStart_3120487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120487 prefixEnd_3120487 := by exact prefixLift 3120487
  have htrace : WordTrace (prefixWord ++ tailWord_3120487) baseStart_3120487 baseEnd_3120487 := by
    simpa [prefixWord, tailWord_3120487, baseEnd_3120487] using wordTrace_append hprefix tailTrace_3120487
  have hstable : (prefixWord ++ tailWord_3120487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120487).length < 2 ^ (prefixWord ++ tailWord_3120487).sum := by decide
  have hdescent : baseEnd_3120487 < baseStart_3120487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120515 : List Nat := [1, 1, 1, 3, 5, 2, 1, 8]
def baseStart_3120515 : Nat := 118140960795 + 3120515 * 2 ^ 59
def prefixEnd_3120515 : Nat := 4983230072969 + 3 ^ 40 * 3120515 * 2
def baseEnd_3120515 : Nat := 118690672930738052178631

theorem tailTrace_3120515 : CollatzResearch.WordTrace tailWord_3120515 prefixEnd_3120515 118690672930738052178631 := by
  unfold tailWord_3120515
  simp only [CollatzResearch.WordTrace]
  refine ⟨113814532289914571377466999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75876354859943047584977999 113814532289914571377466999)
  ·
    refine ⟨170721798434871857066200499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113814532289914571377466999 170721798434871857066200499)
    ·
      refine ⟨256082697652307785599300749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170721798434871857066200499 256082697652307785599300749)
      ·
        refine ⟨96031011619615419599737781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256082697652307785599300749 96031011619615419599737781)
        ·
          refine ⟨9002907339338945587475417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96031011619615419599737781 9002907339338945587475417)
          ·
            refine ⟨6752180504504209190606563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9002907339338945587475417 6752180504504209190606563)
            ·
              refine ⟨10128270756756313785909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752180504504209190606563 10128270756756313785909845)
              ·
                refine ⟨118690672930738052178631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10128270756756313785909845 118690672930738052178631)
                ·
                  rfl

theorem cell22_3120515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 8].length) (baseStart_3120515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120515 prefixEnd_3120515 := by exact prefixLift 3120515
  have htrace : WordTrace (prefixWord ++ tailWord_3120515) baseStart_3120515 baseEnd_3120515 := by
    simpa [prefixWord, tailWord_3120515, baseEnd_3120515] using wordTrace_append hprefix tailTrace_3120515
  have hstable : (prefixWord ++ tailWord_3120515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120515).length < 2 ^ (prefixWord ++ tailWord_3120515).sum := by decide
  have hdescent : baseEnd_3120515 < baseStart_3120515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120521 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 4]
def baseStart_3120521 : Nat := 118140960795 + 3120521 * 2 ^ 59
def prefixEnd_3120521 : Nat := 4983230072969 + 3 ^ 40 * 3120521 * 2
def baseEnd_3120521 : Nat := 356072703433086817985887

theorem tailTrace_3120521 : CollatzResearch.WordTrace tailWord_3120521 prefixEnd_3120521 356072703433086817985887 := by
  unfold tailWord_3120521
  simp only [CollatzResearch.WordTrace]
  refine ⟨113814751127892834402185417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75876500751928556268123611 113814751127892834402185417)
  ·
    refine ⟨85361063345919625801639063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113814751127892834402185417 85361063345919625801639063)
    ·
      refine ⟨128041595018879438702458595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85361063345919625801639063 128041595018879438702458595)
      ·
        refine ⟨192062392528319158053687893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128041595018879438702458595 192062392528319158053687893)
        ·
          refine ⟨2250731162441240133441655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 192062392528319158053687893 2250731162441240133441655)
          ·
            refine ⟨3376096743661860200162483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250731162441240133441655 3376096743661860200162483)
            ·
              refine ⟨5064145115492790300243725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376096743661860200162483 5064145115492790300243725)
              ·
                refine ⟨1899054418309796362591397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5064145115492790300243725 1899054418309796362591397)
                ·
                  refine ⟨356072703433086817985887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899054418309796362591397 356072703433086817985887)
                  ·
                    rfl

theorem cell22_3120521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_3120521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120521 prefixEnd_3120521 := by exact prefixLift 3120521
  have htrace : WordTrace (prefixWord ++ tailWord_3120521) baseStart_3120521 baseEnd_3120521 := by
    simpa [prefixWord, tailWord_3120521, baseEnd_3120521] using wordTrace_append hprefix tailTrace_3120521
  have hstable : (prefixWord ++ tailWord_3120521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120521).length < 2 ^ (prefixWord ++ tailWord_3120521).sum := by decide
  have hdescent : baseEnd_3120521 < baseStart_3120521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120532 : List Nat := [2, 4, 2, 1, 2, 3, 8]
def baseStart_3120532 : Nat := 118140960795 + 3120532 * 2 ^ 59
def prefixEnd_3120532 : Nat := 4983230072969 + 3 ^ 40 * 3120532 * 2
def baseEnd_3120532 : Nat := 39563773178668892293801

theorem tailTrace_3120532 : CollatzResearch.WordTrace tailWord_3120532 prefixEnd_3120532 39563773178668892293801 := by
  unfold tailWord_3120532
  simp only [CollatzResearch.WordTrace]
  refine ⟨56907576165426491640417925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75876768220568655520557233 56907576165426491640417925)
  ·
    refine ⟨10670170531017467182578361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56907576165426491640417925 10670170531017467182578361)
    ·
      refine ⟨8002627898263100386933771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10670170531017467182578361 8002627898263100386933771)
      ·
        refine ⟨12003941847394650580400657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002627898263100386933771 12003941847394650580400657)
        ·
          refine ⟨9002956385545987935300493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12003941847394650580400657 9002956385545987935300493)
          ·
            refine ⟨3376108644579745475737685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9002956385545987935300493 3376108644579745475737685)
            ·
              refine ⟨39563773178668892293801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3376108644579745475737685 39563773178668892293801)
              ·
                rfl

theorem cell22_3120532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 8].length) (baseStart_3120532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120532 prefixEnd_3120532 := by exact prefixLift 3120532
  have htrace : WordTrace (prefixWord ++ tailWord_3120532) baseStart_3120532 baseEnd_3120532 := by
    simpa [prefixWord, tailWord_3120532, baseEnd_3120532] using wordTrace_append hprefix tailTrace_3120532
  have hstable : (prefixWord ++ tailWord_3120532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120532).length < 2 ^ (prefixWord ++ tailWord_3120532).sum := by decide
  have hdescent : baseEnd_3120532 < baseStart_3120532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120598 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3120598 : Nat := 118140960795 + 3120598 * 2 ^ 59
def prefixEnd_3120598 : Nat := 4983230072969 + 3 ^ 40 * 3120598 * 2
def baseEnd_3120598 : Nat := 1068244468972857919782425

theorem tailTrace_3120598 : CollatzResearch.WordTrace tailWord_3120598 prefixEnd_3120598 1068244468972857919782425 := by
  unfold tailWord_3120598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113597471788367284546153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75878373032409251035158965 7113597471788367284546153)
  ·
    refine ⟨5335198103841275463409615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7113597471788367284546153 5335198103841275463409615)
    ·
      refine ⟨8002797155761913195114423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335198103841275463409615 8002797155761913195114423)
      ·
        refine ⟨12004195733642869792671635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002797155761913195114423 12004195733642869792671635)
        ·
          refine ⟨18006293600464304689007453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004195733642869792671635 18006293600464304689007453)
          ·
            refine ⟨6752360100174114258377795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18006293600464304689007453 6752360100174114258377795)
            ·
              refine ⟨10128540150261171387566693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752360100174114258377795 10128540150261171387566693)
              ·
                refine ⟨1899101278173969635168755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10128540150261171387566693 1899101278173969635168755)
                ·
                  refine ⟨2848651917260954452753133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899101278173969635168755 2848651917260954452753133)
                  ·
                    refine ⟨1068244468972857919782425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2848651917260954452753133 1068244468972857919782425)
                    ·
                      rfl

theorem cell22_3120598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3120598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120598 prefixEnd_3120598 := by exact prefixLift 3120598
  have htrace : WordTrace (prefixWord ++ tailWord_3120598) baseStart_3120598 baseEnd_3120598 := by
    simpa [prefixWord, tailWord_3120598, baseEnd_3120598] using wordTrace_append hprefix tailTrace_3120598
  have hstable : (prefixWord ++ tailWord_3120598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120598).length < 2 ^ (prefixWord ++ tailWord_3120598).sum := by decide
  have hdescent : baseEnd_3120598 < baseStart_3120598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120622 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_3120622 : Nat := 118140960795 + 3120622 * 2 ^ 59
def prefixEnd_3120622 : Nat := 4983230072969 + 3 ^ 40 * 3120622 * 2
def baseEnd_3120622 : Nat := 356084228221109952394117

theorem tailTrace_3120622 : CollatzResearch.WordTrace tailWord_3120622 prefixEnd_3120622 356084228221109952394117 := by
  unfold tailWord_3120622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14227304362565866081451515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75878956600351285767741413 14227304362565866081451515)
  ·
    refine ⟨21340956543848799122177273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14227304362565866081451515 21340956543848799122177273)
    ·
      refine ⟨16005717407886599341632955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21340956543848799122177273 16005717407886599341632955)
      ·
        refine ⟨24008576111829899012449433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16005717407886599341632955 24008576111829899012449433)
        ·
          refine ⟨18006432083872424259337075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24008576111829899012449433 18006432083872424259337075)
          ·
            refine ⟨27009648125808636389005613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18006432083872424259337075 27009648125808636389005613)
            ·
              refine ⟨10128618047178238645877105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27009648125808636389005613 10128618047178238645877105)
              ·
                refine ⟨7596463535383678984407829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10128618047178238645877105 7596463535383678984407829)
                ·
                  refine ⟨356084228221109952394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7596463535383678984407829 356084228221109952394117)
                  ·
                    rfl

theorem cell22_3120622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_3120622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120622 prefixEnd_3120622 := by exact prefixLift 3120622
  have htrace : WordTrace (prefixWord ++ tailWord_3120622) baseStart_3120622 baseEnd_3120622 := by
    simpa [prefixWord, tailWord_3120622, baseEnd_3120622] using wordTrace_append hprefix tailTrace_3120622
  have hstable : (prefixWord ++ tailWord_3120622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120622).length < 2 ^ (prefixWord ++ tailWord_3120622).sum := by decide
  have hdescent : baseEnd_3120622 < baseStart_3120622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120635 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_3120635 : Nat := 118140960795 + 3120635 * 2 ^ 59
def prefixEnd_3120635 : Nat := 4983230072969 + 3 ^ 40 * 3120635 * 2
def baseEnd_3120635 : Nat := 1068257134829002156607311

theorem tailTrace_3120635 : CollatzResearch.WordTrace tailWord_3120635 prefixEnd_3120635 1068257134829002156607311 := by
  unfold tailWord_3120635
  simp only [CollatzResearch.WordTrace]
  refine ⟨113818909049479831871835359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75879272699653221247890239 113818909049479831871835359)
  ·
    refine ⟨170728363574219747807753039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113818909049479831871835359 170728363574219747807753039)
    ·
      refine ⟨256092545361329621711629559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170728363574219747807753039 256092545361329621711629559)
      ·
        refine ⟨384138818041994432567444339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256092545361329621711629559 384138818041994432567444339)
        ·
          refine ⟨576208227062991648851166509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384138818041994432567444339 576208227062991648851166509)
          ·
            refine ⟨216078085148621868319187441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 576208227062991648851166509 216078085148621868319187441)
            ·
              refine ⟨162058563861466401239390581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216078085148621868319187441 162058563861466401239390581)
              ·
                refine ⟨15192990362012475116192867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162058563861466401239390581 15192990362012475116192867)
                ·
                  refine ⟨22789485543018712674289301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15192990362012475116192867 22789485543018712674289301)
                  ·
                    refine ⟨1068257134829002156607311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22789485543018712674289301 1068257134829002156607311)
                    ·
                      rfl

theorem cell22_3120635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_3120635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120635 prefixEnd_3120635 := by exact prefixLift 3120635
  have htrace : WordTrace (prefixWord ++ tailWord_3120635) baseStart_3120635 baseEnd_3120635 := by
    simpa [prefixWord, tailWord_3120635, baseEnd_3120635] using wordTrace_append hprefix tailTrace_3120635
  have hstable : (prefixWord ++ tailWord_3120635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120635).length < 2 ^ (prefixWord ++ tailWord_3120635).sum := by decide
  have hdescent : baseEnd_3120635 < baseStart_3120635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120637 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_3120637 : Nat := 118140960795 + 3120637 * 2 ^ 59
def prefixEnd_3120637 : Nat := 4983230072969 + 3 ^ 40 * 3120637 * 2
def baseEnd_3120637 : Nat := 1068257819469874818057305

theorem tailTrace_3120637 : CollatzResearch.WordTrace tailWord_3120637 prefixEnd_3120637 1068257819469874818057305 := by
  unfold tailWord_3120637
  simp only [CollatzResearch.WordTrace]
  refine ⟨113818981995472586213408165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75879321330315057475605443 113818981995472586213408165)
  ·
    refine ⟨21341059124151109915014031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113818981995472586213408165 21341059124151109915014031)
    ·
      refine ⟨32011588686226664872521047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21341059124151109915014031 32011588686226664872521047)
      ·
        refine ⟨48017383029339997308781571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32011588686226664872521047 48017383029339997308781571)
        ·
          refine ⟨72026074544009995963172357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48017383029339997308781571 72026074544009995963172357)
          ·
            refine ⟨13504888977001874243094817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72026074544009995963172357 13504888977001874243094817)
            ·
              refine ⟨10128666732751405682321113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13504888977001874243094817 10128666732751405682321113)
              ·
                refine ⟨7596500049563554261740835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10128666732751405682321113 7596500049563554261740835)
                ·
                  refine ⟨11394750074345331392611253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7596500049563554261740835 11394750074345331392611253)
                  ·
                    refine ⟨1068257819469874818057305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11394750074345331392611253 1068257819469874818057305)
                    ·
                      rfl

theorem cell22_3120637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_3120637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120637 prefixEnd_3120637 := by exact prefixLift 3120637
  have htrace : WordTrace (prefixWord ++ tailWord_3120637) baseStart_3120637 baseEnd_3120637 := by
    simpa [prefixWord, tailWord_3120637, baseEnd_3120637] using wordTrace_append hprefix tailTrace_3120637
  have hstable : (prefixWord ++ tailWord_3120637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120637).length < 2 ^ (prefixWord ++ tailWord_3120637).sum := by decide
  have hdescent : baseEnd_3120637 < baseStart_3120637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120665 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_3120665 : Nat := 118140960795 + 3120665 * 2 ^ 59
def prefixEnd_3120665 : Nat := 4983230072969 + 3 ^ 40 * 3120665 * 2
def baseEnd_3120665 : Nat := 1068267404442092078357219

theorem tailTrace_3120665 : CollatzResearch.WordTrace tailWord_3120665 prefixEnd_3120665 1068267404442092078357219 := by
  unfold tailWord_3120665
  simp only [CollatzResearch.WordTrace]
  refine ⟨113820003239371146995427449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75880002159580764663618299 113820003239371146995427449)
  ·
    refine ⟨85365002429528360246570587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113820003239371146995427449 85365002429528360246570587)
    ·
      refine ⟨128047503644292540369855881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85365002429528360246570587 128047503644292540369855881)
      ·
        refine ⟨96035627733219405277391911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128047503644292540369855881 96035627733219405277391911)
        ·
          refine ⟨144053441599829107916087867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96035627733219405277391911 144053441599829107916087867)
          ·
            refine ⟨216080162399743661874131801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144053441599829107916087867 216080162399743661874131801)
            ·
              refine ⟨162060121799807746405598851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216080162399743661874131801 162060121799807746405598851)
              ·
                refine ⟨243090182699711619608398277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162060121799807746405598851 243090182699711619608398277)
                ·
                  refine ⟨45579409256195928676574677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243090182699711619608398277 45579409256195928676574677)
                  ·
                    refine ⟨1068267404442092078357219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45579409256195928676574677 1068267404442092078357219)
                    ·
                      rfl

theorem cell22_3120665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_3120665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120665 prefixEnd_3120665 := by exact prefixLift 3120665
  have htrace : WordTrace (prefixWord ++ tailWord_3120665) baseStart_3120665 baseEnd_3120665 := by
    simpa [prefixWord, tailWord_3120665, baseEnd_3120665] using wordTrace_append hprefix tailTrace_3120665
  have hstable : (prefixWord ++ tailWord_3120665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120665).length < 2 ^ (prefixWord ++ tailWord_3120665).sum := by decide
  have hdescent : baseEnd_3120665 < baseStart_3120665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120682 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3120682 : Nat := 118140960795 + 3120682 * 2 ^ 59
def prefixEnd_3120682 : Nat := 4983230072969 + 3 ^ 40 * 3120682 * 2
def baseEnd_3120682 : Nat := 1068273223889509700682167

theorem tailTrace_3120682 : CollatzResearch.WordTrace tailWord_3120682 prefixEnd_3120682 1068273223889509700682167 := by
  unfold tailWord_3120682
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455155820077389724699075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75880415520206372599197533 28455155820077389724699075)
  ·
    refine ⟨42682733730116084587048613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28455155820077389724699075 42682733730116084587048613)
    ·
      refine ⟨8003012574396765860071615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42682733730116084587048613 8003012574396765860071615)
      ·
        refine ⟨12004518861595148790107423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003012574396765860071615 12004518861595148790107423)
        ·
          refine ⟨18006778292392723185161135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004518861595148790107423 18006778292392723185161135)
          ·
            refine ⟨27010167438589084777741703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18006778292392723185161135 27010167438589084777741703)
            ·
              refine ⟨40515251157883627166612555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27010167438589084777741703 40515251157883627166612555)
              ·
                refine ⟨60772876736825440749918833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40515251157883627166612555 60772876736825440749918833)
                ·
                  refine ⟨45579657552619080562439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60772876736825440749918833 45579657552619080562439125)
                  ·
                    refine ⟨1068273223889509700682167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45579657552619080562439125 1068273223889509700682167)
                    ·
                      rfl

theorem cell22_3120682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3120682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120682 prefixEnd_3120682 := by exact prefixLift 3120682
  have htrace : WordTrace (prefixWord ++ tailWord_3120682) baseStart_3120682 baseEnd_3120682 := by
    simpa [prefixWord, tailWord_3120682, baseEnd_3120682] using wordTrace_append hprefix tailTrace_3120682
  have hstable : (prefixWord ++ tailWord_3120682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120682).length < 2 ^ (prefixWord ++ tailWord_3120682).sum := by decide
  have hdescent : baseEnd_3120682 < baseStart_3120682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120716 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_3120716 : Nat := 118140960795 + 3120716 * 2 ^ 59
def prefixEnd_3120716 : Nat := 4983230072969 + 3 ^ 40 * 3120716 * 2
def baseEnd_3120716 : Nat := 1068284862784344945332063

theorem tailTrace_3120716 : CollatzResearch.WordTrace tailWord_3120716 prefixEnd_3120716 1068284862784344945332063 := by
  unfold tailWord_3120716
  simp only [CollatzResearch.WordTrace]
  refine ⟨56910931681093191352767001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75881242241457588470356001 56910931681093191352767001)
  ·
    refine ⟨42683198760819893514575251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56910931681093191352767001 42683198760819893514575251)
    ·
      refine ⟨64024798141229840271862877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42683198760819893514575251 64024798141229840271862877)
      ·
        refine ⟨24009299302961190101948579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64024798141229840271862877 24009299302961190101948579)
        ·
          refine ⟨36013948954441785152922869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24009299302961190101948579 36013948954441785152922869)
          ·
            refine ⟨3376307714478917358086519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36013948954441785152922869 3376307714478917358086519)
            ·
              refine ⟨5064461571718376037129779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376307714478917358086519 5064461571718376037129779)
              ·
                refine ⟨7596692357577564055694669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064461571718376037129779 7596692357577564055694669)
                ·
                  refine ⟨2848759634091586520885501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7596692357577564055694669 2848759634091586520885501)
                  ·
                    refine ⟨1068284862784344945332063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2848759634091586520885501 1068284862784344945332063)
                    ·
                      rfl

theorem cell22_3120716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_3120716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120716 prefixEnd_3120716 := by exact prefixLift 3120716
  have htrace : WordTrace (prefixWord ++ tailWord_3120716) baseStart_3120716 baseEnd_3120716 := by
    simpa [prefixWord, tailWord_3120716, baseEnd_3120716] using wordTrace_append hprefix tailTrace_3120716
  have hstable : (prefixWord ++ tailWord_3120716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120716).length < 2 ^ (prefixWord ++ tailWord_3120716).sum := by decide
  have hdescent : baseEnd_3120716 < baseStart_3120716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120804 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_3120804 : Nat := 118140960795 + 3120804 * 2 ^ 59
def prefixEnd_3120804 : Nat := 4983230072969 + 3 ^ 40 * 3120804 * 2
def baseEnd_3120804 : Nat := 1068314986982742049131793

theorem tailTrace_3120804 : CollatzResearch.WordTrace tailWord_3120804 prefixEnd_3120804 1068314986982742049131793 := by
  unfold tailWord_3120804
  simp only [CollatzResearch.WordTrace]
  refine ⟨56912536492933786867368733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75883381990578382489824977 56912536492933786867368733)
  ·
    refine ⟨21342201184850170075263275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56912536492933786867368733 21342201184850170075263275)
    ·
      refine ⟨32013301777275255112894913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21342201184850170075263275 32013301777275255112894913)
      ·
        refine ⟨24009976332956441334671185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32013301777275255112894913 24009976332956441334671185)
        ·
          refine ⟨18007482249717331001003389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24009976332956441334671185 18007482249717331001003389)
          ·
            refine ⟨6752805843643999125376271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18007482249717331001003389 6752805843643999125376271)
            ·
              refine ⟨10129208765465998688064407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6752805843643999125376271 10129208765465998688064407)
              ·
                refine ⟨15193813148198998032096611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129208765465998688064407 15193813148198998032096611)
                ·
                  refine ⟨22790719722298497048144917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15193813148198998032096611 22790719722298497048144917)
                  ·
                    refine ⟨1068314986982742049131793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22790719722298497048144917 1068314986982742049131793)
                    ·
                      rfl

theorem cell22_3120804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_3120804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120804 prefixEnd_3120804 := by exact prefixLift 3120804
  have htrace : WordTrace (prefixWord ++ tailWord_3120804) baseStart_3120804 baseEnd_3120804 := by
    simpa [prefixWord, tailWord_3120804, baseEnd_3120804] using wordTrace_append hprefix tailTrace_3120804
  have hstable : (prefixWord ++ tailWord_3120804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120804).length < 2 ^ (prefixWord ++ tailWord_3120804).sum := by decide
  have hdescent : baseEnd_3120804 < baseStart_3120804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120823 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 2, 3]
def baseStart_3120823 : Nat := 118140960795 + 3120823 * 2 ^ 59
def prefixEnd_3120823 : Nat := 4983230072969 + 3 ^ 40 * 3120823 * 2
def baseEnd_3120823 : Nat := 1068321491071032332906735

theorem tailTrace_3120823 : CollatzResearch.WordTrace tailWord_3120823 prefixEnd_3120823 1068321491071032332906735 := by
  unfold tailWord_3120823
  simp only [CollatzResearch.WordTrace]
  refine ⟨113825765972798739979679123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75883843981865826653119415 113825765972798739979679123)
  ·
    refine ⟨170738648959198109969518685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113825765972798739979679123 170738648959198109969518685)
    ·
      refine ⟨64026993359699291238569507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170738648959198109969518685 64026993359699291238569507)
      ·
        refine ⟨96040490039548936857854261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64026993359699291238569507 96040490039548936857854261)
        ·
          refine ⟨9003795941207712830423837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96040490039548936857854261 9003795941207712830423837)
          ·
            refine ⟨3376423477952892311408939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9003795941207712830423837 3376423477952892311408939)
            ·
              refine ⟨5064635216929338467113409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376423477952892311408939 5064635216929338467113409)
              ·
                refine ⟨3798476412697003850335057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064635216929338467113409 3798476412697003850335057)
                ·
                  refine ⟨2848857309522752887751293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798476412697003850335057 2848857309522752887751293)
                  ·
                    refine ⟨1068321491071032332906735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2848857309522752887751293 1068321491071032332906735)
                    ·
                      rfl

theorem cell22_3120823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_3120823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120823 prefixEnd_3120823 := by exact prefixLift 3120823
  have htrace : WordTrace (prefixWord ++ tailWord_3120823) baseStart_3120823 baseEnd_3120823 := by
    simpa [prefixWord, tailWord_3120823, baseEnd_3120823] using wordTrace_append hprefix tailTrace_3120823
  have hstable : (prefixWord ++ tailWord_3120823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120823).length < 2 ^ (prefixWord ++ tailWord_3120823).sum := by decide
  have hdescent : baseEnd_3120823 < baseStart_3120823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120838 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3120838 : Nat := 118140960795 + 3120838 * 2 ^ 59
def prefixEnd_3120838 : Nat := 4983230072969 + 3 ^ 40 * 3120838 * 2
def baseEnd_3120838 : Nat := 1068326625877577293781689

theorem tailTrace_3120838 : CollatzResearch.WordTrace tailWord_3120838 prefixEnd_3120838 1068326625877577293781689 := by
  unfold tailWord_3120838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557072283367012423171099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75884208711829598360983445 3557072283367012423171099)
  ·
    refine ⟨5335608425050518634756649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3557072283367012423171099 5335608425050518634756649)
    ·
      refine ⟨4001706318787888976067487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5335608425050518634756649 4001706318787888976067487)
      ·
        refine ⟨6002559478181833464101231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001706318787888976067487 6002559478181833464101231)
        ·
          refine ⟨9003839217272750196151847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002559478181833464101231 9003839217272750196151847)
          ·
            refine ⟨13505758825909125294227771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003839217272750196151847 13505758825909125294227771)
            ·
              refine ⟨20258638238863687941341657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13505758825909125294227771 20258638238863687941341657)
              ·
                refine ⟨15193978679147765956006243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20258638238863687941341657 15193978679147765956006243)
                ·
                  refine ⟨22790968018721648934009365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15193978679147765956006243 22790968018721648934009365)
                  ·
                    refine ⟨1068326625877577293781689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22790968018721648934009365 1068326625877577293781689)
                    ·
                      rfl

theorem cell22_3120838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3120838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120838 prefixEnd_3120838 := by exact prefixLift 3120838
  have htrace : WordTrace (prefixWord ++ tailWord_3120838) baseStart_3120838 baseEnd_3120838 := by
    simpa [prefixWord, tailWord_3120838, baseEnd_3120838] using wordTrace_append hprefix tailTrace_3120838
  have hstable : (prefixWord ++ tailWord_3120838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120838).length < 2 ^ (prefixWord ++ tailWord_3120838).sum := by decide
  have hdescent : baseEnd_3120838 < baseStart_3120838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120928 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 1, 4]
def baseStart_3120928 : Nat := 118140960795 + 3120928 * 2 ^ 59
def prefixEnd_3120928 : Nat := 4983230072969 + 3 ^ 40 * 3120928 * 2
def baseEnd_3120928 : Nat := 1068357434716847059031413

theorem tailTrace_3120928 : CollatzResearch.WordTrace tailWord_3120928 prefixEnd_3120928 1068357434716847059031413 := by
  unfold tailWord_3120928
  simp only [CollatzResearch.WordTrace]
  refine ⟨56914797818709171456125719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75886397091612228608167625 56914797818709171456125719)
  ·
    refine ⟨85372196728063757184188579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56914797818709171456125719 85372196728063757184188579)
    ·
      refine ⟨128058295092095635776282869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85372196728063757184188579 128058295092095635776282869)
      ·
        refine ⟨12005465164883965854026519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128058295092095635776282869 12005465164883965854026519)
        ·
          refine ⟨18008197747325948781039779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005465164883965854026519 18008197747325948781039779)
          ·
            refine ⟨27012296620988923171559669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18008197747325948781039779 27012296620988923171559669)
            ·
              refine ⟨2532402808217711547333719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27012296620988923171559669 2532402808217711547333719)
              ·
                refine ⟨3798604212326567321000579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532402808217711547333719 3798604212326567321000579)
                ·
                  refine ⟨5697906318489850981500869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3798604212326567321000579 5697906318489850981500869)
                  ·
                    refine ⟨1068357434716847059031413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5697906318489850981500869 1068357434716847059031413)
                    ·
                      rfl

theorem cell22_3120928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_3120928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120928 prefixEnd_3120928 := by exact prefixLift 3120928
  have htrace : WordTrace (prefixWord ++ tailWord_3120928) baseStart_3120928 baseEnd_3120928 := by
    simpa [prefixWord, tailWord_3120928, baseEnd_3120928] using wordTrace_append hprefix tailTrace_3120928
  have hstable : (prefixWord ++ tailWord_3120928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120928).length < 2 ^ (prefixWord ++ tailWord_3120928).sum := by decide
  have hdescent : baseEnd_3120928 < baseStart_3120928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120958 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3120958 : Nat := 118140960795 + 3120958 * 2 ^ 59
def prefixEnd_3120958 : Nat := 4983230072969 + 3 ^ 40 * 3120958 * 2
def baseEnd_3120958 : Nat := 1068367704329936980781321

theorem tailTrace_3120958 : CollatzResearch.WordTrace tailWord_3120958 prefixEnd_3120958 1068367704329936980781321 := by
  unfold tailWord_3120958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14228836228413707254480441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75887126551539772023895685 14228836228413707254480441)
  ·
    refine ⟨10671627171310280440860331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14228836228413707254480441 10671627171310280440860331)
    ·
      refine ⟨16007440756965420661290497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10671627171310280440860331 16007440756965420661290497)
      ·
        refine ⟨12005580567724065495967873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16007440756965420661290497 12005580567724065495967873)
        ·
          refine ⟨9004185425793049121975905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12005580567724065495967873 9004185425793049121975905)
          ·
            refine ⟨6753139069344786841481929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9004185425793049121975905 6753139069344786841481929)
            ·
              refine ⟨5064854302008590131111447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6753139069344786841481929 5064854302008590131111447)
              ·
                refine ⟨7597281453012885196667171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064854302008590131111447 7597281453012885196667171)
                ·
                  refine ⟨11395922179519327795000757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7597281453012885196667171 11395922179519327795000757)
                  ·
                    refine ⟨1068367704329936980781321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11395922179519327795000757 1068367704329936980781321)
                    ·
                      rfl

theorem cell22_3120958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3120958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120958 prefixEnd_3120958 := by exact prefixLift 3120958
  have htrace : WordTrace (prefixWord ++ tailWord_3120958) baseStart_3120958 baseEnd_3120958 := by
    simpa [prefixWord, tailWord_3120958, baseEnd_3120958] using wordTrace_append hprefix tailTrace_3120958
  have hstable : (prefixWord ++ tailWord_3120958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120958).length < 2 ^ (prefixWord ++ tailWord_3120958).sum := by decide
  have hdescent : baseEnd_3120958 < baseStart_3120958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120973 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3120973 : Nat := 118140960795 + 3120973 * 2 ^ 59
def prefixEnd_3120973 : Nat := 4983230072969 + 3 ^ 40 * 3120973 * 2
def baseEnd_3120973 : Nat := 1068372839136481941656275

theorem tailTrace_3120973 : CollatzResearch.WordTrace tailWord_3120973 prefixEnd_3120973 1068372839136481941656275 := by
  unfold tailWord_3120973
  simp only [CollatzResearch.WordTrace]
  refine ⟨113831236922255315597639573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75887491281503543731759715 113831236922255315597639573)
  ·
    refine ⟨5335839230730717918639355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113831236922255315597639573 5335839230730717918639355)
    ·
      refine ⟨8003758846096076877959033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335839230730717918639355 8003758846096076877959033)
      ·
        refine ⟨6002819134572057658469275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8003758846096076877959033 6002819134572057658469275)
        ·
          refine ⟨9004228701858086487703913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002819134572057658469275 9004228701858086487703913)
          ·
            refine ⟨6753171526393564865777935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9004228701858086487703913 6753171526393564865777935)
            ·
              refine ⟨10129757289590347298666903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6753171526393564865777935 10129757289590347298666903)
              ·
                refine ⟨15194635934385520948000355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129757289590347298666903 15194635934385520948000355)
                ·
                  refine ⟨22791953901578281422000533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15194635934385520948000355 22791953901578281422000533)
                  ·
                    refine ⟨1068372839136481941656275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22791953901578281422000533 1068372839136481941656275)
                    ·
                      rfl

theorem cell22_3120973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3120973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120973 prefixEnd_3120973 := by exact prefixLift 3120973
  have htrace : WordTrace (prefixWord ++ tailWord_3120973) baseStart_3120973 baseEnd_3120973 := by
    simpa [prefixWord, tailWord_3120973, baseEnd_3120973] using wordTrace_append hprefix tailTrace_3120973
  have hstable : (prefixWord ++ tailWord_3120973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120973).length < 2 ^ (prefixWord ++ tailWord_3120973).sum := by decide
  have hdescent : baseEnd_3120973 < baseStart_3120973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3120986 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_3120986 : Nat := 118140960795 + 3120986 * 2 ^ 59
def prefixEnd_3120986 : Nat := 4983230072969 + 3 ^ 40 * 3120986 * 2
def baseEnd_3120986 : Nat := 1068377289302154241081235

theorem tailTrace_3120986 : CollatzResearch.WordTrace tailWord_3120986 prefixEnd_3120986 1068377289302154241081235 := by
  unfold tailWord_3120986
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457927767802054704465703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75887807380805479211908541 28457927767802054704465703)
  ·
    refine ⟨42686891651703082056698555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28457927767802054704465703 42686891651703082056698555)
    ·
      refine ⟨64030337477554623085047833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42686891651703082056698555 64030337477554623085047833)
      ·
        refine ⟨48022753108165967313785875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64030337477554623085047833 48022753108165967313785875)
        ·
          refine ⟨72034129662248950970678813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48022753108165967313785875 72034129662248950970678813)
          ·
            refine ⟨27012798623343356614004555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72034129662248950970678813 27012798623343356614004555)
            ·
              refine ⟨40519197935015034921006833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27012798623343356614004555 40519197935015034921006833)
              ·
                refine ⟨30389398451261276190755125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40519197935015034921006833 30389398451261276190755125)
                ·
                  refine ⟨2849006104805744642883293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30389398451261276190755125 2849006104805744642883293)
                  ·
                    refine ⟨1068377289302154241081235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849006104805744642883293 1068377289302154241081235)
                    ·
                      rfl

theorem cell22_3120986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_3120986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3120986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3120986 prefixEnd_3120986 := by exact prefixLift 3120986
  have htrace : WordTrace (prefixWord ++ tailWord_3120986) baseStart_3120986 baseEnd_3120986 := by
    simpa [prefixWord, tailWord_3120986, baseEnd_3120986] using wordTrace_append hprefix tailTrace_3120986
  have hstable : (prefixWord ++ tailWord_3120986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3120986).length < 2 ^ (prefixWord ++ tailWord_3120986).sum := by decide
  have hdescent : baseEnd_3120986 < baseStart_3120986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3120986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121054 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_3121054 : Nat := 118140960795 + 3121054 * 2 ^ 59
def prefixEnd_3121054 : Nat := 4983230072969 + 3 ^ 40 * 3121054 * 2
def baseEnd_3121054 : Nat := 1068400567091824730381027

theorem tailTrace_3121054 : CollatzResearch.WordTrace tailWord_3121054 prefixEnd_3121054 1068400567091824730381027 := by
  unfold tailWord_3121054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14229273904370233303917277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75889460823307910954225477 14229273904370233303917277)
  ·
    refine ⟨5335977714138837488968979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14229273904370233303917277 5335977714138837488968979)
    ·
      refine ⟨8003966571208256233453469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335977714138837488968979 8003966571208256233453469)
      ·
        refine ⟨3001487464203096087545051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8003966571208256233453469 3001487464203096087545051)
        ·
          refine ⟨4502231196304644131317577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001487464203096087545051 4502231196304644131317577)
          ·
            refine ⟨3376673397228483098488183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502231196304644131317577 3376673397228483098488183)
            ·
              refine ⟨5065010095842724647732275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376673397228483098488183 5065010095842724647732275)
              ·
                refine ⟨7597515143764086971598413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065010095842724647732275 7597515143764086971598413)
                ·
                  refine ⟨2849068178911532614349405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7597515143764086971598413 2849068178911532614349405)
                  ·
                    refine ⟨1068400567091824730381027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849068178911532614349405 1068400567091824730381027)
                    ·
                      rfl

theorem cell22_3121054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_3121054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121054 prefixEnd_3121054 := by exact prefixLift 3121054
  have htrace : WordTrace (prefixWord ++ tailWord_3121054) baseStart_3121054 baseEnd_3121054 := by
    simpa [prefixWord, tailWord_3121054, baseEnd_3121054] using wordTrace_append hprefix tailTrace_3121054
  have hstable : (prefixWord ++ tailWord_3121054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121054).length < 2 ^ (prefixWord ++ tailWord_3121054).sum := by decide
  have hdescent : baseEnd_3121054 < baseStart_3121054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121106 : List Nat := [3, 2, 2, 3, 12]
def baseStart_3121106 : Nat := 118140960795 + 3121106 * 2 ^ 59
def prefixEnd_3121106 : Nat := 4983230072969 + 3 ^ 40 * 3121106 * 2
def baseEnd_3121106 : Nat := 4396783406397176658769

theorem tailTrace_3121106 : CollatzResearch.WordTrace tailWord_3121106 prefixEnd_3121106 4396783406397176658769 := by
  unfold tailWord_3121106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28459021957693369828057793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75890725220515652874820781 28459021957693369828057793)
  ·
    refine ⟨21344266468270027371043345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28459021957693369828057793 21344266468270027371043345)
    ·
      refine ⟨16008199851202520528282509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21344266468270027371043345 16008199851202520528282509)
      ·
        refine ⟨6003074944200945198105941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16008199851202520528282509 6003074944200945198105941)
        ·
          refine ⟨4396783406397176658769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6003074944200945198105941 4396783406397176658769)
          ·
            rfl

theorem cell22_3121106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 12].length) (baseStart_3121106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121106 prefixEnd_3121106 := by exact prefixLift 3121106
  have htrace : WordTrace (prefixWord ++ tailWord_3121106) baseStart_3121106 baseEnd_3121106 := by
    simpa [prefixWord, tailWord_3121106, baseEnd_3121106] using wordTrace_append hprefix tailTrace_3121106
  have hstable : (prefixWord ++ tailWord_3121106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121106).length < 2 ^ (prefixWord ++ tailWord_3121106).sum := by decide
  have hdescent : baseEnd_3121106 < baseStart_3121106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121108 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3121108 : Nat := 118140960795 + 3121108 * 2 ^ 59
def prefixEnd_3121108 : Nat := 4983230072969 + 3 ^ 40 * 3121108 * 2
def baseEnd_3121108 : Nat := 1068419052395386589530861

theorem tailTrace_3121108 : CollatzResearch.WordTrace tailWord_3121108 prefixEnd_3121108 1068419052395386589530861 := by
  unfold tailWord_3121108
  simp only [CollatzResearch.WordTrace]
  refine ⟨56918080388383116826901989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75890773851177489102535985 56918080388383116826901989)
  ·
    refine ⟨10672140072821834405044123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56918080388383116826901989 10672140072821834405044123)
    ·
      refine ⟨16008210109232751607566185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10672140072821834405044123 16008210109232751607566185)
      ·
        refine ⟨12006157581924563705674639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16008210109232751607566185 12006157581924563705674639)
        ·
          refine ⟨18009236372886845558511959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12006157581924563705674639 18009236372886845558511959)
          ·
            refine ⟨27013854559330268337767939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18009236372886845558511959 27013854559330268337767939)
            ·
              refine ⟨40520781838995402506651909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27013854559330268337767939 40520781838995402506651909)
              ·
                refine ⟨7597646594811637969997233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40520781838995402506651909 7597646594811637969997233)
                ·
                  refine ⟨5698234946108728477497925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7597646594811637969997233 5698234946108728477497925)
                  ·
                    refine ⟨1068419052395386589530861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698234946108728477497925 1068419052395386589530861)
                    ·
                      rfl

theorem cell22_3121108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3121108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121108 prefixEnd_3121108 := by exact prefixLift 3121108
  have htrace : WordTrace (prefixWord ++ tailWord_3121108) baseStart_3121108 baseEnd_3121108 := by
    simpa [prefixWord, tailWord_3121108, baseEnd_3121108] using wordTrace_append hprefix tailTrace_3121108
  have hstable : (prefixWord ++ tailWord_3121108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121108).length < 2 ^ (prefixWord ++ tailWord_3121108).sum := by decide
  have hdescent : baseEnd_3121108 < baseStart_3121108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121123 : List Nat := [1, 1, 1, 6, 1, 4, 1, 7]
def baseStart_3121123 : Nat := 118140960795 + 3121123 * 2 ^ 59
def prefixEnd_3121123 : Nat := 4983230072969 + 3 ^ 40 * 3121123 * 2
def baseEnd_3121123 : Nat := 118713798577992394489535

theorem tailTrace_3121123 : CollatzResearch.WordTrace tailWord_3121123 prefixEnd_3121123 118713798577992394489535 := by
  unfold tailWord_3121123
  simp only [CollatzResearch.WordTrace]
  refine ⟨113836707871711891215600023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75891138581141260810400015 113836707871711891215600023)
  ·
    refine ⟨170755061807567836823400035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113836707871711891215600023 170755061807567836823400035)
    ·
      refine ⟨256132592711351755235100053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170755061807567836823400035 256132592711351755235100053)
      ·
        refine ⟨12006215283344613526645315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 256132592711351755235100053 12006215283344613526645315)
        ·
          refine ⟨18009322925016920289967973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12006215283344613526645315 18009322925016920289967973)
          ·
            refine ⟨3376748048440672554368995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18009322925016920289967973 3376748048440672554368995)
            ·
              refine ⟨5065122072661008831553493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376748048440672554368995 5065122072661008831553493)
              ·
                refine ⟨118713798577992394489535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5065122072661008831553493 118713798577992394489535)
                ·
                  rfl

theorem cell22_3121123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 7].length) (baseStart_3121123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121123 prefixEnd_3121123 := by exact prefixLift 3121123
  have htrace : WordTrace (prefixWord ++ tailWord_3121123) baseStart_3121123 baseEnd_3121123 := by
    simpa [prefixWord, tailWord_3121123, baseEnd_3121123] using wordTrace_append hprefix tailTrace_3121123
  have hstable : (prefixWord ++ tailWord_3121123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121123).length < 2 ^ (prefixWord ++ tailWord_3121123).sum := by decide
  have hdescent : baseEnd_3121123 < baseStart_3121123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121142 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3121142 : Nat := 118140960795 + 3121142 * 2 ^ 59
def prefixEnd_3121142 : Nat := 4983230072969 + 3 ^ 40 * 3121142 * 2
def baseEnd_3121142 : Nat := 1068430691290221834180757

theorem tailTrace_3121142 : CollatzResearch.WordTrace tailWord_3121142 prefixEnd_3121142 1068430691290221834180757 := by
  unfold tailWord_3121142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114837553665191091283855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75891600572428704973694453 7114837553665191091283855)
  ·
    refine ⟨10672256330497786636925783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7114837553665191091283855 10672256330497786636925783)
    ·
      refine ⟨16008384495746679955388675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10672256330497786636925783 16008384495746679955388675)
      ·
        refine ⟨24012576743620019933083013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16008384495746679955388675 24012576743620019933083013)
        ·
          refine ⟨4502358139428753737453065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24012576743620019933083013 4502358139428753737453065)
          ·
            refine ⟨3376768604571565303089799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502358139428753737453065 3376768604571565303089799)
            ·
              refine ⟨5065152906857347954634699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376768604571565303089799 5065152906857347954634699)
              ·
                refine ⟨7597729360286021931952049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065152906857347954634699 7597729360286021931952049)
                ·
                  refine ⟨5698297020214516448964037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7597729360286021931952049 5698297020214516448964037)
                  ·
                    refine ⟨1068430691290221834180757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698297020214516448964037 1068430691290221834180757)
                    ·
                      rfl

theorem cell22_3121142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3121142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121142 prefixEnd_3121142 := by exact prefixLift 3121142
  have htrace : WordTrace (prefixWord ++ tailWord_3121142) baseStart_3121142 baseEnd_3121142 := by
    simpa [prefixWord, tailWord_3121142, baseEnd_3121142] using wordTrace_append hprefix tailTrace_3121142
  have hstable : (prefixWord ++ tailWord_3121142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121142).length < 2 ^ (prefixWord ++ tailWord_3121142).sum := by decide
  have hdescent : baseEnd_3121142 < baseStart_3121142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121196 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_3121196 : Nat := 118140960795 + 3121196 * 2 ^ 59
def prefixEnd_3121196 : Nat := 4983230072969 + 3 ^ 40 * 3121196 * 2
def baseEnd_3121196 : Nat := 356149725531261231110197

theorem tailTrace_3121196 : CollatzResearch.WordTrace tailWord_3121196 prefixEnd_3121196 356149725531261231110197 := by
  unfold tailWord_3121196
  simp only [CollatzResearch.WordTrace]
  refine ⟨56919685200223712341503721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75892913600298283122004961 56919685200223712341503721)
  ·
    refine ⟨42689763900167784256127791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56919685200223712341503721 42689763900167784256127791)
    ·
      refine ⟨64034645850251676384191687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42689763900167784256127791 64034645850251676384191687)
      ·
        refine ⟨96051968775377514576287531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64034645850251676384191687 96051968775377514576287531)
        ·
          refine ⟨144077953163066271864431297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96051968775377514576287531 144077953163066271864431297)
          ·
            refine ⟨108058464872299703898323473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144077953163066271864431297 108058464872299703898323473)
            ·
              refine ⟨81043848654224777923742605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108058464872299703898323473 81043848654224777923742605)
              ·
                refine ⟨30391443245334291721403477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81043848654224777923742605 30391443245334291721403477)
                ·
                  refine ⟨356149725531261231110197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30391443245334291721403477 356149725531261231110197)
                  ·
                    rfl

theorem cell22_3121196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_3121196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121196 prefixEnd_3121196 := by exact prefixLift 3121196
  have htrace : WordTrace (prefixWord ++ tailWord_3121196) baseStart_3121196 baseEnd_3121196 := by
    simpa [prefixWord, tailWord_3121196, baseEnd_3121196] using wordTrace_append hprefix tailTrace_3121196
  have hstable : (prefixWord ++ tailWord_3121196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121196).length < 2 ^ (prefixWord ++ tailWord_3121196).sum := by decide
  have hdescent : baseEnd_3121196 < baseStart_3121196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121230 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_3121230 : Nat := 118140960795 + 3121230 * 2 ^ 59
def prefixEnd_3121230 : Nat := 4983230072969 + 3 ^ 40 * 3121230 * 2
def baseEnd_3121230 : Nat := 356153605162872979326829

theorem tailTrace_3121230 : CollatzResearch.WordTrace tailWord_3121230 prefixEnd_3121230 356153605162872979326829 := by
  unfold tailWord_3121230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14230076310290531061218143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75893740321549498993163429 14230076310290531061218143)
  ·
    refine ⟨21345114465435796591827215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14230076310290531061218143 21345114465435796591827215)
    ·
      refine ⟨32017671698153694887740823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21345114465435796591827215 32017671698153694887740823)
      ·
        refine ⟨48026507547230542331611235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32017671698153694887740823 48026507547230542331611235)
        ·
          refine ⟨72039761320845813497416853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48026507547230542331611235 72039761320845813497416853)
          ·
            refine ⟨3376863811914647507691415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72039761320845813497416853 3376863811914647507691415)
            ·
              refine ⟨5065295717871971261537123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376863811914647507691415 5065295717871971261537123)
              ·
                refine ⟨7597943576807956892305685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065295717871971261537123 7597943576807956892305685)
                ·
                  refine ⟨356153605162872979326829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7597943576807956892305685 356153605162872979326829)
                  ·
                    rfl

theorem cell22_3121230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_3121230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121230 prefixEnd_3121230 := by exact prefixLift 3121230
  have htrace : WordTrace (prefixWord ++ tailWord_3121230) baseStart_3121230 baseEnd_3121230 := by
    simpa [prefixWord, tailWord_3121230, baseEnd_3121230] using wordTrace_append hprefix tailTrace_3121230
  have hstable : (prefixWord ++ tailWord_3121230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121230).length < 2 ^ (prefixWord ++ tailWord_3121230).sum := by decide
  have hdescent : baseEnd_3121230 < baseStart_3121230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121260 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_3121260 : Nat := 118140960795 + 3121260 * 2 ^ 59
def prefixEnd_3121260 : Nat := 4983230072969 + 3 ^ 40 * 3121260 * 2
def baseEnd_3121260 : Nat := 1068471085101708859730395

theorem tailTrace_3121260 : CollatzResearch.WordTrace tailWord_3121260 prefixEnd_3121260 1068471085101708859730395 := by
  unfold tailWord_3121260
  simp only [CollatzResearch.WordTrace]
  refine ⟨56920852336107781806668617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75894469781477042408891489 56920852336107781806668617)
  ·
    refine ⟨42690639252080836355001463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56920852336107781806668617 42690639252080836355001463)
    ·
      refine ⟨64035958878121254532502195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42690639252080836355001463 64035958878121254532502195)
      ·
        refine ⟨96053938317181881798753293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64035958878121254532502195 96053938317181881798753293)
        ·
          refine ⟨36020226868943205674532485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96053938317181881798753293 36020226868943205674532485)
          ·
            refine ⟨6753792537926851063974841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36020226868943205674532485 6753792537926851063974841)
            ·
              refine ⟨5065344403445138297981131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6753792537926851063974841 5065344403445138297981131)
              ·
                refine ⟨7598016605167707446971697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065344403445138297981131 7598016605167707446971697)
                ·
                  refine ⟨5698512453875780585228773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7598016605167707446971697 5698512453875780585228773)
                  ·
                    refine ⟨1068471085101708859730395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698512453875780585228773 1068471085101708859730395)
                    ·
                      rfl

theorem cell22_3121260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_3121260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121260 prefixEnd_3121260 := by exact prefixLift 3121260
  have htrace : WordTrace (prefixWord ++ tailWord_3121260) baseStart_3121260 baseEnd_3121260 := by
    simpa [prefixWord, tailWord_3121260, baseEnd_3121260] using wordTrace_append hprefix tailTrace_3121260
  have hstable : (prefixWord ++ tailWord_3121260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121260).length < 2 ^ (prefixWord ++ tailWord_3121260).sum := by decide
  have hdescent : baseEnd_3121260 < baseStart_3121260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121281 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 4]
def baseStart_3121281 : Nat := 118140960795 + 3121281 * 2 ^ 59
def prefixEnd_3121281 : Nat := 4983230072969 + 3 ^ 40 * 3121281 * 2
def baseEnd_3121281 : Nat := 356159424610290601651777

theorem tailTrace_3121281 : CollatzResearch.WordTrace tailWord_3121281 prefixEnd_3121281 356159424610290601651777 := by
  unfold tailWord_3121281
  simp only [CollatzResearch.WordTrace]
  refine ⟨113842470605139484199851697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75894980403426322799901131 113842470605139484199851697)
  ·
    refine ⟨85381852953854613149888773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113842470605139484199851697 85381852953854613149888773)
    ·
      refine ⟨16009097428847739965604145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85381852953854613149888773 16009097428847739965604145)
      ·
        refine ⟨12006823071635804974203109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16009097428847739965604145 12006823071635804974203109)
        ·
          refine ⟨2251279325931713432663083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12006823071635804974203109 2251279325931713432663083)
          ·
            refine ⟨3376918988897570148994625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251279325931713432663083 3376918988897570148994625)
            ·
              refine ⟨2532689241673177611745969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376918988897570148994625 2532689241673177611745969)
              ·
                refine ⟨1899516931254883208809477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2532689241673177611745969 1899516931254883208809477)
                ·
                  refine ⟨356159424610290601651777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899516931254883208809477 356159424610290601651777)
                  ·
                    rfl

theorem cell22_3121281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_3121281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121281 prefixEnd_3121281 := by exact prefixLift 3121281
  have htrace : WordTrace (prefixWord ++ tailWord_3121281) baseStart_3121281 baseEnd_3121281 := by
    simpa [prefixWord, tailWord_3121281, baseEnd_3121281] using wordTrace_append hprefix tailTrace_3121281
  have hstable : (prefixWord ++ tailWord_3121281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121281).length < 2 ^ (prefixWord ++ tailWord_3121281).sum := by decide
  have hdescent : baseEnd_3121281 < baseStart_3121281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121393 : List Nat := [1, 2, 2, 2, 2, 1, 12]
def baseStart_3121393 : Nat := 118140960795 + 3121393 * 2 ^ 59
def prefixEnd_3121393 : Nat := 4983230072969 + 3 ^ 40 * 3121393 * 2
def baseEnd_3121393 : Nat := 39574689397027438746481

theorem tailTrace_3121393 : CollatzResearch.WordTrace tailWord_3121393 prefixEnd_3121393 39574689397027438746481 := by
  unfold tailWord_3121393
  simp only [CollatzResearch.WordTrace]
  refine ⟨113846555580733727327928833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75897703720489151551952555 113846555580733727327928833)
  ·
    refine ⟨85384916685550295495946625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113846555580733727327928833 85384916685550295495946625)
    ·
      refine ⟨64038687514162721621959969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85384916685550295495946625 64038687514162721621959969)
      ·
        refine ⟨48029015635622041216469977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64038687514162721621959969 48029015635622041216469977)
        ·
          refine ⟨36021761726716530912352483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48029015635622041216469977 36021761726716530912352483)
          ·
            refine ⟨54032642590074796368528725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36021761726716530912352483 54032642590074796368528725)
            ·
              refine ⟨39574689397027438746481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54032642590074796368528725 39574689397027438746481)
              ·
                rfl

theorem cell22_3121393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 12].length) (baseStart_3121393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121393 prefixEnd_3121393 := by exact prefixLift 3121393
  have htrace : WordTrace (prefixWord ++ tailWord_3121393) baseStart_3121393 baseEnd_3121393 := by
    simpa [prefixWord, tailWord_3121393, baseEnd_3121393] using wordTrace_append hprefix tailTrace_3121393
  have hstable : (prefixWord ++ tailWord_3121393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121393).length < 2 ^ (prefixWord ++ tailWord_3121393).sum := by decide
  have hdescent : baseEnd_3121393 < baseStart_3121393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121395 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 2, 4]
def baseStart_3121395 : Nat := 118140960795 + 3121395 * 2 ^ 59
def prefixEnd_3121395 : Nat := 4983230072969 + 3 ^ 40 * 3121395 * 2
def baseEnd_3121395 : Nat := 1068517298360613507604981

theorem tailTrace_3121395 : CollatzResearch.WordTrace tailWord_3121395 prefixEnd_3121395 1068517298360613507604981 := by
  unfold tailWord_3121395
  simp only [CollatzResearch.WordTrace]
  refine ⟨113846628526726481669501639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75897752351150987779667759 113846628526726481669501639)
  ·
    refine ⟨170769942790089722504252459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113846628526726481669501639 170769942790089722504252459)
    ·
      refine ⟨256154914185134583756378689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170769942790089722504252459 256154914185134583756378689)
      ·
        refine ⟨192116185638850937817284017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256154914185134583756378689 192116185638850937817284017)
        ·
          refine ⟨144087139229138203362963013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192116185638850937817284017 144087139229138203362963013)
          ·
            refine ⟨27016338605463413130555565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144087139229138203362963013 27016338605463413130555565)
            ·
              refine ⟨10131126977048779923958337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27016338605463413130555565 10131126977048779923958337)
              ·
                refine ⟨7598345232786584942968753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10131126977048779923958337 7598345232786584942968753)
                ·
                  refine ⟨5698758924589938707226565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7598345232786584942968753 5698758924589938707226565)
                  ·
                    refine ⟨1068517298360613507604981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5698758924589938707226565 1068517298360613507604981)
                    ·
                      rfl

theorem cell22_3121395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_3121395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121395 prefixEnd_3121395 := by exact prefixLift 3121395
  have htrace : WordTrace (prefixWord ++ tailWord_3121395) baseStart_3121395 baseEnd_3121395 := by
    simpa [prefixWord, tailWord_3121395, baseEnd_3121395] using wordTrace_append hprefix tailTrace_3121395
  have hstable : (prefixWord ++ tailWord_3121395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121395).length < 2 ^ (prefixWord ++ tailWord_3121395).sum := by decide
  have hdescent : baseEnd_3121395 < baseStart_3121395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121455 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 5]
def baseStart_3121455 : Nat := 118140960795 + 3121455 * 2 ^ 59
def prefixEnd_3121455 : Nat := 4983230072969 + 3 ^ 40 * 3121455 * 2
def baseEnd_3121455 : Nat := 356179279195597783701599

theorem tailTrace_3121455 : CollatzResearch.WordTrace tailWord_3121455 prefixEnd_3121455 356179279195597783701599 := by
  unfold tailWord_3121455
  simp only [CollatzResearch.WordTrace]
  refine ⟨113848816906509111916685819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75899211271006074611123879 113848816906509111916685819)
  ·
    refine ⟨170773225359763667875028729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113848816906509111916685819 170773225359763667875028729)
    ·
      refine ⟨128079919019822750906271547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170773225359763667875028729 128079919019822750906271547)
      ·
        refine ⟨192119878529734126359407321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128079919019822750906271547 192119878529734126359407321)
        ·
          refine ⟨144089908897300594769555491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192119878529734126359407321 144089908897300594769555491)
          ·
            refine ⟨216134863345950892154333237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144089908897300594769555491 216134863345950892154333237)
            ·
              refine ⟨20262643438682896139468741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216134863345950892154333237 20262643438682896139468741)
              ·
                refine ⟨3799245644753043026150389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20262643438682896139468741 3799245644753043026150389)
                ·
                  refine ⟨356179279195597783701599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3799245644753043026150389 356179279195597783701599)
                  ·
                    rfl

theorem cell22_3121455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 5].length) (baseStart_3121455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121455 prefixEnd_3121455 := by exact prefixLift 3121455
  have htrace : WordTrace (prefixWord ++ tailWord_3121455) baseStart_3121455 baseEnd_3121455 := by
    simpa [prefixWord, tailWord_3121455, baseEnd_3121455] using wordTrace_append hprefix tailTrace_3121455
  have hstable : (prefixWord ++ tailWord_3121455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121455).length < 2 ^ (prefixWord ++ tailWord_3121455).sum := by decide
  have hdescent : baseEnd_3121455 < baseStart_3121455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121459 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 1, 3]
def baseStart_3121459 : Nat := 118140960795 + 3121459 * 2 ^ 59
def prefixEnd_3121459 : Nat := 4983230072969 + 3 ^ 40 * 3121459 * 2
def baseEnd_3121459 : Nat := 1068539206868538674004785

theorem tailTrace_3121459 : CollatzResearch.WordTrace tailWord_3121459 prefixEnd_3121459 1068539206868538674004785 := by
  unfold tailWord_3121459
  simp only [CollatzResearch.WordTrace]
  refine ⟨113848962798494620599831431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75899308532329747066554287 113848962798494620599831431)
  ·
    refine ⟨170773444197741930899747147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113848962798494620599831431 170773444197741930899747147)
    ·
      refine ⟨256160166296612896349620721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170773444197741930899747147 256160166296612896349620721)
      ·
        refine ⟨192120124722459672262215541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256160166296612896349620721 192120124722459672262215541)
        ·
          refine ⟨18011261692730594274582707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192120124722459672262215541 18011261692730594274582707)
          ·
            refine ⟨27016892539095891411874061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18011261692730594274582707 27016892539095891411874061)
            ·
              refine ⟨10131334702160959279452773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27016892539095891411874061 10131334702160959279452773)
              ·
                refine ⟨1899625256655179864897395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10131334702160959279452773 1899625256655179864897395)
                ·
                  refine ⟨2849437884982769797346093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899625256655179864897395 2849437884982769797346093)
                  ·
                    refine ⟨1068539206868538674004785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849437884982769797346093 1068539206868538674004785)
                    ·
                      rfl

theorem cell22_3121459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 3].length) (baseStart_3121459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121459 prefixEnd_3121459 := by exact prefixLift 3121459
  have htrace : WordTrace (prefixWord ++ tailWord_3121459) baseStart_3121459 baseEnd_3121459 := by
    simpa [prefixWord, tailWord_3121459, baseEnd_3121459] using wordTrace_append hprefix tailTrace_3121459
  have hstable : (prefixWord ++ tailWord_3121459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121459).length < 2 ^ (prefixWord ++ tailWord_3121459).sum := by decide
  have hdescent : baseEnd_3121459 < baseStart_3121459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121476 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3121476 : Nat := 118140960795 + 3121476 * 2 ^ 59
def prefixEnd_3121476 : Nat := 4983230072969 + 3 ^ 40 * 3121476 * 2
def baseEnd_3121476 : Nat := 1068545026315956296329733

theorem tailTrace_3121476 : CollatzResearch.WordTrace tailWord_3121476 prefixEnd_3121476 1068545026315956296329733 := by
  unfold tailWord_3121476
  simp only [CollatzResearch.WordTrace]
  refine ⟨56924791419716516251600141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75899721892955355002133521 56924791419716516251600141)
  ·
    refine ⟨21346796782393693594350053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56924791419716516251600141 21346796782393693594350053)
    ·
      refine ⟨4002524396698817548940635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21346796782393693594350053 4002524396698817548940635)
      ·
        refine ⟨6003786595048226323410953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4002524396698817548940635 6003786595048226323410953)
        ·
          refine ⟨4502839946286169742558215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6003786595048226323410953 4502839946286169742558215)
          ·
            refine ⟨6754259919429254613837323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502839946286169742558215 6754259919429254613837323)
            ·
              refine ⟨10131389879143881920755985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754259919429254613837323 10131389879143881920755985)
              ·
                refine ⟨7598542409357911440566989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10131389879143881920755985 7598542409357911440566989)
                ·
                  refine ⟨2849453403509216790212621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7598542409357911440566989 2849453403509216790212621)
                  ·
                    refine ⟨1068545026315956296329733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849453403509216790212621 1068545026315956296329733)
                    ·
                      rfl

theorem cell22_3121476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3121476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121476 prefixEnd_3121476 := by exact prefixLift 3121476
  have htrace : WordTrace (prefixWord ++ tailWord_3121476) baseStart_3121476 baseEnd_3121476 := by
    simpa [prefixWord, tailWord_3121476, baseEnd_3121476] using wordTrace_append hprefix tailTrace_3121476
  have hstable : (prefixWord ++ tailWord_3121476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121476).length < 2 ^ (prefixWord ++ tailWord_3121476).sum := by decide
  have hdescent : baseEnd_3121476 < baseStart_3121476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121517 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3121517 : Nat := 118140960795 + 3121517 * 2 ^ 59
def prefixEnd_3121517 : Nat := 4983230072969 + 3 ^ 40 * 3121517 * 2
def baseEnd_3121517 : Nat := 356186353817948618684869

theorem tailTrace_3121517 : CollatzResearch.WordTrace tailWord_3121517 prefixEnd_3121517 356186353817948618684869 := by
  unfold tailWord_3121517
  simp only [CollatzResearch.WordTrace]
  refine ⟨113851078232284496505442805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75900718821522997670295203 113851078232284496505442805)
  ·
    refine ⟨10673538584276671547385263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113851078232284496505442805 10673538584276671547385263)
    ·
      refine ⟨16010307876415007321077895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673538584276671547385263 16010307876415007321077895)
      ·
        refine ⟨24015461814622510981616843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16010307876415007321077895 24015461814622510981616843)
        ·
          refine ⟨36023192721933766472425265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24015461814622510981616843 36023192721933766472425265)
          ·
            refine ⟨27017394541450324854318949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36023192721933766472425265 27017394541450324854318949)
            ·
              refine ⟨5065761476521935910184803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27017394541450324854318949 5065761476521935910184803)
              ·
                refine ⟨7598642214782903865277205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5065761476521935910184803 7598642214782903865277205)
                ·
                  refine ⟨356186353817948618684869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7598642214782903865277205 356186353817948618684869)
                  ·
                    rfl

theorem cell22_3121517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3121517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121517 prefixEnd_3121517 := by exact prefixLift 3121517
  have htrace : WordTrace (prefixWord ++ tailWord_3121517) baseStart_3121517 baseEnd_3121517 := by
    simpa [prefixWord, tailWord_3121517, baseEnd_3121517] using wordTrace_append hprefix tailTrace_3121517
  have hstable : (prefixWord ++ tailWord_3121517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121517).length < 2 ^ (prefixWord ++ tailWord_3121517).sum := by decide
  have hdescent : baseEnd_3121517 < baseStart_3121517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121562 : List Nat := [3, 1, 1, 4, 1, 4, 8]
def baseStart_3121562 : Nat := 118140960795 + 3121562 * 2 ^ 59
def prefixEnd_3121562 : Nat := 4983230072969 + 3 ^ 40 * 3121562 * 2
def baseEnd_3121562 : Nat := 39576832069388175506647

theorem tailTrace_3121562 : CollatzResearch.WordTrace tailWord_3121562 prefixEnd_3121562 39576832069388175506647 := by
  unfold tailWord_3121562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28463179879280367297707735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75901813011414312793887293 28463179879280367297707735)
  ·
    refine ⟨42694769818920550946561603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28463179879280367297707735 42694769818920550946561603)
    ·
      refine ⟨64042154728380826419842405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42694769818920550946561603 64042154728380826419842405)
      ·
        refine ⟨12007904011571404953720451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64042154728380826419842405 12007904011571404953720451)
        ·
          refine ⟨18011856017357107430580677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12007904011571404953720451 18011856017357107430580677)
          ·
            refine ⟨3377223003254457643233877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18011856017357107430580677 3377223003254457643233877)
            ·
              refine ⟨39576832069388175506647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3377223003254457643233877 39576832069388175506647)
              ·
                rfl

theorem cell22_3121562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 8].length) (baseStart_3121562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121562 prefixEnd_3121562 := by exact prefixLift 3121562
  have htrace : WordTrace (prefixWord ++ tailWord_3121562) baseStart_3121562 baseEnd_3121562 := by
    simpa [prefixWord, tailWord_3121562, baseEnd_3121562] using wordTrace_append hprefix tailTrace_3121562
  have hstable : (prefixWord ++ tailWord_3121562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121562).length < 2 ^ (prefixWord ++ tailWord_3121562).sum := by decide
  have hdescent : baseEnd_3121562 < baseStart_3121562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121566 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3121566 : Nat := 118140960795 + 3121566 * 2 ^ 59
def prefixEnd_3121566 : Nat := 4983230072969 + 3 ^ 40 * 3121566 * 2
def baseEnd_3121566 : Nat := 1068575835155226061579457

theorem tailTrace_3121566 : CollatzResearch.WordTrace tailWord_3121566 prefixEnd_3121566 1068575835155226061579457 := by
  unfold tailWord_3121566
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231608176138372234247069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75901910272737985249317701 14231608176138372234247069)
  ·
    refine ⟨5336853066051889587842651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14231608176138372234247069 5336853066051889587842651)
    ·
      refine ⟨8005279599077834381763977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5336853066051889587842651 8005279599077834381763977)
      ·
        refine ⟨6003959699308375786322983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8005279599077834381763977 6003959699308375786322983)
        ·
          refine ⟨9005939548962563679484475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003959699308375786322983 9005939548962563679484475)
          ·
            refine ⟨13508909323443845519226713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005939548962563679484475 13508909323443845519226713)
            ·
              refine ⟨10131681992582884139420035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13508909323443845519226713 10131681992582884139420035)
              ·
                refine ⟨15197522988874326209130053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10131681992582884139420035 15197522988874326209130053)
                ·
                  refine ⟨2849535560413936164211885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15197522988874326209130053 2849535560413936164211885)
                  ·
                    refine ⟨1068575835155226061579457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2849535560413936164211885 1068575835155226061579457)
                    ·
                      rfl

theorem cell22_3121566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3121566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121566 prefixEnd_3121566 := by exact prefixLift 3121566
  have htrace : WordTrace (prefixWord ++ tailWord_3121566) baseStart_3121566 baseEnd_3121566 := by
    simpa [prefixWord, tailWord_3121566, baseEnd_3121566] using wordTrace_append hprefix tailTrace_3121566
  have hstable : (prefixWord ++ tailWord_3121566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121566).length < 2 ^ (prefixWord ++ tailWord_3121566).sum := by decide
  have hdescent : baseEnd_3121566 < baseStart_3121566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121654 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3121654 : Nat := 118140960795 + 3121654 * 2 ^ 59
def prefixEnd_3121654 : Nat := 4983230072969 + 3 ^ 40 * 3121654 * 2
def baseEnd_3121654 : Nat := 1068605959353623165379187

theorem tailTrace_3121654 : CollatzResearch.WordTrace tailWord_3121654 prefixEnd_3121654 1068605959353623165379187 := by
  unfold tailWord_3121654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7116004689549260556448751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75904050021858779268786677 7116004689549260556448751)
  ·
    refine ⟨10674007034323890834673127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7116004689549260556448751 10674007034323890834673127)
    ·
      refine ⟨16011010551485836252009691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10674007034323890834673127 16011010551485836252009691)
      ·
        refine ⟨24016515827228754378014537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16011010551485836252009691 24016515827228754378014537)
        ·
          refine ⟨18012386870421565783510903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24016515827228754378014537 18012386870421565783510903)
          ·
            refine ⟨27018580305632348675266355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012386870421565783510903 27018580305632348675266355)
            ·
              refine ⟨40527870458448523012899533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27018580305632348675266355 40527870458448523012899533)
              ·
                refine ⟨15197951421918196129837325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40527870458448523012899533 15197951421918196129837325)
                ·
                  refine ⟨5699231783219323548688997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15197951421918196129837325 5699231783219323548688997)
                  ·
                    refine ⟨1068605959353623165379187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699231783219323548688997 1068605959353623165379187)
                    ·
                      rfl

theorem cell22_3121654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3121654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121654 prefixEnd_3121654 := by exact prefixLift 3121654
  have htrace : WordTrace (prefixWord ++ tailWord_3121654) baseStart_3121654 baseEnd_3121654 := by
    simpa [prefixWord, tailWord_3121654, baseEnd_3121654] using wordTrace_append hprefix tailTrace_3121654
  have hstable : (prefixWord ++ tailWord_3121654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121654).length < 2 ^ (prefixWord ++ tailWord_3121654).sum := by decide
  have hdescent : baseEnd_3121654 < baseStart_3121654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121667 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 1, 5]
def baseStart_3121667 : Nat := 118140960795 + 3121667 * 2 ^ 59
def prefixEnd_3121667 : Nat := 4983230072969 + 3 ^ 40 * 3121667 * 2
def baseEnd_3121667 : Nat := 1068610409519295464804147

theorem tailTrace_3121667 : CollatzResearch.WordTrace tailWord_3121667 prefixEnd_3121667 1068610409519295464804147 := by
  unfold tailWord_3121667
  simp only [CollatzResearch.WordTrace]
  refine ⟨113856549181741072123403255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75904366121160714748935503 113856549181741072123403255)
  ·
    refine ⟨170784823772611608185104883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113856549181741072123403255 170784823772611608185104883)
    ·
      refine ⟨256177235658917412277657325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170784823772611608185104883 256177235658917412277657325)
      ·
        refine ⟨96066463372094029604121497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256177235658917412277657325 96066463372094029604121497)
        ·
          refine ⟨72049847529070522203091123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96066463372094029604121497 72049847529070522203091123)
          ·
            refine ⟨108074771293605783304636685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72049847529070522203091123 108074771293605783304636685)
            ·
              refine ⟨40528039235102168739238757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108074771293605783304636685 40528039235102168739238757)
              ·
                refine ⟨7599007356581656638607267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40528039235102168739238757 7599007356581656638607267)
                ·
                  refine ⟨11398511034872484957910901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7599007356581656638607267 11398511034872484957910901)
                  ·
                    refine ⟨1068610409519295464804147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11398511034872484957910901 1068610409519295464804147)
                    ·
                      rfl

theorem cell22_3121667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_3121667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121667 prefixEnd_3121667 := by exact prefixLift 3121667
  have htrace : WordTrace (prefixWord ++ tailWord_3121667) baseStart_3121667 baseEnd_3121667 := by
    simpa [prefixWord, tailWord_3121667, baseEnd_3121667] using wordTrace_append hprefix tailTrace_3121667
  have hstable : (prefixWord ++ tailWord_3121667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121667).length < 2 ^ (prefixWord ++ tailWord_3121667).sum := by decide
  have hdescent : baseEnd_3121667 < baseStart_3121667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121669 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 4]
def baseStart_3121669 : Nat := 118140960795 + 3121669 * 2 ^ 59
def prefixEnd_3121669 : Nat := 4983230072969 + 3 ^ 40 * 3121669 * 2
def baseEnd_3121669 : Nat := 356203698053389375418047

theorem tailTrace_3121669 : CollatzResearch.WordTrace tailWord_3121669 prefixEnd_3121669 356203698053389375418047 := by
  unfold tailWord_3121669
  simp only [CollatzResearch.WordTrace]
  refine ⟨113856622127733826464976061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75904414751822550976650707 113856622127733826464976061)
  ·
    refine ⟨42696233297900184924366023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113856622127733826464976061 42696233297900184924366023)
    ·
      refine ⟨64044349946850277386549035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42696233297900184924366023 64044349946850277386549035)
      ·
        refine ⟨96066524920275416079823553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64044349946850277386549035 96066524920275416079823553)
        ·
          refine ⟨72049893690206562059867665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96066524920275416079823553 72049893690206562059867665)
          ·
            refine ⟨54037420267654921544900749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72049893690206562059867665 54037420267654921544900749)
            ·
              refine ⟨20264032600370595579337781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54037420267654921544900749 20264032600370595579337781)
              ·
                refine ⟨1899753056284743335562917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20264032600370595579337781 1899753056284743335562917)
                ·
                  refine ⟨356203698053389375418047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899753056284743335562917 356203698053389375418047)
                  ·
                    rfl

theorem cell22_3121669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_3121669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121669 prefixEnd_3121669 := by exact prefixLift 3121669
  have htrace : WordTrace (prefixWord ++ tailWord_3121669) baseStart_3121669 baseEnd_3121669 := by
    simpa [prefixWord, tailWord_3121669, baseEnd_3121669] using wordTrace_append hprefix tailTrace_3121669
  have hstable : (prefixWord ++ tailWord_3121669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121669).length < 2 ^ (prefixWord ++ tailWord_3121669).sum := by decide
  have hdescent : baseEnd_3121669 < baseStart_3121669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121671 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3121671 : Nat := 118140960795 + 3121671 * 2 ^ 59
def prefixEnd_3121671 : Nat := 4983230072969 + 3 ^ 40 * 3121671 * 2
def baseEnd_3121671 : Nat := 1068611778801040787704135

theorem tailTrace_3121671 : CollatzResearch.WordTrace tailWord_3121671 prefixEnd_3121671 1068611778801040787704135 := by
  unfold tailWord_3121671
  simp only [CollatzResearch.WordTrace]
  refine ⟨113856695073726580806548867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75904463382484387204365911 113856695073726580806548867)
  ·
    refine ⟨170785042610589871209823301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113856695073726580806548867 170785042610589871209823301)
    ·
      refine ⟨32022195489485600851841869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170785042610589871209823301 32022195489485600851841869)
      ·
        refine ⟨12008323308557100319440701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32022195489485600851841869 12008323308557100319440701)
        ·
          refine ⟨4503121240708912619790263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12008323308557100319440701 4503121240708912619790263)
          ·
            refine ⟨6754681861063368929685395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4503121240708912619790263 6754681861063368929685395)
            ·
              refine ⟨10132022791595053394528093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754681861063368929685395 10132022791595053394528093)
              ·
                refine ⟨3799508546848145022948035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10132022791595053394528093 3799508546848145022948035)
                ·
                  refine ⟨5699262820272217534422053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3799508546848145022948035 5699262820272217534422053)
                  ·
                    refine ⟨1068611778801040787704135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5699262820272217534422053 1068611778801040787704135)
                    ·
                      rfl

theorem cell22_3121671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3121671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121671 prefixEnd_3121671 := by exact prefixLift 3121671
  have htrace : WordTrace (prefixWord ++ tailWord_3121671) baseStart_3121671 baseEnd_3121671 := by
    simpa [prefixWord, tailWord_3121671, baseEnd_3121671] using wordTrace_append hprefix tailTrace_3121671
  have hstable : (prefixWord ++ tailWord_3121671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121671).length < 2 ^ (prefixWord ++ tailWord_3121671).sum := by decide
  have hdescent : baseEnd_3121671 < baseStart_3121671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3121697 : List Nat := [1, 2, 3, 2, 2, 1, 2, 9]
def baseStart_3121697 : Nat := 118140960795 + 3121697 * 2 ^ 59
def prefixEnd_3121697 : Nat := 4983230072969 + 3 ^ 40 * 3121697 * 2
def baseEnd_3121697 : Nat := 118735631014709487394895

theorem tailTrace_3121697 : CollatzResearch.WordTrace tailWord_3121697 prefixEnd_3121697 118735631014709487394895 := by
  unfold tailWord_3121697
  simp only [CollatzResearch.WordTrace]
  refine ⟨113857643371632387246995345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75905095581088258164663563 113857643371632387246995345)
  ·
    refine ⟨85393232528724290435246509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113857643371632387246995345 85393232528724290435246509)
    ·
      refine ⟨32022462198271608913217441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85393232528724290435246509 32022462198271608913217441)
      ·
        refine ⟨24016846648703706684913081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32022462198271608913217441 24016846648703706684913081)
        ·
          refine ⟨18012634986527780013684811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24016846648703706684913081 18012634986527780013684811)
          ·
            refine ⟨27018952479791670020527217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18012634986527780013684811 27018952479791670020527217)
            ·
              refine ⟨20264214359843752515395413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27018952479791670020527217 20264214359843752515395413)
              ·
                refine ⟨118735631014709487394895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20264214359843752515395413 118735631014709487394895)
                ·
                  rfl

theorem cell22_3121697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 9].length) (baseStart_3121697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3121697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3121697 prefixEnd_3121697 := by exact prefixLift 3121697
  have htrace : WordTrace (prefixWord ++ tailWord_3121697) baseStart_3121697 baseEnd_3121697 := by
    simpa [prefixWord, tailWord_3121697, baseEnd_3121697] using wordTrace_append hprefix tailTrace_3121697
  have hstable : (prefixWord ++ tailWord_3121697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3121697).length < 2 ^ (prefixWord ++ tailWord_3121697).sum := by decide
  have hdescent : baseEnd_3121697 < baseStart_3121697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3121697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
