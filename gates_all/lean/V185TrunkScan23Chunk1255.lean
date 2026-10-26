import V185TrunkScan23Chunk1254

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7434263 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7434263 : Nat := 118140960795 + 7434263 * 2 ^ 59
def prefixEnd_7434263 : Nat := 4983230072969 + 3 ^ 40 * 7434263 * 2
def baseEnd_7434263 : Nat := 3817350230936152145522953

theorem tailTrace_7434263 : CollatzResearch.WordTrace tailWord_7434263 prefixEnd_7434263 3817350230936152145522953 := by
  unfold tailWord_7434263
  simp only [CollatzResearch.WordTrace]
  refine ⟨271149847465942296881835443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180766564977294864587890295 271149847465942296881835443)
  ·
    refine ⟨406724771198913445322753165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271149847465942296881835443 406724771198913445322753165)
    ·
      refine ⟨152521789199592541996032437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406724771198913445322753165 152521789199592541996032437)
      ·
        refine ⟨14298917737461800812128041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152521789199592541996032437 14298917737461800812128041)
        ·
          refine ⟨10724188303096350609096031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14298917737461800812128041 10724188303096350609096031)
          ·
            refine ⟨16086282454644525913644047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724188303096350609096031 16086282454644525913644047)
            ·
              refine ⟨24129423681966788870466071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16086282454644525913644047 24129423681966788870466071)
              ·
                refine ⟨36194135522950183305699107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24129423681966788870466071 36194135522950183305699107)
                ·
                  refine ⟨54291203284425274958548661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36194135522950183305699107 54291203284425274958548661)
                  ·
                    refine ⟨5089800307914869527363937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54291203284425274958548661 5089800307914869527363937)
                    ·
                      refine ⟨3817350230936152145522953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089800307914869527363937 3817350230936152145522953)
                      ·
                        rfl

theorem cell23_7434263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7434263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434263 prefixEnd_7434263 := by exact prefixLift 7434263
  have htrace : WordTrace (prefixWord ++ tailWord_7434263) baseStart_7434263 baseEnd_7434263 := by
    simpa [prefixWord, tailWord_7434263, baseEnd_7434263] using wordTrace_append hprefix tailTrace_7434263
  have hstable : (prefixWord ++ tailWord_7434263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434263).length < 2 ^ (prefixWord ++ tailWord_7434263).sum := by decide
  have hdescent : baseEnd_7434263 < baseStart_7434263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434293 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_7434293 : Nat := 118140960795 + 7434293 * 2 ^ 59
def prefixEnd_7434293 : Nat := 4983230072969 + 3 ^ 40 * 7434293 * 2
def baseEnd_7434293 : Nat := 3817365635355787028147815

theorem tailTrace_7434293 : CollatzResearch.WordTrace tailWord_7434293 prefixEnd_7434293 3817365635355787028147815 := by
  unfold tailWord_7434293
  simp only [CollatzResearch.WordTrace]
  refine ⟨271150941655833612005427533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180767294437222408003618355 271150941655833612005427533)
  ·
    refine ⟨101681603120937604502035325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271150941655833612005427533 101681603120937604502035325)
    ·
      refine ⟨38130601170351601688263247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101681603120937604502035325 38130601170351601688263247)
      ·
        refine ⟨57195901755527402532394871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38130601170351601688263247 57195901755527402532394871)
        ·
          refine ⟨85793852633291103798592307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57195901755527402532394871 85793852633291103798592307)
          ·
            refine ⟨128690778949936655697888461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85793852633291103798592307 128690778949936655697888461)
            ·
              refine ⟨48259042106226245886708173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128690778949936655697888461 48259042106226245886708173)
              ·
                refine ⟨18097140789834842207515565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48259042106226245886708173 18097140789834842207515565)
                ·
                  refine ⟨6786427796188065827818337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18097140789834842207515565 6786427796188065827818337)
                  ·
                    refine ⟨5089820847141049370863753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6786427796188065827818337 5089820847141049370863753)
                    ·
                      refine ⟨3817365635355787028147815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089820847141049370863753 3817365635355787028147815)
                      ·
                        rfl

theorem cell23_7434293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_7434293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434293 prefixEnd_7434293 := by exact prefixLift 7434293
  have htrace : WordTrace (prefixWord ++ tailWord_7434293) baseStart_7434293 baseEnd_7434293 := by
    simpa [prefixWord, tailWord_7434293, baseEnd_7434293] using wordTrace_append hprefix tailTrace_7434293
  have hstable : (prefixWord ++ tailWord_7434293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434293).length < 2 ^ (prefixWord ++ tailWord_7434293).sum := by decide
  have hdescent : baseEnd_7434293 < baseStart_7434293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434296 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_7434296 : Nat := 118140960795 + 7434296 * 2 ^ 59
def prefixEnd_7434296 : Nat := 4983230072969 + 3 ^ 40 * 7434296 * 2
def baseEnd_7434296 : Nat := 3817367175797750516410301

theorem tailTrace_7434296 : CollatzResearch.WordTrace tailWord_7434296 prefixEnd_7434296 3817367175797750516410301 := by
  unfold tailWord_7434296
  simp only [CollatzResearch.WordTrace]
  refine ⟨135575525537411371758893371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180767367383215162345191161 135575525537411371758893371)
  ·
    refine ⟨203363288306117057638340057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135575525537411371758893371 203363288306117057638340057)
    ·
      refine ⟨152522466229587793228755043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203363288306117057638340057 152522466229587793228755043)
      ·
        refine ⟨228783699344381689843132565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152522466229587793228755043 228783699344381689843132565)
        ·
          refine ⟨10724235906767891711396839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228783699344381689843132565 10724235906767891711396839)
          ·
            refine ⟨16086353860151837567095259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724235906767891711396839 16086353860151837567095259)
            ·
              refine ⟨24129530790227756350642889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16086353860151837567095259 24129530790227756350642889)
              ·
                refine ⟨18097148092670817262982167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24129530790227756350642889 18097148092670817262982167)
                ·
                  refine ⟨27145722139006225894473251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18097148092670817262982167 27145722139006225894473251)
                  ·
                    refine ⟨40718583208509338841709877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27145722139006225894473251 40718583208509338841709877)
                    ·
                      refine ⟨3817367175797750516410301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40718583208509338841709877 3817367175797750516410301)
                      ·
                        rfl

theorem cell23_7434296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_7434296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434296 prefixEnd_7434296 := by exact prefixLift 7434296
  have htrace : WordTrace (prefixWord ++ tailWord_7434296) baseStart_7434296 baseEnd_7434296 := by
    simpa [prefixWord, tailWord_7434296, baseEnd_7434296] using wordTrace_append hprefix tailTrace_7434296
  have hstable : (prefixWord ++ tailWord_7434296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434296).length < 2 ^ (prefixWord ++ tailWord_7434296).sum := by decide
  have hdescent : baseEnd_7434296 < baseStart_7434296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434310 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_7434310 : Nat := 118140960795 + 7434310 * 2 ^ 59
def prefixEnd_7434310 : Nat := 4983230072969 + 3 ^ 40 * 7434310 * 2
def baseEnd_7434310 : Nat := 3817374364526913461635237

theorem tailTrace_7434310 : CollatzResearch.WordTrace tailWord_7434310 prefixEnd_7434310 3817374364526913461635237 := by
  unfold tailWord_7434310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473486303024125747149887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180767707797848015939197589 8473486303024125747149887)
  ·
    refine ⟨12710229454536188620724831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8473486303024125747149887 12710229454536188620724831)
    ·
      refine ⟨19065344181804282931087247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12710229454536188620724831 19065344181804282931087247)
      ·
        refine ⟨28598016272706424396630871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19065344181804282931087247 28598016272706424396630871)
        ·
          refine ⟨42897024409059636594946307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28598016272706424396630871 42897024409059636594946307)
          ·
            refine ⟨64345536613589454892419461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42897024409059636594946307 64345536613589454892419461)
            ·
              refine ⟨12064788115048022792328649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64345536613589454892419461 12064788115048022792328649)
              ·
                refine ⟨9048591086286017094246487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12064788115048022792328649 9048591086286017094246487)
                ·
                  refine ⟨13572886629429025641369731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048591086286017094246487 13572886629429025641369731)
                  ·
                    refine ⟨20359329944143538462054597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13572886629429025641369731 20359329944143538462054597)
                    ·
                      refine ⟨3817374364526913461635237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20359329944143538462054597 3817374364526913461635237)
                      ·
                        rfl

theorem cell23_7434310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_7434310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434310 prefixEnd_7434310 := by exact prefixLift 7434310
  have htrace : WordTrace (prefixWord ++ tailWord_7434310) baseStart_7434310 baseEnd_7434310 := by
    simpa [prefixWord, tailWord_7434310, baseEnd_7434310] using wordTrace_append hprefix tailTrace_7434310
  have hstable : (prefixWord ++ tailWord_7434310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434310).length < 2 ^ (prefixWord ++ tailWord_7434310).sum := by decide
  have hdescent : baseEnd_7434310 < baseStart_7434310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434343 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_7434343 : Nat := 118140960795 + 7434343 * 2 ^ 59
def prefixEnd_7434343 : Nat := 4983230072969 + 3 ^ 40 * 7434343 * 2
def baseEnd_7434343 : Nat := 3817391309388511832522585

theorem tailTrace_7434343 : CollatzResearch.WordTrace tailWord_7434343 prefixEnd_7434343 3817391309388511832522585 := by
  unfold tailWord_7434343
  simp only [CollatzResearch.WordTrace]
  refine ⟨271152765305652470544747683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180768510203768313696498455 271152765305652470544747683)
  ·
    refine ⟨406729147958478705817121525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271152765305652470544747683 406729147958478705817121525)
    ·
      refine ⟨38130857621107378670355143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406729147958478705817121525 38130857621107378670355143)
      ·
        refine ⟨57196286431661068005532715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38130857621107378670355143 57196286431661068005532715)
        ·
          refine ⟨85794429647491602008299073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57196286431661068005532715 85794429647491602008299073)
          ·
            refine ⟨64345822235618701506224305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85794429647491602008299073 64345822235618701506224305)
            ·
              refine ⟨48259366676714026129668229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64345822235618701506224305 48259366676714026129668229)
              ·
                refine ⟨9048631251883879899312793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48259366676714026129668229 9048631251883879899312793)
                ·
                  refine ⟨6786473438912909924484595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9048631251883879899312793 6786473438912909924484595)
                  ·
                    refine ⟨10179710158369364886726893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786473438912909924484595 10179710158369364886726893)
                    ·
                      refine ⟨3817391309388511832522585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10179710158369364886726893 3817391309388511832522585)
                      ·
                        rfl

theorem cell23_7434343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_7434343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434343 prefixEnd_7434343 := by exact prefixLift 7434343
  have htrace : WordTrace (prefixWord ++ tailWord_7434343) baseStart_7434343 baseEnd_7434343 := by
    simpa [prefixWord, tailWord_7434343, baseEnd_7434343] using wordTrace_append hprefix tailTrace_7434343
  have hstable : (prefixWord ++ tailWord_7434343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434343).length < 2 ^ (prefixWord ++ tailWord_7434343).sum := by decide
  have hdescent : baseEnd_7434343 < baseStart_7434343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434379 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4]
def baseStart_7434379 : Nat := 118140960795 + 7434379 * 2 ^ 59
def prefixEnd_7434379 : Nat := 4983230072969 + 3 ^ 40 * 7434379 * 2
def baseEnd_7434379 : Nat := 3817409794692073691672419

theorem tailTrace_7434379 : CollatzResearch.WordTrace tailWord_7434379 prefixEnd_7434379 3817409794692073691672419 := by
  unfold tailWord_7434379
  simp only [CollatzResearch.WordTrace]
  refine ⟨271154078333522048693058191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180769385555681365795372127 271154078333522048693058191)
  ·
    refine ⟨406731117500283073039587287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271154078333522048693058191 406731117500283073039587287)
    ·
      refine ⟨610096676250424609559380931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406731117500283073039587287 610096676250424609559380931)
      ·
        refine ⟨915145014375636914339071397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610096676250424609559380931 915145014375636914339071397)
        ·
          refine ⟨171589690195431921438575887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 915145014375636914339071397 171589690195431921438575887)
          ·
            refine ⟨257384535293147882157863831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171589690195431921438575887 257384535293147882157863831)
            ·
              refine ⟨386076802939721823236795747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257384535293147882157863831 386076802939721823236795747)
              ·
                refine ⟨579115204409582734855193621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386076802939721823236795747 579115204409582734855193621)
                ·
                  refine ⟨27146025206699190696337201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 579115204409582734855193621 27146025206699190696337201)
                  ·
                    refine ⟨20359518905024393022252901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27146025206699190696337201 20359518905024393022252901)
                    ·
                      refine ⟨3817409794692073691672419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20359518905024393022252901 3817409794692073691672419)
                      ·
                        rfl

theorem cell23_7434379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_7434379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434379 prefixEnd_7434379 := by exact prefixLift 7434379
  have htrace : WordTrace (prefixWord ++ tailWord_7434379) baseStart_7434379 baseEnd_7434379 := by
    simpa [prefixWord, tailWord_7434379, baseEnd_7434379] using wordTrace_append hprefix tailTrace_7434379
  have hstable : (prefixWord ++ tailWord_7434379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434379).length < 2 ^ (prefixWord ++ tailWord_7434379).sum := by decide
  have hdescent : baseEnd_7434379 < baseStart_7434379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434386 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7434386 : Nat := 118140960795 + 7434386 * 2 ^ 59
def prefixEnd_7434386 : Nat := 4983230072969 + 3 ^ 40 * 7434386 * 2
def baseEnd_7434386 : Nat := 3817413389056655164284887

theorem tailTrace_7434386 : CollatzResearch.WordTrace tailWord_7434386 prefixEnd_7434386 3817413389056655164284887 := by
  unfold tailWord_7434386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67788583411124172222140753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180769555762997792592375341 67788583411124172222140753)
  ·
    refine ⟨50841437558343129166605565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67788583411124172222140753 50841437558343129166605565)
    ·
      refine ⟨19065539084378673437477087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50841437558343129166605565 19065539084378673437477087)
      ·
        refine ⟨28598308626568010156215631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19065539084378673437477087 28598308626568010156215631)
        ·
          refine ⟨42897462939852015234323447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28598308626568010156215631 42897462939852015234323447)
          ·
            refine ⟨64346194409778022851485171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42897462939852015234323447 64346194409778022851485171)
            ·
              refine ⟨96519291614667034277227757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64346194409778022851485171 96519291614667034277227757)
              ·
                refine ⟨36194734355500137853960409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96519291614667034277227757 36194734355500137853960409)
                ·
                  refine ⟨27146050766625103390470307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36194734355500137853960409 27146050766625103390470307)
                  ·
                    refine ⟨40719076149937655085705461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27146050766625103390470307 40719076149937655085705461)
                    ·
                      refine ⟨3817413389056655164284887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40719076149937655085705461 3817413389056655164284887)
                      ·
                        rfl

theorem cell23_7434386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7434386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434386 prefixEnd_7434386 := by exact prefixLift 7434386
  have htrace : WordTrace (prefixWord ++ tailWord_7434386) baseStart_7434386 baseEnd_7434386 := by
    simpa [prefixWord, tailWord_7434386, baseEnd_7434386] using wordTrace_append hprefix tailTrace_7434386
  have hstable : (prefixWord ++ tailWord_7434386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434386).length < 2 ^ (prefixWord ++ tailWord_7434386).sum := by decide
  have hdescent : baseEnd_7434386 < baseStart_7434386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434396 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7434396 : Nat := 118140960795 + 7434396 * 2 ^ 59
def prefixEnd_7434396 : Nat := 4983230072969 + 3 ^ 40 * 7434396 * 2
def baseEnd_7434396 : Nat := 3817418523863200125159841

theorem tailTrace_7434396 : CollatzResearch.WordTrace tailWord_7434396 prefixEnd_7434396 3817418523863200125159841 := by
  unfold tailWord_7434396
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577349187230230298213521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180769798916306973730951361 135577349187230230298213521)
  ·
    refine ⟨101683011890422672723660141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135577349187230230298213521 101683011890422672723660141)
    ·
      refine ⟨38131129458908502271372553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101683011890422672723660141 38131129458908502271372553)
      ·
        refine ⟨28598347094181376703529415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38131129458908502271372553 28598347094181376703529415)
        ·
          refine ⟨42897520641272065055294123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28598347094181376703529415 42897520641272065055294123)
          ·
            refine ⟨64346280961908097582941185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42897520641272065055294123 64346280961908097582941185)
            ·
              refine ⟨48259710721431073187205889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64346280961908097582941185 48259710721431073187205889)
              ·
                refine ⟨36194783041073304890404417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48259710721431073187205889 36194783041073304890404417)
                ·
                  refine ⟨27146087280804978667803313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36194783041073304890404417 27146087280804978667803313)
                  ·
                    refine ⟨20359565460603734000852485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27146087280804978667803313 20359565460603734000852485)
                    ·
                      refine ⟨3817418523863200125159841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20359565460603734000852485 3817418523863200125159841)
                      ·
                        rfl

theorem cell23_7434396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7434396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434396 prefixEnd_7434396 := by exact prefixLift 7434396
  have htrace : WordTrace (prefixWord ++ tailWord_7434396) baseStart_7434396 baseEnd_7434396 := by
    simpa [prefixWord, tailWord_7434396, baseEnd_7434396] using wordTrace_append hprefix tailTrace_7434396
  have hstable : (prefixWord ++ tailWord_7434396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434396).length < 2 ^ (prefixWord ++ tailWord_7434396).sum := by decide
  have hdescent : baseEnd_7434396 < baseStart_7434396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434400 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 2, 2, 2]
def baseStart_7434400 : Nat := 118140960795 + 7434400 * 2 ^ 59
def prefixEnd_7434400 : Nat := 4983230072969 + 3 ^ 40 * 7434400 * 2
def baseEnd_7434400 : Nat := 3817420577785818109509823

theorem tailTrace_7434400 : CollatzResearch.WordTrace tailWord_7434400 prefixEnd_7434400 3817420577785818109509823 := by
  unfold tailWord_7434400
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577422133222984639786327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180769896177630646186381769 135577422133222984639786327)
  ·
    refine ⟨203366133199834476959679491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135577422133222984639786327 203366133199834476959679491)
    ·
      refine ⟨305049199799751715439519237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203366133199834476959679491 305049199799751715439519237)
      ·
        refine ⟨57196724962453446644909857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305049199799751715439519237 57196724962453446644909857)
        ·
          refine ⟨42897543721840084983682393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57196724962453446644909857 42897543721840084983682393)
          ·
            refine ⟨32173157791380063737761795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42897543721840084983682393 32173157791380063737761795)
            ·
              refine ⟨48259736687070095606642693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32173157791380063737761795 48259736687070095606642693)
              ·
                refine ⟨9048700628825642926245505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48259736687070095606642693 9048700628825642926245505)
                ·
                  refine ⟨6786525471619232194684129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9048700628825642926245505 6786525471619232194684129)
                  ·
                    refine ⟨5089894103714424146013097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6786525471619232194684129 5089894103714424146013097)
                    ·
                      refine ⟨3817420577785818109509823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5089894103714424146013097 3817420577785818109509823)
                      ·
                        rfl

theorem cell23_7434400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_7434400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434400 prefixEnd_7434400 := by exact prefixLift 7434400
  have htrace : WordTrace (prefixWord ++ tailWord_7434400) baseStart_7434400 baseEnd_7434400 := by
    simpa [prefixWord, tailWord_7434400, baseEnd_7434400] using wordTrace_append hprefix tailTrace_7434400
  have hstable : (prefixWord ++ tailWord_7434400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434400).length < 2 ^ (prefixWord ++ tailWord_7434400).sum := by decide
  have hdescent : baseEnd_7434400 < baseStart_7434400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434413 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7434413 : Nat := 118140960795 + 7434413 * 2 ^ 59
def prefixEnd_7434413 : Nat := 4983230072969 + 3 ^ 40 * 7434413 * 2
def baseEnd_7434413 : Nat := 3817427253034326558647263

theorem tailTrace_7434413 : CollatzResearch.WordTrace tailWord_7434413 prefixEnd_7434413 3817427253034326558647263 := by
  unfold tailWord_7434413
  simp only [CollatzResearch.WordTrace]
  refine ⟨271155318415398872499795893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180770212276932581666530595 271155318415398872499795893)
  ·
    refine ⟨25420811101443644296855865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271155318415398872499795893 25420811101443644296855865)
    ·
      refine ⟨19065608326082733222641899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25420811101443644296855865 19065608326082733222641899)
      ·
        refine ⟨28598412489124099833962849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19065608326082733222641899 28598412489124099833962849)
        ·
          refine ⟨21448809366843074875472137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28598412489124099833962849 21448809366843074875472137)
          ·
            refine ⟨16086607025132306156604103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21448809366843074875472137 16086607025132306156604103)
            ·
              refine ⟨24129910537698459234906155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16086607025132306156604103 24129910537698459234906155)
              ·
                refine ⟨36194865806547688852359233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24129910537698459234906155 36194865806547688852359233)
                ·
                  refine ⟨27146149354910766639269425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36194865806547688852359233 27146149354910766639269425)
                  ·
                    refine ⟨20359612016183074979452069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27146149354910766639269425 20359612016183074979452069)
                    ·
                      refine ⟨3817427253034326558647263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20359612016183074979452069 3817427253034326558647263)
                      ·
                        rfl

theorem cell23_7434413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7434413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434413 prefixEnd_7434413 := by exact prefixLift 7434413
  have htrace : WordTrace (prefixWord ++ tailWord_7434413) baseStart_7434413 baseEnd_7434413 := by
    simpa [prefixWord, tailWord_7434413, baseEnd_7434413] using wordTrace_append hprefix tailTrace_7434413
  have hstable : (prefixWord ++ tailWord_7434413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434413).length < 2 ^ (prefixWord ++ tailWord_7434413).sum := by decide
  have hdescent : baseEnd_7434413 < baseStart_7434413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434419 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 1, 7]
def baseStart_7434419 : Nat := 118140960795 + 7434419 * 2 ^ 59
def prefixEnd_7434419 : Nat := 4983230072969 + 3 ^ 40 * 7434419 * 2
def baseEnd_7434419 : Nat := 1272476777972751178390745

theorem tailTrace_7434419 : CollatzResearch.WordTrace tailWord_7434419 prefixEnd_7434419 1272476777972751178390745 := by
  unfold tailWord_7434419
  simp only [CollatzResearch.WordTrace]
  refine ⟨271155537253377135524514311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180770358168918090349676207 271155537253377135524514311)
  ·
    refine ⟨406733305880065703286771467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271155537253377135524514311 406733305880065703286771467)
    ·
      refine ⟨610099958820098554930157201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406733305880065703286771467 610099958820098554930157201)
      ·
        refine ⟨457574969115073916197617901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610099958820098554930157201 457574969115073916197617901)
        ·
          refine ⟨171590613418152718574106713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457574969115073916197617901 171590613418152718574106713)
          ·
            refine ⟨128692960063614538930580035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171590613418152718574106713 128692960063614538930580035)
            ·
              refine ⟨193039440095421808395870053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128692960063614538930580035 193039440095421808395870053)
              ·
                refine ⟨36194895017891589074225635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193039440095421808395870053 36194895017891589074225635)
                ·
                  refine ⟨54292342526837383611338453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36194895017891589074225635 54292342526837383611338453)
                  ·
                    refine ⟨1272476777972751178390745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54292342526837383611338453 1272476777972751178390745)
                    ·
                      rfl

theorem cell23_7434419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 7].length) (baseStart_7434419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434419 prefixEnd_7434419 := by exact prefixLift 7434419
  have htrace : WordTrace (prefixWord ++ tailWord_7434419) baseStart_7434419 baseEnd_7434419 := by
    simpa [prefixWord, tailWord_7434419, baseEnd_7434419] using wordTrace_append hprefix tailTrace_7434419
  have hstable : (prefixWord ++ tailWord_7434419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434419).length < 2 ^ (prefixWord ++ tailWord_7434419).sum := by decide
  have hdescent : baseEnd_7434419 < baseStart_7434419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434459 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_7434459 : Nat := 118140960795 + 7434459 * 2 ^ 59
def prefixEnd_7434459 : Nat := 4983230072969 + 3 ^ 40 * 7434459 * 2
def baseEnd_7434459 : Nat := 3817450873144433378672051

theorem tailTrace_7434459 : CollatzResearch.WordTrace tailWord_7434459 prefixEnd_7434459 3817450873144433378672051 := by
  unfold tailWord_7434459
  simp only [CollatzResearch.WordTrace]
  refine ⟨271156996173232222355970431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180771330782154814903980287 271156996173232222355970431)
  ·
    refine ⟨406735494259848333533955647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271156996173232222355970431 406735494259848333533955647)
    ·
      refine ⟨610103241389772500300933471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406735494259848333533955647 610103241389772500300933471)
      ·
        refine ⟨915154862084658750451400207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610103241389772500300933471 915154862084658750451400207)
        ·
          refine ⟨1372732293126988125677100311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915154862084658750451400207 1372732293126988125677100311)
          ·
            refine ⟨2059098439690482188515650467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372732293126988125677100311 2059098439690482188515650467)
            ·
              refine ⟨3088647659535723282773475701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059098439690482188515650467 3088647659535723282773475701)
              ·
                refine ⟨289560718081474057760013347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3088647659535723282773475701 289560718081474057760013347)
                ·
                  refine ⟨434341077122211086640020021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289560718081474057760013347 434341077122211086640020021)
                  ·
                    refine ⟨40719475980207289372501877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 434341077122211086640020021 40719475980207289372501877)
                    ·
                      refine ⟨3817450873144433378672051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40719475980207289372501877 3817450873144433378672051)
                      ·
                        rfl

theorem cell23_7434459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_7434459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434459 prefixEnd_7434459 := by exact prefixLift 7434459
  have htrace : WordTrace (prefixWord ++ tailWord_7434459) baseStart_7434459 baseEnd_7434459 := by
    simpa [prefixWord, tailWord_7434459, baseEnd_7434459] using wordTrace_append hprefix tailTrace_7434459
  have hstable : (prefixWord ++ tailWord_7434459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434459).length < 2 ^ (prefixWord ++ tailWord_7434459).sum := by decide
  have hdescent : baseEnd_7434459 < baseStart_7434459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434476 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_7434476 : Nat := 118140960795 + 7434476 * 2 ^ 59
def prefixEnd_7434476 : Nat := 4983230072969 + 3 ^ 40 * 7434476 * 2
def baseEnd_7434476 : Nat := 3817459602315559812159473

theorem tailTrace_7434476 : CollatzResearch.WordTrace tailWord_7434476 prefixEnd_7434476 3817459602315559812159473 := by
  unfold tailWord_7434476
  simp only [CollatzResearch.WordTrace]
  refine ⟨135578808107085317129669641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180771744142780422839559521 135578808107085317129669641)
  ·
    refine ⟨101684106080313987847252231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135578808107085317129669641 101684106080313987847252231)
    ·
      refine ⟨152526159120470981770878347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101684106080313987847252231 152526159120470981770878347)
      ·
        refine ⟨228789238680706472656317521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152526159120470981770878347 228789238680706472656317521)
        ·
          refine ⟨171591929010529854492238141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228789238680706472656317521 171591929010529854492238141)
          ·
            refine ⟨64346973378948695434589303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171591929010529854492238141 64346973378948695434589303)
            ·
              refine ⟨96520460068423043151883955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64346973378948695434589303 96520460068423043151883955)
              ·
                refine ⟨144780690102634564727825933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96520460068423043151883955 144780690102634564727825933)
                ·
                  refine ⟨54292758788487961772934725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144780690102634564727825933 54292758788487961772934725)
                  ·
                    refine ⟨10179892272841492832425261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54292758788487961772934725 10179892272841492832425261)
                    ·
                      refine ⟨3817459602315559812159473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10179892272841492832425261 3817459602315559812159473)
                      ·
                        rfl

theorem cell23_7434476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_7434476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434476 prefixEnd_7434476 := by exact prefixLift 7434476
  have htrace : WordTrace (prefixWord ++ tailWord_7434476) baseStart_7434476 baseEnd_7434476 := by
    simpa [prefixWord, tailWord_7434476, baseEnd_7434476] using wordTrace_append hprefix tailTrace_7434476
  have hstable : (prefixWord ++ tailWord_7434476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434476).length < 2 ^ (prefixWord ++ tailWord_7434476).sum := by decide
  have hdescent : baseEnd_7434476 < baseStart_7434476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434530 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_7434530 : Nat := 118140960795 + 7434530 * 2 ^ 59
def prefixEnd_7434530 : Nat := 4983230072969 + 3 ^ 40 * 7434530 * 2
def baseEnd_7434530 : Nat := 424165258918989177876025

theorem tailTrace_7434530 : CollatzResearch.WordTrace tailWord_7434530 prefixEnd_7434530 424165258918989177876025 := by
  unfold tailWord_7434530
  simp only [CollatzResearch.WordTrace]
  refine ⟨67789896438993750370451261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180773057170650000987870029 67789896438993750370451261)
  ·
    refine ⟨25421211164622656388919223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67789896438993750370451261 25421211164622656388919223)
    ·
      refine ⟨38131816746933984583378835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25421211164622656388919223 38131816746933984583378835)
      ·
        refine ⟨57197725120400976875068253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38131816746933984583378835 57197725120400976875068253)
        ·
          refine ⟨21449146920150366328150595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57197725120400976875068253 21449146920150366328150595)
          ·
            refine ⟨32173720380225549492225893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21449146920150366328150595 32173720380225549492225893)
            ·
              refine ⟨6032572571292290529792355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32173720380225549492225893 6032572571292290529792355)
              ·
                refine ⟨9048858856938435794688533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032572571292290529792355 9048858856938435794688533)
                ·
                  refine ⟨424165258918989177876025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9048858856938435794688533 424165258918989177876025)
                  ·
                    rfl

theorem cell23_7434530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_7434530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434530 prefixEnd_7434530 := by exact prefixLift 7434530
  have htrace : WordTrace (prefixWord ++ tailWord_7434530) baseStart_7434530 baseEnd_7434530 := by
    simpa [prefixWord, tailWord_7434530, baseEnd_7434530] using wordTrace_append hprefix tailTrace_7434530
  have hstable : (prefixWord ++ tailWord_7434530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434530).length < 2 ^ (prefixWord ++ tailWord_7434530).sum := by decide
  have hdescent : baseEnd_7434530 < baseStart_7434530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434543 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 1, 5]
def baseStart_7434543 : Nat := 118140960795 + 7434543 * 2 ^ 59
def prefixEnd_7434543 : Nat := 4983230072969 + 3 ^ 40 * 7434543 * 2
def baseEnd_7434543 : Nat := 1272498001839803683340555

theorem tailTrace_7434543 : CollatzResearch.WordTrace tailWord_7434543 prefixEnd_7434543 1272498001839803683340555 := by
  unfold tailWord_7434543
  simp only [CollatzResearch.WordTrace]
  refine ⟨271160059904927904702028283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180773373269951936468018855 271160059904927904702028283)
  ·
    refine ⟨406740089857391857053042425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271160059904927904702028283 406740089857391857053042425)
    ·
      refine ⟨305055067393043892789781819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406740089857391857053042425 305055067393043892789781819)
      ·
        refine ⟨457582601089565839184672729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305055067393043892789781819 457582601089565839184672729)
        ·
          refine ⟨343186950817174379388504547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457582601089565839184672729 343186950817174379388504547)
          ·
            refine ⟨514780426225761569082756821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343186950817174379388504547 514780426225761569082756821)
            ·
              refine ⟨12065166239666286775377113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 514780426225761569082756821 12065166239666286775377113)
              ·
                refine ⟨9048874679749715081532835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12065166239666286775377113 9048874679749715081532835)
                ·
                  refine ⟨13573312019624572622299253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048874679749715081532835 13573312019624572622299253)
                  ·
                    refine ⟨1272498001839803683340555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13573312019624572622299253 1272498001839803683340555)
                    ·
                      rfl

theorem cell23_7434543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_7434543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434543 prefixEnd_7434543 := by exact prefixLift 7434543
  have htrace : WordTrace (prefixWord ++ tailWord_7434543) baseStart_7434543 baseEnd_7434543 := by
    simpa [prefixWord, tailWord_7434543, baseEnd_7434543] using wordTrace_append hprefix tailTrace_7434543
  have hstable : (prefixWord ++ tailWord_7434543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434543).length < 2 ^ (prefixWord ++ tailWord_7434543).sum := by decide
  have hdescent : baseEnd_7434543 < baseStart_7434543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434563 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4]
def baseStart_7434563 : Nat := 118140960795 + 7434563 * 2 ^ 59
def prefixEnd_7434563 : Nat := 4983230072969 + 3 ^ 40 * 7434563 * 2
def baseEnd_7434563 : Nat := 3817504275132500971771573

theorem tailTrace_7434563 : CollatzResearch.WordTrace tailWord_7434563 prefixEnd_7434563 3817504275132500971771573 := by
  unfold tailWord_7434563
  simp only [CollatzResearch.WordTrace]
  refine ⟨271160789364855448117756343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180773859576570298745170895 271160789364855448117756343)
  ·
    refine ⟨406741184047283172176634515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271160789364855448117756343 406741184047283172176634515)
    ·
      refine ⟨610111776070924758264951773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406741184047283172176634515 610111776070924758264951773)
      ·
        refine ⟨228791916026596784349356915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610111776070924758264951773 228791916026596784349356915)
        ·
          refine ⟨343187874039895176524035373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228791916026596784349356915 343187874039895176524035373)
          ·
            refine ⟨128695452764960691196513265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343187874039895176524035373 128695452764960691196513265)
            ·
              refine ⟨96521589573720518397384949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128695452764960691196513265 96521589573720518397384949)
              ·
                refine ⟨9048899022536298599754839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96521589573720518397384949 9048899022536298599754839)
                ·
                  refine ⟨13573348533804447899632259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048899022536298599754839 13573348533804447899632259)
                  ·
                    refine ⟨20360022800706671849448389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13573348533804447899632259 20360022800706671849448389)
                    ·
                      refine ⟨3817504275132500971771573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20360022800706671849448389 3817504275132500971771573)
                      ·
                        rfl

theorem cell23_7434563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_7434563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434563 prefixEnd_7434563 := by exact prefixLift 7434563
  have htrace : WordTrace (prefixWord ++ tailWord_7434563) baseStart_7434563 baseEnd_7434563 := by
    simpa [prefixWord, tailWord_7434563, baseEnd_7434563] using wordTrace_append hprefix tailTrace_7434563
  have hstable : (prefixWord ++ tailWord_7434563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434563).length < 2 ^ (prefixWord ++ tailWord_7434563).sum := by decide
  have hdescent : baseEnd_7434563 < baseStart_7434563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434583 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_7434583 : Nat := 118140960795 + 7434583 * 2 ^ 59
def prefixEnd_7434583 : Nat := 4983230072969 + 3 ^ 40 * 7434583 * 2
def baseEnd_7434583 : Nat := 3817514544745590893521481

theorem tailTrace_7434583 : CollatzResearch.WordTrace tailWord_7434583 prefixEnd_7434583 3817514544745590893521481 := by
  unfold tailWord_7434583
  simp only [CollatzResearch.WordTrace]
  refine ⟨271161518824782991533484403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180774345883188661022322935 271161518824782991533484403)
  ·
    refine ⟨406742278237174487300226605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271161518824782991533484403 406742278237174487300226605)
    ·
      refine ⟨152528354338940432737584977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406742278237174487300226605 152528354338940432737584977)
      ·
        refine ⟨114396265754205324553188733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152528354338940432737584977 114396265754205324553188733)
        ·
          refine ⟨42898599657826996707445775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114396265754205324553188733 42898599657826996707445775)
          ·
            refine ⟨64347899486740495061168663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42898599657826996707445775 64347899486740495061168663)
            ·
              refine ⟨96521849230110742591752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64347899486740495061168663 96521849230110742591752995)
              ·
                refine ⟨144782773845166113887629493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96521849230110742591752995 144782773845166113887629493)
                ·
                  refine ⟨13573385047984323176965265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144782773845166113887629493 13573385047984323176965265)
                  ·
                    refine ⟨10180038785988242382723949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13573385047984323176965265 10180038785988242382723949)
                    ·
                      refine ⟨3817514544745590893521481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180038785988242382723949 3817514544745590893521481)
                      ·
                        rfl

theorem cell23_7434583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_7434583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434583 prefixEnd_7434583 := by exact prefixLift 7434583
  have htrace : WordTrace (prefixWord ++ tailWord_7434583) baseStart_7434583 baseEnd_7434583 := by
    simpa [prefixWord, tailWord_7434583, baseEnd_7434583] using wordTrace_append hprefix tailTrace_7434583
  have hstable : (prefixWord ++ tailWord_7434583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434583).length < 2 ^ (prefixWord ++ tailWord_7434583).sum := by decide
  have hdescent : baseEnd_7434583 < baseStart_7434583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434597 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 3, 2, 2]
def baseStart_7434597 : Nat := 118140960795 + 7434597 * 2 ^ 59
def prefixEnd_7434597 : Nat := 4983230072969 + 3 ^ 40 * 7434597 * 2
def baseEnd_7434597 : Nat := 3817521733474753838746417

theorem tailTrace_7434597 : CollatzResearch.WordTrace tailWord_7434597 prefixEnd_7434597 3817521733474753838746417 := by
  unfold tailWord_7434597
  simp only [CollatzResearch.WordTrace]
  refine ⟨271162029446732271924494045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180774686297821514616329363 271162029446732271924494045)
  ·
    refine ⟨101685761042524601971685267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271162029446732271924494045 101685761042524601971685267)
    ·
      refine ⟨152528641563786902957527901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101685761042524601971685267 152528641563786902957527901)
      ·
        refine ⟨57198240586420088609072963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152528641563786902957527901 57198240586420088609072963)
        ·
          refine ⟨85797360879630132913609445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57198240586420088609072963 85797360879630132913609445)
          ·
            refine ⟨16087005164930649921301771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85797360879630132913609445 16087005164930649921301771)
            ·
              refine ⟨24130507747395974881952657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16087005164930649921301771 24130507747395974881952657)
              ·
                refine ⟨18097880810546981161464493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24130507747395974881952657 18097880810546981161464493)
                ·
                  refine ⟨6786705303955117935549185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18097880810546981161464493 6786705303955117935549185)
                  ·
                    refine ⟨5090028977966338451661889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6786705303955117935549185 5090028977966338451661889)
                    ·
                      refine ⟨3817521733474753838746417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090028977966338451661889 3817521733474753838746417)
                      ·
                        rfl

theorem cell23_7434597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_7434597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434597 prefixEnd_7434597 := by exact prefixLift 7434597
  have htrace : WordTrace (prefixWord ++ tailWord_7434597) baseStart_7434597 baseEnd_7434597 := by
    simpa [prefixWord, tailWord_7434597, baseEnd_7434597] using wordTrace_append hprefix tailTrace_7434597
  have hstable : (prefixWord ++ tailWord_7434597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434597).length < 2 ^ (prefixWord ++ tailWord_7434597).sum := by decide
  have hdescent : baseEnd_7434597 < baseStart_7434597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434600 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_7434600 : Nat := 118140960795 + 7434600 * 2 ^ 59
def prefixEnd_7434600 : Nat := 4983230072969 + 3 ^ 40 * 7434600 * 2
def baseEnd_7434600 : Nat := 3817523273916717327008903

theorem tailTrace_7434600 : CollatzResearch.WordTrace tailWord_7434600 prefixEnd_7434600 3817523273916717327008903 := by
  unfold tailWord_7434600
  simp only [CollatzResearch.WordTrace]
  refine ⟨135581069432860701718426627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180774759243814268957902169 135581069432860701718426627)
  ·
    refine ⟨203371604149291052577639941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135581069432860701718426627 203371604149291052577639941)
    ·
      refine ⟨38132175777992072358307489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203371604149291052577639941 38132175777992072358307489)
      ·
        refine ⟨28599131833494054268730617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38132175777992072358307489 28599131833494054268730617)
        ·
          refine ⟨21449348875120540701547963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28599131833494054268730617 21449348875120540701547963)
          ·
            refine ⟨32174023312680811052321945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21449348875120540701547963 32174023312680811052321945)
            ·
              refine ⟨24130517484510608289241459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32174023312680811052321945 24130517484510608289241459)
              ·
                refine ⟨36195776226765912433862189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24130517484510608289241459 36195776226765912433862189)
                ·
                  refine ⟨13573416085037217162698321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36195776226765912433862189 13573416085037217162698321)
                  ·
                    refine ⟨10180062063777912872023741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13573416085037217162698321 10180062063777912872023741)
                    ·
                      refine ⟨3817523273916717327008903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180062063777912872023741 3817523273916717327008903)
                      ·
                        rfl

theorem cell23_7434600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_7434600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434600 prefixEnd_7434600 := by exact prefixLift 7434600
  have htrace : WordTrace (prefixWord ++ tailWord_7434600) baseStart_7434600 baseEnd_7434600 := by
    simpa [prefixWord, tailWord_7434600, baseEnd_7434600] using wordTrace_append hprefix tailTrace_7434600
  have hstable : (prefixWord ++ tailWord_7434600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434600).length < 2 ^ (prefixWord ++ tailWord_7434600).sum := by decide
  have hdescent : baseEnd_7434600 < baseStart_7434600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434614 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7434614 : Nat := 118140960795 + 7434614 * 2 ^ 59
def prefixEnd_7434614 : Nat := 4983230072969 + 3 ^ 40 * 7434614 * 2
def baseEnd_7434614 : Nat := 3817530462645880272233839

theorem tailTrace_7434614 : CollatzResearch.WordTrace tailWord_7434614 prefixEnd_7434614 3817530462645880272233839 := by
  unfold tailWord_7434614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16947665592979417739241431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180775099658447122551908597 16947665592979417739241431)
  ·
    refine ⟨25421498389469126608862147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16947665592979417739241431 25421498389469126608862147)
    ·
      refine ⟨38132247584203689913293221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25421498389469126608862147 38132247584203689913293221)
      ·
        refine ⟨7149796422038191858742479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38132247584203689913293221 7149796422038191858742479)
        ·
          refine ⟨10724694633057287788113719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149796422038191858742479 10724694633057287788113719)
          ·
            refine ⟨16087041949585931682170579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724694633057287788113719 16087041949585931682170579)
            ·
              refine ⟨24130562924378897523255869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16087041949585931682170579 24130562924378897523255869)
              ·
                refine ⟨9048961096642086571220951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24130562924378897523255869 9048961096642086571220951)
                ·
                  refine ⟨13573441644963129856831427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048961096642086571220951 13573441644963129856831427)
                  ·
                    refine ⟨20360162467444694785247141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13573441644963129856831427 20360162467444694785247141)
                    ·
                      refine ⟨3817530462645880272233839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20360162467444694785247141 3817530462645880272233839)
                      ·
                        rfl

theorem cell23_7434614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7434614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434614 prefixEnd_7434614 := by exact prefixLift 7434614
  have htrace : WordTrace (prefixWord ++ tailWord_7434614) baseStart_7434614 baseEnd_7434614 := by
    simpa [prefixWord, tailWord_7434614, baseEnd_7434614] using wordTrace_append hprefix tailTrace_7434614
  have hstable : (prefixWord ++ tailWord_7434614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434614).length < 2 ^ (prefixWord ++ tailWord_7434614).sum := by decide
  have hdescent : baseEnd_7434614 < baseStart_7434614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434644 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7434644 : Nat := 118140960795 + 7434644 * 2 ^ 59
def prefixEnd_7434644 : Nat := 4983230072969 + 3 ^ 40 * 7434644 * 2
def baseEnd_7434644 : Nat := 3817545867065515154858701

theorem tailTrace_7434644 : CollatzResearch.WordTrace tailWord_7434644 prefixEnd_7434644 3817545867065515154858701 := by
  unfold tailWord_7434644
  simp only [CollatzResearch.WordTrace]
  refine ⟨135581871838780999475727493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180775829118374665967636657 135581871838780999475727493)
  ·
    refine ⟨25421600969771437401698905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135581871838780999475727493 25421600969771437401698905)
    ·
      refine ⟨19066200727328578051274179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25421600969771437401698905 19066200727328578051274179)
      ·
        refine ⟨28599301090992867076911269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19066200727328578051274179 28599301090992867076911269)
        ·
          refine ⟨5362368954561162576920863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28599301090992867076911269 5362368954561162576920863)
          ·
            refine ⟨8043553431841743865381295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362368954561162576920863 8043553431841743865381295)
            ·
              refine ⟨12065330147762615798071943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043553431841743865381295 12065330147762615798071943)
              ·
                refine ⟨18097995221643923697107915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12065330147762615798071943 18097995221643923697107915)
                ·
                  refine ⟨27146992832465885545661873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18097995221643923697107915 27146992832465885545661873)
                  ·
                    refine ⟨20360244624349414159246405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27146992832465885545661873 20360244624349414159246405)
                    ·
                      refine ⟨3817545867065515154858701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20360244624349414159246405 3817545867065515154858701)
                      ·
                        rfl

theorem cell23_7434644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7434644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434644 prefixEnd_7434644 := by exact prefixLift 7434644
  have htrace : WordTrace (prefixWord ++ tailWord_7434644) baseStart_7434644 baseEnd_7434644 := by
    simpa [prefixWord, tailWord_7434644, baseEnd_7434644] using wordTrace_append hprefix tailTrace_7434644
  have hstable : (prefixWord ++ tailWord_7434644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434644).length < 2 ^ (prefixWord ++ tailWord_7434644).sum := by decide
  have hdescent : baseEnd_7434644 < baseStart_7434644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434673 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7434673 : Nat := 118140960795 + 7434673 * 2 ^ 59
def prefixEnd_7434673 : Nat := 4983230072969 + 3 ^ 40 * 7434673 * 2
def baseEnd_7434673 : Nat := 3817560758004495541396067

theorem tailTrace_7434673 : CollatzResearch.WordTrace tailWord_7434673 prefixEnd_7434673 3817560758004495541396067 := by
  unfold tailWord_7434673
  simp only [CollatzResearch.WordTrace]
  refine ⟨271164801394456936904260673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180776534262971291269507115 271164801394456936904260673)
  ·
    refine ⟨203373601045842702678195505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271164801394456936904260673 203373601045842702678195505)
    ·
      refine ⟨152530200784382027008646629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203373601045842702678195505 152530200784382027008646629)
      ·
        refine ⟨28599412647071630064121243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152530200784382027008646629 28599412647071630064121243)
        ·
          refine ⟨42899118970607445096181865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28599412647071630064121243 42899118970607445096181865)
          ·
            refine ⟨32174339227955583822136399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42899118970607445096181865 32174339227955583822136399)
            ·
              refine ⟨48261508841933375733204599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32174339227955583822136399 48261508841933375733204599)
              ·
                refine ⟨72392263262900063599806899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48261508841933375733204599 72392263262900063599806899)
                ·
                  refine ⟨108588394894350095399710349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72392263262900063599806899 108588394894350095399710349)
                  ·
                    refine ⟨40720648085381285774891381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108588394894350095399710349 40720648085381285774891381)
                    ·
                      refine ⟨3817560758004495541396067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40720648085381285774891381 3817560758004495541396067)
                      ·
                        rfl

theorem cell23_7434673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7434673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434673 prefixEnd_7434673 := by exact prefixLift 7434673
  have htrace : WordTrace (prefixWord ++ tailWord_7434673) baseStart_7434673 baseEnd_7434673 := by
    simpa [prefixWord, tailWord_7434673, baseEnd_7434673] using wordTrace_append hprefix tailTrace_7434673
  have hstable : (prefixWord ++ tailWord_7434673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434673).length < 2 ^ (prefixWord ++ tailWord_7434673).sum := by decide
  have hdescent : baseEnd_7434673 < baseStart_7434673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434703 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_7434703 : Nat := 118140960795 + 7434703 * 2 ^ 59
def prefixEnd_7434703 : Nat := 4983230072969 + 3 ^ 40 * 7434703 * 2
def baseEnd_7434703 : Nat := 3817576162424130424020929

theorem tailTrace_7434703 : CollatzResearch.WordTrace tailWord_7434703 prefixEnd_7434703 3817576162424130424020929 := by
  unfold tailWord_7434703
  simp only [CollatzResearch.WordTrace]
  refine ⟨271165895584348252027852763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180777263722898834685235175 271165895584348252027852763)
  ·
    refine ⟨406748843376522378041779145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271165895584348252027852763 406748843376522378041779145)
    ·
      refine ⟨305061632532391783531334359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406748843376522378041779145 305061632532391783531334359)
      ·
        refine ⟨457592448798587675297001539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305061632532391783531334359 457592448798587675297001539)
        ·
          refine ⟨686388673197881512945502309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457592448798587675297001539 686388673197881512945502309)
          ·
            refine ⟨128697876224602783677281683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 686388673197881512945502309 128697876224602783677281683)
            ·
              refine ⟨193046814336904175515922525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128697876224602783677281683 193046814336904175515922525)
              ·
                refine ⟨72392555376339065818470947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193046814336904175515922525 72392555376339065818470947)
                ·
                  refine ⟨108588833064508598727706421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72392555376339065818470947 108588833064508598727706421)
                  ·
                    refine ⟨10180203099797681130722477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108588833064508598727706421 10180203099797681130722477)
                    ·
                      refine ⟨3817576162424130424020929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180203099797681130722477 3817576162424130424020929)
                      ·
                        rfl

theorem cell23_7434703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_7434703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434703 prefixEnd_7434703 := by exact prefixLift 7434703
  have htrace : WordTrace (prefixWord ++ tailWord_7434703) baseStart_7434703 baseEnd_7434703 := by
    simpa [prefixWord, tailWord_7434703, baseEnd_7434703] using wordTrace_append hprefix tailTrace_7434703
  have hstable : (prefixWord ++ tailWord_7434703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434703).length < 2 ^ (prefixWord ++ tailWord_7434703).sum := by decide
  have hdescent : baseEnd_7434703 < baseStart_7434703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434710 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7434710 : Nat := 118140960795 + 7434710 * 2 ^ 59
def prefixEnd_7434710 : Nat := 4983230072969 + 3 ^ 40 * 7434710 * 2
def baseEnd_7434710 : Nat := 424175528532079099625933

theorem tailTrace_7434710 : CollatzResearch.WordTrace tailWord_7434710 prefixEnd_7434710 424175528532079099625933 := by
  unfold tailWord_7434710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16947884430957680763959849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180777433930215261482238389 16947884430957680763959849)
  ·
    refine ⟨12710913323218260572969887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16947884430957680763959849 12710913323218260572969887)
    ·
      refine ⟨19066369984827390859454831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12710913323218260572969887 19066369984827390859454831)
      ·
        refine ⟨28599554977241086289182247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19066369984827390859454831 28599554977241086289182247)
        ·
          refine ⟨42899332465861629433773371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28599554977241086289182247 42899332465861629433773371)
          ·
            refine ⟨64348998698792444150660057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42899332465861629433773371 64348998698792444150660057)
            ·
              refine ⟨48261749024094333112995043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64348998698792444150660057 48261749024094333112995043)
              ·
                refine ⟨72392623536141499669492565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48261749024094333112995043 72392623536141499669492565)
                ·
                  refine ⟨424175528532079099625933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72392623536141499669492565 424175528532079099625933)
                  ·
                    rfl

theorem cell23_7434710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7434710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434710 prefixEnd_7434710 := by exact prefixLift 7434710
  have htrace : WordTrace (prefixWord ++ tailWord_7434710) baseStart_7434710 baseEnd_7434710 := by
    simpa [prefixWord, tailWord_7434710, baseEnd_7434710] using wordTrace_append hprefix tailTrace_7434710
  have hstable : (prefixWord ++ tailWord_7434710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434710).length < 2 ^ (prefixWord ++ tailWord_7434710).sum := by decide
  have hdescent : baseEnd_7434710 < baseStart_7434710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434754 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7434754 : Nat := 118140960795 + 7434754 * 2 ^ 59
def prefixEnd_7434754 : Nat := 4983230072969 + 3 ^ 40 * 7434754 * 2
def baseEnd_7434754 : Nat := 3817602349937509724483195

theorem tailTrace_7434754 : CollatzResearch.WordTrace tailWord_7434754 prefixEnd_7434754 3817602349937509724483195 := by
  unfold tailWord_7434754
  simp only [CollatzResearch.WordTrace]
  refine ⟨67791938926790871934489829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180778503804775658491972877 67791938926790871934489829)
  ·
    refine ⟨12710988548773288487716843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67791938926790871934489829 12710988548773288487716843)
    ·
      refine ⟨19066482823159932731575265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12710988548773288487716843 19066482823159932731575265)
      ·
        refine ⟨14299862117369949548681449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19066482823159932731575265 14299862117369949548681449)
        ·
          refine ⟨10724896588027462161511087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14299862117369949548681449 10724896588027462161511087)
          ·
            refine ⟨16087344882041193242266631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724896588027462161511087 16087344882041193242266631)
            ·
              refine ⟨24131017323061789863399947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16087344882041193242266631 24131017323061789863399947)
              ·
                refine ⟨36196525984592684795099921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24131017323061789863399947 36196525984592684795099921)
                ·
                  refine ⟨27147394488444513596324941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36196525984592684795099921 27147394488444513596324941)
                  ·
                    refine ⟨10180272933166692598621853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27147394488444513596324941 10180272933166692598621853)
                    ·
                      refine ⟨3817602349937509724483195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180272933166692598621853 3817602349937509724483195)
                      ·
                        rfl

theorem cell23_7434754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7434754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434754 prefixEnd_7434754 := by exact prefixLift 7434754
  have htrace : WordTrace (prefixWord ++ tailWord_7434754) baseStart_7434754 baseEnd_7434754 := by
    simpa [prefixWord, tailWord_7434754, baseEnd_7434754] using wordTrace_append hprefix tailTrace_7434754
  have hstable : (prefixWord ++ tailWord_7434754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434754).length < 2 ^ (prefixWord ++ tailWord_7434754).sum := by decide
  have hdescent : baseEnd_7434754 < baseStart_7434754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434783 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 8]
def baseStart_7434783 : Nat := 118140960795 + 7434783 * 2 ^ 59
def prefixEnd_7434783 : Nat := 4983230072969 + 3 ^ 40 * 7434783 * 2
def baseEnd_7434783 : Nat := 424179693430721123446729

theorem tailTrace_7434783 : CollatzResearch.WordTrace tailWord_7434783 prefixEnd_7434783 424179693430721123446729 := by
  unfold tailWord_7434783
  simp only [CollatzResearch.WordTrace]
  refine ⟨271168813424058425690765003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180779208949372283793843335 271168813424058425690765003)
  ·
    refine ⟨406753220136087638536147505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271168813424058425690765003 406753220136087638536147505)
    ·
      refine ⟨305064915102065728902110629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406753220136087638536147505 305064915102065728902110629)
      ·
        refine ⟨57199671581637324169145743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305064915102065728902110629 57199671581637324169145743)
        ·
          refine ⟨85799507372455986253718615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57199671581637324169145743 85799507372455986253718615)
          ·
            refine ⟨128699261058683979380577923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85799507372455986253718615 128699261058683979380577923)
            ·
              refine ⟨193048891588025969070866885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128699261058683979380577923 193048891588025969070866885)
              ·
                refine ⟨36196667172754869200787541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193048891588025969070866885 36196667172754869200787541)
                ·
                  refine ⟨424179693430721123446729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36196667172754869200787541 424179693430721123446729)
                  ·
                    rfl

theorem cell23_7434783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 8].length) (baseStart_7434783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434783 prefixEnd_7434783 := by exact prefixLift 7434783
  have htrace : WordTrace (prefixWord ++ tailWord_7434783) baseStart_7434783 baseEnd_7434783 := by
    simpa [prefixWord, tailWord_7434783, baseEnd_7434783] using wordTrace_append hprefix tailTrace_7434783
  have hstable : (prefixWord ++ tailWord_7434783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434783).length < 2 ^ (prefixWord ++ tailWord_7434783).sum := by decide
  have hdescent : baseEnd_7434783 < baseStart_7434783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434800 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 6]
def baseStart_7434800 : Nat := 118140960795 + 7434800 * 2 ^ 59
def prefixEnd_7434800 : Nat := 4983230072969 + 3 ^ 40 * 7434800 * 2
def baseEnd_7434800 : Nat := 424180663338624060500887

theorem tailTrace_7434800 : CollatzResearch.WordTrace tailWord_7434800 prefixEnd_7434800 424180663338624060500887 := by
  unfold tailWord_7434800
  simp only [CollatzResearch.WordTrace]
  refine ⟨135584716732498418797066927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180779622309997891729422569 135584716732498418797066927)
  ·
    refine ⟨203377075098747628195600391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135584716732498418797066927 203377075098747628195600391)
    ·
      refine ⟨305065612648121442293400587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203377075098747628195600391 305065612648121442293400587)
      ·
        refine ⟨457598418972182163440100881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305065612648121442293400587 457598418972182163440100881)
        ·
          refine ⟨343198814229136622580075661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457598418972182163440100881 343198814229136622580075661)
          ·
            refine ⟨128699555335926233467528373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343198814229136622580075661 128699555335926233467528373)
            ·
              refine ⟨12065583312743084387580785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128699555335926233467528373 12065583312743084387580785)
              ·
                refine ⟨9049187484557313290685589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12065583312743084387580785 9049187484557313290685589)
                ·
                  refine ⟨424180663338624060500887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9049187484557313290685589 424180663338624060500887)
                  ·
                    rfl

theorem cell23_7434800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_7434800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434800 prefixEnd_7434800 := by exact prefixLift 7434800
  have htrace : WordTrace (prefixWord ++ tailWord_7434800) baseStart_7434800 baseEnd_7434800 := by
    simpa [prefixWord, tailWord_7434800, baseEnd_7434800] using wordTrace_append hprefix tailTrace_7434800
  have hstable : (prefixWord ++ tailWord_7434800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434800).length < 2 ^ (prefixWord ++ tailWord_7434800).sum := by decide
  have hdescent : baseEnd_7434800 < baseStart_7434800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434803 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_7434803 : Nat := 118140960795 + 7434803 * 2 ^ 59
def prefixEnd_7434803 : Nat := 4983230072969 + 3 ^ 40 * 7434803 * 2
def baseEnd_7434803 : Nat := 3817627510489580032770469

theorem tailTrace_7434803 : CollatzResearch.WordTrace tailWord_7434803 prefixEnd_7434803 3817627510489580032770469 := by
  unfold tailWord_7434803
  simp only [CollatzResearch.WordTrace]
  refine ⟨271169542883985969106493063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180779695255990646070995375 271169542883985969106493063)
  ·
    refine ⟨406754314325978953659739595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271169542883985969106493063 406754314325978953659739595)
    ·
      refine ⟨610131471488968430489609393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406754314325978953659739595 610131471488968430489609393)
      ·
        refine ⟨457598603616726322867207045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610131471488968430489609393 457598603616726322867207045)
        ·
          refine ⟨85799738178136185537601321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457598603616726322867207045 85799738178136185537601321)
          ·
            refine ⟨64349803633602139153200991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85799738178136185537601321 64349803633602139153200991)
            ·
              refine ⟨96524705450403208729801487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64349803633602139153200991 96524705450403208729801487)
              ·
                refine ⟨144787058175604813094702231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96524705450403208729801487 144787058175604813094702231)
                ·
                  refine ⟨217180587263407219642053347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144787058175604813094702231 217180587263407219642053347)
                  ·
                    refine ⟨325770880895110829463080021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217180587263407219642053347 325770880895110829463080021)
                    ·
                      refine ⟨3817627510489580032770469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 325770880895110829463080021 3817627510489580032770469)
                      ·
                        rfl

theorem cell23_7434803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_7434803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434803 prefixEnd_7434803 := by exact prefixLift 7434803
  have htrace : WordTrace (prefixWord ++ tailWord_7434803) baseStart_7434803 baseEnd_7434803 := by
    simpa [prefixWord, tailWord_7434803, baseEnd_7434803] using wordTrace_append hprefix tailTrace_7434803
  have hstable : (prefixWord ++ tailWord_7434803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434803).length < 2 ^ (prefixWord ++ tailWord_7434803).sum := by decide
  have hdescent : baseEnd_7434803 < baseStart_7434803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434827 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 3]
def baseStart_7434827 : Nat := 118140960795 + 7434827 * 2 ^ 59
def prefixEnd_7434827 : Nat := 4983230072969 + 3 ^ 40 * 7434827 * 2
def baseEnd_7434827 : Nat := 3817639834025287938870359

theorem tailTrace_7434827 : CollatzResearch.WordTrace tailWord_7434827 prefixEnd_7434827 3817639834025287938870359 := by
  unfold tailWord_7434827
  simp only [CollatzResearch.WordTrace]
  refine ⟨271170418235899021205366735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180780278823932680803577823 271170418235899021205366735)
  ·
    refine ⟨406755627353848531808050103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271170418235899021205366735 406755627353848531808050103)
    ·
      refine ⟨610133441030772797712075155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406755627353848531808050103 610133441030772797712075155)
      ·
        refine ⟨915200161546159196568112733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610133441030772797712075155 915200161546159196568112733)
        ·
          refine ⟨343200060579809698713042275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 915200161546159196568112733 343200060579809698713042275)
          ·
            refine ⟨514800090869714548069563413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343200060579809698713042275 514800090869714548069563413)
            ·
              refine ⟨24131254259517869440760785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 514800090869714548069563413 24131254259517869440760785)
              ·
                refine ⟨18098440694638402080570589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24131254259517869440760785 18098440694638402080570589)
                ·
                  refine ⟨6786915260489400780213971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18098440694638402080570589 6786915260489400780213971)
                  ·
                    refine ⟨10180372890734101170320957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786915260489400780213971 10180372890734101170320957)
                    ·
                      refine ⟨3817639834025287938870359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180372890734101170320957 3817639834025287938870359)
                      ·
                        rfl

theorem cell23_7434827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 3].length) (baseStart_7434827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434827 prefixEnd_7434827 := by exact prefixLift 7434827
  have htrace : WordTrace (prefixWord ++ tailWord_7434827) baseStart_7434827 baseEnd_7434827 := by
    simpa [prefixWord, tailWord_7434827, baseEnd_7434827] using wordTrace_append hprefix tailTrace_7434827
  have hstable : (prefixWord ++ tailWord_7434827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434827).length < 2 ^ (prefixWord ++ tailWord_7434827).sum := by decide
  have hdescent : baseEnd_7434827 < baseStart_7434827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434830 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_7434830 : Nat := 118140960795 + 7434830 * 2 ^ 59
def prefixEnd_7434830 : Nat := 4983230072969 + 3 ^ 40 * 7434830 * 2
def baseEnd_7434830 : Nat := 1272547124822417142377615

theorem tailTrace_7434830 : CollatzResearch.WordTrace tailWord_7434830 prefixEnd_7434830 1272547124822417142377615 := by
  unfold tailWord_7434830
  simp only [CollatzResearch.WordTrace]
  refine ⟨33896315956861019089715743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180780351769925435145150629 33896315956861019089715743)
  ·
    refine ⟨50844473935291528634573615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33896315956861019089715743 50844473935291528634573615)
    ·
      refine ⟨76266710902937292951860423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50844473935291528634573615 76266710902937292951860423)
      ·
        refine ⟨114400066354405939427790635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76266710902937292951860423 114400066354405939427790635)
        ·
          refine ⟨171600099531608909141685953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114400066354405939427790635 171600099531608909141685953)
          ·
            refine ⟨128700074648706681856264465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171600099531608909141685953 128700074648706681856264465)
            ·
              refine ⟨96525055986530011392198349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128700074648706681856264465 96525055986530011392198349)
              ·
                refine ⟨36196895994948754272074381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96525055986530011392198349 36196895994948754272074381)
                ·
                  refine ⟨13573835998105782852027893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36196895994948754272074381 13573835998105782852027893)
                  ·
                    refine ⟨1272547124822417142377615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13573835998105782852027893 1272547124822417142377615)
                    ·
                      rfl

theorem cell23_7434830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_7434830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434830 prefixEnd_7434830 := by exact prefixLift 7434830
  have htrace : WordTrace (prefixWord ++ tailWord_7434830) baseStart_7434830 baseEnd_7434830 := by
    simpa [prefixWord, tailWord_7434830, baseEnd_7434830] using wordTrace_append hprefix tailTrace_7434830
  have hstable : (prefixWord ++ tailWord_7434830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434830).length < 2 ^ (prefixWord ++ tailWord_7434830).sum := by decide
  have hdescent : baseEnd_7434830 < baseStart_7434830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434837 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_7434837 : Nat := 118140960795 + 7434837 * 2 ^ 59
def prefixEnd_7434837 : Nat := 4983230072969 + 3 ^ 40 * 7434837 * 2
def baseEnd_7434837 : Nat := 3817644968831832899745313

theorem tailTrace_7434837 : CollatzResearch.WordTrace tailWord_7434837 prefixEnd_7434837 3817644968831832899745313 := by
  unfold tailWord_7434837
  simp only [CollatzResearch.WordTrace]
  refine ⟨271170782965862792913230765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180780521977241861942153843 271170782965862792913230765)
  ·
    refine ⟨101689043612198547342461537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271170782965862792913230765 101689043612198547342461537)
    ·
      refine ⟨76266782709148910506846153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101689043612198547342461537 76266782709148910506846153)
      ·
        refine ⟨57200087031861682880134615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76266782709148910506846153 57200087031861682880134615)
        ·
          refine ⟨85800130547792524320201923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57200087031861682880134615 85800130547792524320201923)
          ·
            refine ⟨128700195821688786480302885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85800130547792524320201923 128700195821688786480302885)
            ·
              refine ⟨24131286716566647465056791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128700195821688786480302885 24131286716566647465056791)
              ·
                refine ⟨36196930074849971197585187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24131286716566647465056791 36196930074849971197585187)
                ·
                  refine ⟨54295395112274956796377781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36196930074849971197585187 54295395112274956796377781)
                  ·
                    refine ⟨5090193291775777199660417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54295395112274956796377781 5090193291775777199660417)
                    ·
                      refine ⟨3817644968831832899745313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090193291775777199660417 3817644968831832899745313)
                      ·
                        rfl

theorem cell23_7434837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_7434837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434837 prefixEnd_7434837 := by exact prefixLift 7434837
  have htrace : WordTrace (prefixWord ++ tailWord_7434837) baseStart_7434837 baseEnd_7434837 := by
    simpa [prefixWord, tailWord_7434837, baseEnd_7434837] using wordTrace_append hprefix tailTrace_7434837
  have hstable : (prefixWord ++ tailWord_7434837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434837).length < 2 ^ (prefixWord ++ tailWord_7434837).sum := by decide
  have hdescent : baseEnd_7434837 < baseStart_7434837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434861 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_7434861 : Nat := 118140960795 + 7434861 * 2 ^ 59
def prefixEnd_7434861 : Nat := 4983230072969 + 3 ^ 40 * 7434861 * 2
def baseEnd_7434861 : Nat := 3817657292367540805845203

theorem tailTrace_7434861 : CollatzResearch.WordTrace tailWord_7434861 prefixEnd_7434861 3817657292367540805845203 := by
  unfold tailWord_7434861
  simp only [CollatzResearch.WordTrace]
  refine ⟨271171658317775845012104437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180781105545183896674736291 271171658317775845012104437)
  ·
    refine ⟨25422342967291485469884791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271171658317775845012104437 25422342967291485469884791)
    ·
      refine ⟨38133514450937228204827187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25422342967291485469884791 38133514450937228204827187)
      ·
        refine ⟨57200271676405842307240781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38133514450937228204827187 57200271676405842307240781)
        ·
          refine ⟨21450101878652190865215293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57200271676405842307240781 21450101878652190865215293)
          ·
            refine ⟨8043788204494571574455735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21450101878652190865215293 8043788204494571574455735)
            ·
              refine ⟨12065682306741857361683603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043788204494571574455735 12065682306741857361683603)
              ·
                refine ⟨18098523460112786042525405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12065682306741857361683603 18098523460112786042525405)
                ·
                  refine ⟨6786946297542294765947027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18098523460112786042525405 6786946297542294765947027)
                  ·
                    refine ⟨10180419446313442148920541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786946297542294765947027 10180419446313442148920541)
                    ·
                      refine ⟨3817657292367540805845203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180419446313442148920541 3817657292367540805845203)
                      ·
                        rfl

theorem cell23_7434861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_7434861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434861 prefixEnd_7434861 := by exact prefixLift 7434861
  have htrace : WordTrace (prefixWord ++ tailWord_7434861) baseStart_7434861 baseEnd_7434861 := by
    simpa [prefixWord, tailWord_7434861, baseEnd_7434861] using wordTrace_append hprefix tailTrace_7434861
  have hstable : (prefixWord ++ tailWord_7434861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434861).length < 2 ^ (prefixWord ++ tailWord_7434861).sum := by decide
  have hdescent : baseEnd_7434861 < baseStart_7434861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434880 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_7434880 : Nat := 118140960795 + 7434880 * 2 ^ 59
def prefixEnd_7434880 : Nat := 4983230072969 + 3 ^ 40 * 7434880 * 2
def baseEnd_7434880 : Nat := 3817667048499976231507615

theorem tailTrace_7434880 : CollatzResearch.WordTrace tailWord_7434880 prefixEnd_7434880 3817667048499976231507615 := by
  unfold tailWord_7434880
  simp only [CollatzResearch.WordTrace]
  refine ⟨135586175652353505628523047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180781567536471340838030729 135586175652353505628523047)
  ·
    refine ⟨203379263478530258442784571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135586175652353505628523047 203379263478530258442784571)
    ·
      refine ⟨305068895217795387664176857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203379263478530258442784571 305068895217795387664176857)
      ·
        refine ⟨228801671413346540748132643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305068895217795387664176857 228801671413346540748132643)
        ·
          refine ⟨343202507120019811122198965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228801671413346540748132643 343202507120019811122198965)
          ·
            refine ⟨32175235042501857292706153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343202507120019811122198965 32175235042501857292706153)
            ·
              refine ⟨24131426281876392969529615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32175235042501857292706153 24131426281876392969529615)
              ·
                refine ⟨36197139422814589454294423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24131426281876392969529615 36197139422814589454294423)
                ·
                  refine ⟨54295709134221884181441635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36197139422814589454294423 54295709134221884181441635)
                  ·
                    refine ⟨81443563701332826272162453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54295709134221884181441635 81443563701332826272162453)
                    ·
                      refine ⟨3817667048499976231507615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81443563701332826272162453 3817667048499976231507615)
                      ·
                        rfl

theorem cell23_7434880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_7434880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434880 prefixEnd_7434880 := by exact prefixLift 7434880
  have htrace : WordTrace (prefixWord ++ tailWord_7434880) baseStart_7434880 baseEnd_7434880 := by
    simpa [prefixWord, tailWord_7434880, baseEnd_7434880] using wordTrace_append hprefix tailTrace_7434880
  have hstable : (prefixWord ++ tailWord_7434880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434880).length < 2 ^ (prefixWord ++ tailWord_7434880).sum := by decide
  have hdescent : baseEnd_7434880 < baseStart_7434880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434884 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_7434884 : Nat := 118140960795 + 7434884 * 2 ^ 59
def prefixEnd_7434884 : Nat := 4983230072969 + 3 ^ 40 * 7434884 * 2
def baseEnd_7434884 : Nat := 3817669102422594215857597

theorem tailTrace_7434884 : CollatzResearch.WordTrace tailWord_7434884 prefixEnd_7434884 3817669102422594215857597 := by
  unfold tailWord_7434884
  simp only [CollatzResearch.WordTrace]
  refine ⟨135586248598346259970095853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180781664797795013293461137 135586248598346259970095853)
  ·
    refine ⟨50844843224379847488785945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135586248598346259970095853 50844843224379847488785945)
    ·
      refine ⟨38133632418284885616589459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50844843224379847488785945 38133632418284885616589459)
      ·
        refine ⟨57200448627427328424884189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38133632418284885616589459 57200448627427328424884189)
        ·
          refine ⟨21450168235285248159331571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57200448627427328424884189 21450168235285248159331571)
          ·
            refine ⟨32175252352927872238997357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21450168235285248159331571 32175252352927872238997357)
            ·
              refine ⟨12065719632347952089624009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32175252352927872238997357 12065719632347952089624009)
              ·
                refine ⟨9049289724260964067218007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12065719632347952089624009 9049289724260964067218007)
                ·
                  refine ⟨13573934586391446100827011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9049289724260964067218007 13573934586391446100827011)
                  ·
                    refine ⟨20360901879587169151240517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13573934586391446100827011 20360901879587169151240517)
                    ·
                      refine ⟨3817669102422594215857597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20360901879587169151240517 3817669102422594215857597)
                      ·
                        rfl

theorem cell23_7434884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_7434884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434884 prefixEnd_7434884 := by exact prefixLift 7434884
  have htrace : WordTrace (prefixWord ++ tailWord_7434884) baseStart_7434884 baseEnd_7434884 := by
    simpa [prefixWord, tailWord_7434884, baseEnd_7434884] using wordTrace_append hprefix tailTrace_7434884
  have hstable : (prefixWord ++ tailWord_7434884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434884).length < 2 ^ (prefixWord ++ tailWord_7434884).sum := by decide
  have hdescent : baseEnd_7434884 < baseStart_7434884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434887 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_7434887 : Nat := 118140960795 + 7434887 * 2 ^ 59
def prefixEnd_7434887 : Nat := 4983230072969 + 3 ^ 40 * 7434887 * 2
def baseEnd_7434887 : Nat := 3817670642864557704120083

theorem tailTrace_7434887 : CollatzResearch.WordTrace tailWord_7434887 prefixEnd_7434887 3817670642864557704120083 := by
  unfold tailWord_7434887
  simp only [CollatzResearch.WordTrace]
  refine ⟨271172606615681651452550915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180781737743787767635033943 271172606615681651452550915)
  ·
    refine ⟨406758909923522477178826373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271172606615681651452550915 406758909923522477178826373)
    ·
      refine ⟨76267295610660464471029945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406758909923522477178826373 76267295610660464471029945)
      ·
        refine ⟨57200471707995348353272459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76267295610660464471029945 57200471707995348353272459)
        ·
          refine ⟨85800707561993022529908689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57200471707995348353272459 85800707561993022529908689)
          ·
            refine ⟨64350530671494766897431517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85800707561993022529908689 64350530671494766897431517)
            ·
              refine ⟨24131449001810537586536819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64350530671494766897431517 24131449001810537586536819)
              ·
                refine ⟨36197173502715806379805229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24131449001810537586536819 36197173502715806379805229)
                ·
                  refine ⟨13573940063518427392426961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36197173502715806379805229 13573940063518427392426961)
                  ·
                    refine ⟨10180455047638820544320221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13573940063518427392426961 10180455047638820544320221)
                    ·
                      refine ⟨3817670642864557704120083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180455047638820544320221 3817670642864557704120083)
                      ·
                        rfl

theorem cell23_7434887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_7434887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434887 prefixEnd_7434887 := by exact prefixLift 7434887
  have htrace : WordTrace (prefixWord ++ tailWord_7434887) baseStart_7434887 baseEnd_7434887 := by
    simpa [prefixWord, tailWord_7434887, baseEnd_7434887] using wordTrace_append hprefix tailTrace_7434887
  have hstable : (prefixWord ++ tailWord_7434887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434887).length < 2 ^ (prefixWord ++ tailWord_7434887).sum := by decide
  have hdescent : baseEnd_7434887 < baseStart_7434887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434930 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_7434930 : Nat := 118140960795 + 7434930 * 2 ^ 59
def prefixEnd_7434930 : Nat := 4983230072969 + 3 ^ 40 * 7434930 * 2
def baseEnd_7434930 : Nat := 3817692722532701035882385

theorem tailTrace_7434930 : CollatzResearch.WordTrace tailWord_7434930 prefixEnd_7434930 3817692722532701035882385 := by
  unfold tailWord_7434930
  simp only [CollatzResearch.WordTrace]
  refine ⟨67793543738631467449091561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180782783303017246530910829 67793543738631467449091561)
  ·
    refine ⟨50845157803973600586818671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67793543738631467449091561 50845157803973600586818671)
    ·
      refine ⟨76267736705960400880228007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50845157803973600586818671 76267736705960400880228007)
      ·
        refine ⟨114401605058940601320342011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76267736705960400880228007 114401605058940601320342011)
        ·
          refine ⟨171602407588410901980513017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114401605058940601320342011 171602407588410901980513017)
          ·
            refine ⟨128701805691308176485384763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171602407588410901980513017 128701805691308176485384763)
            ·
              refine ⟨193052708536962264728077145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128701805691308176485384763 193052708536962264728077145)
              ·
                refine ⟨144789531402721698546057859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193052708536962264728077145 144789531402721698546057859)
                ·
                  refine ⟨217184297104082547819086789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144789531402721698546057859 217184297104082547819086789)
                  ·
                    refine ⟨40722055707015477716078773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217184297104082547819086789 40722055707015477716078773)
                    ·
                      refine ⟨3817692722532701035882385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40722055707015477716078773 3817692722532701035882385)
                      ·
                        rfl

theorem cell23_7434930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_7434930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434930 prefixEnd_7434930 := by exact prefixLift 7434930
  have htrace : WordTrace (prefixWord ++ tailWord_7434930) baseStart_7434930 baseEnd_7434930 := by
    simpa [prefixWord, tailWord_7434930, baseEnd_7434930] using wordTrace_append hprefix tailTrace_7434930
  have hstable : (prefixWord ++ tailWord_7434930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434930).length < 2 ^ (prefixWord ++ tailWord_7434930).sum := by decide
  have hdescent : baseEnd_7434930 < baseStart_7434930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434944 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 3, 3, 2]
def baseStart_7434944 : Nat := 118140960795 + 7434944 * 2 ^ 59
def prefixEnd_7434944 : Nat := 4983230072969 + 3 ^ 40 * 7434944 * 2
def baseEnd_7434944 : Nat := 3817699911261863981107321

theorem tailTrace_7434944 : CollatzResearch.WordTrace tailWord_7434944 prefixEnd_7434944 3817699911261863981107321 := by
  unfold tailWord_7434944
  simp only [CollatzResearch.WordTrace]
  refine ⟨135587342788237575093687943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180783123717650100124917257 135587342788237575093687943)
  ·
    refine ⟨203381014182356362640531915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135587342788237575093687943 203381014182356362640531915)
    ·
      refine ⟨305071521273534543960797873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203381014182356362640531915 305071521273534543960797873)
      ·
        refine ⟨228803640955150907970598405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305071521273534543960797873 228803640955150907970598405)
        ·
          refine ⟨42900682679090795244487201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228803640955150907970598405 42900682679090795244487201)
          ·
            refine ⟨32175512009318096433365401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42900682679090795244487201 32175512009318096433365401)
            ·
              refine ⟨24131634006988572325024051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32175512009318096433365401 24131634006988572325024051)
              ·
                refine ⟨36197451010482858487536077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24131634006988572325024051 36197451010482858487536077)
                ·
                  refine ⟨13574044128931071932826029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36197451010482858487536077 13574044128931071932826029)
                  ·
                    refine ⟨5090266548349151974809761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13574044128931071932826029 5090266548349151974809761)
                    ·
                      refine ⟨3817699911261863981107321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090266548349151974809761 3817699911261863981107321)
                      ·
                        rfl

theorem cell23_7434944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_7434944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434944 prefixEnd_7434944 := by exact prefixLift 7434944
  have htrace : WordTrace (prefixWord ++ tailWord_7434944) baseStart_7434944 baseEnd_7434944 := by
    simpa [prefixWord, tailWord_7434944, baseEnd_7434944] using wordTrace_append hprefix tailTrace_7434944
  have hstable : (prefixWord ++ tailWord_7434944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434944).length < 2 ^ (prefixWord ++ tailWord_7434944).sum := by decide
  have hdescent : baseEnd_7434944 < baseStart_7434944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434960 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_7434960 : Nat := 118140960795 + 7434960 * 2 ^ 59
def prefixEnd_7434960 : Nat := 4983230072969 + 3 ^ 40 * 7434960 * 2
def baseEnd_7434960 : Nat := 3817708126952335918507247

theorem tailTrace_7434960 : CollatzResearch.WordTrace tailWord_7434960 prefixEnd_7434960 3817708126952335918507247 := by
  unfold tailWord_7434960
  simp only [CollatzResearch.WordTrace]
  refine ⟨135587634572208592459979167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180783512762944789946638889 135587634572208592459979167)
  ·
    refine ⟨203381451858312888689968751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135587634572208592459979167 203381451858312888689968751)
    ·
      refine ⟨305072177787469333034953127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203381451858312888689968751 305072177787469333034953127)
      ·
        refine ⟨457608266681203999552429691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305072177787469333034953127 457608266681203999552429691)
        ·
          refine ⟨686412400021805999328644537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457608266681203999552429691 686412400021805999328644537)
          ·
            refine ⟨514809300016354499496483403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686412400021805999328644537 514809300016354499496483403)
            ·
              refine ⟨772213950024531749244725105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514809300016354499496483403 772213950024531749244725105)
              ·
                refine ⟨579160462518398811933543829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772213950024531749244725105 579160462518398811933543829)
                ·
                  refine ⟨27148146680549944309384867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 579160462518398811933543829 27148146680549944309384867)
                  ·
                    refine ⟨40722220020824916464077301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27148146680549944309384867 40722220020824916464077301)
                    ·
                      refine ⟨3817708126952335918507247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40722220020824916464077301 3817708126952335918507247)
                      ·
                        rfl

theorem cell23_7434960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_7434960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434960 prefixEnd_7434960 := by exact prefixLift 7434960
  have htrace : WordTrace (prefixWord ++ tailWord_7434960) baseStart_7434960 baseEnd_7434960 := by
    simpa [prefixWord, tailWord_7434960, baseEnd_7434960] using wordTrace_append hprefix tailTrace_7434960
  have hstable : (prefixWord ++ tailWord_7434960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434960).length < 2 ^ (prefixWord ++ tailWord_7434960).sum := by decide
  have hdescent : baseEnd_7434960 < baseStart_7434960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7434991 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 1, 4, 2]
def baseStart_7434991 : Nat := 118140960795 + 7434991 * 2 ^ 59
def prefixEnd_7434991 : Nat := 4983230072969 + 3 ^ 40 * 7434991 * 2
def baseEnd_7434991 : Nat := 3817724044852625297219605

theorem tailTrace_7434991 : CollatzResearch.WordTrace tailWord_7434991 prefixEnd_7434991 3817724044852625297219605 := by
  unfold tailWord_7434991
  simp only [CollatzResearch.WordTrace]
  refine ⟨271176399807304877214336827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180784266538203251476224551 271176399807304877214336827)
  ·
    refine ⟨406764599710957315821505241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271176399807304877214336827 406764599710957315821505241)
    ·
      refine ⟨305073449783217986866128931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406764599710957315821505241 305073449783217986866128931)
      ·
        refine ⟨457610174674826980299193397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305073449783217986866128931 457610174674826980299193397)
        ·
          refine ⟨42900953875765029403049381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457610174674826980299193397 42900953875765029403049381)
          ·
            refine ⟨8043928851705943013071759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42900953875765029403049381 8043928851705943013071759)
            ·
              refine ⟨12065893277558914519607639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043928851705943013071759 12065893277558914519607639)
              ·
                refine ⟨18098839916338371779411459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12065893277558914519607639 18098839916338371779411459)
                ·
                  refine ⟨27148259874507557669117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18098839916338371779411459 27148259874507557669117189)
                  ·
                    refine ⟨5090298726470167062959473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27148259874507557669117189 5090298726470167062959473)
                    ·
                      refine ⟨3817724044852625297219605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090298726470167062959473 3817724044852625297219605)
                      ·
                        rfl

theorem cell23_7434991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 4, 2].length) (baseStart_7434991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7434991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7434991 prefixEnd_7434991 := by exact prefixLift 7434991
  have htrace : WordTrace (prefixWord ++ tailWord_7434991) baseStart_7434991 baseEnd_7434991 := by
    simpa [prefixWord, tailWord_7434991, baseEnd_7434991] using wordTrace_append hprefix tailTrace_7434991
  have hstable : (prefixWord ++ tailWord_7434991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7434991).length < 2 ^ (prefixWord ++ tailWord_7434991).sum := by decide
  have hdescent : baseEnd_7434991 < baseStart_7434991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7434991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435027 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 2, 5]
def baseStart_7435027 : Nat := 118140960795 + 7435027 * 2 ^ 59
def prefixEnd_7435027 : Nat := 4983230072969 + 3 ^ 40 * 7435027 * 2
def baseEnd_7435027 : Nat := 1272580843385395718789813

theorem tailTrace_7435027 : CollatzResearch.WordTrace tailWord_7435027 prefixEnd_7435027 1272580843385395718789813 := by
  unfold tailWord_7435027
  simp only [CollatzResearch.WordTrace]
  refine ⟨271177712835174455362647335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180785141890116303575098223 271177712835174455362647335)
  ·
    refine ⟨406766569252761683043971003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271177712835174455362647335 406766569252761683043971003)
    ·
      refine ⟨610149853879142524565956505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406766569252761683043971003 610149853879142524565956505)
      ·
        refine ⟨457612390409356893424467379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610149853879142524565956505 457612390409356893424467379)
        ·
          refine ⟨686418585614035340136701069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457612390409356893424467379 686418585614035340136701069)
          ·
            refine ⟨257406969605263252551262901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686418585614035340136701069 257406969605263252551262901)
            ·
              refine ⟨24131903400493429926680897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257406969605263252551262901 24131903400493429926680897)
              ·
                refine ⟨18098927550370072445010673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24131903400493429926680897 18098927550370072445010673)
                ·
                  refine ⟨13574195662777554333758005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18098927550370072445010673 13574195662777554333758005)
                  ·
                    refine ⟨1272580843385395718789813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13574195662777554333758005 1272580843385395718789813)
                    ·
                      rfl

theorem cell23_7435027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 5].length) (baseStart_7435027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435027 prefixEnd_7435027 := by exact prefixLift 7435027
  have htrace : WordTrace (prefixWord ++ tailWord_7435027) baseStart_7435027 baseEnd_7435027 := by
    simpa [prefixWord, tailWord_7435027, baseEnd_7435027] using wordTrace_append hprefix tailTrace_7435027
  have hstable : (prefixWord ++ tailWord_7435027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435027).length < 2 ^ (prefixWord ++ tailWord_7435027).sum := by decide
  have hdescent : baseEnd_7435027 < baseStart_7435027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435031 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 7]
def baseStart_7435031 : Nat := 118140960795 + 7435031 * 2 ^ 59
def prefixEnd_7435031 : Nat := 4983230072969 + 3 ^ 40 * 7435031 * 2
def baseEnd_7435031 : Nat := 424193842675422793413269

theorem tailTrace_7435031 : CollatzResearch.WordTrace tailWord_7435031 prefixEnd_7435031 424193842675422793413269 := by
  unfold tailWord_7435031
  simp only [CollatzResearch.WordTrace]
  refine ⟨271177858727159964045792947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180785239151439976030528631 271177858727159964045792947)
  ·
    refine ⟨406766788090739946068689421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271177858727159964045792947 406766788090739946068689421)
    ·
      refine ⟨152537545534027479775758533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406766788090739946068689421 152537545534027479775758533)
      ·
        refine ⟨28600789787630152457954725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152537545534027479775758533 28600789787630152457954725)
        ·
          refine ⟨5362648085180653585866511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28600789787630152457954725 5362648085180653585866511)
          ·
            refine ⟨8043972127770980378799767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362648085180653585866511 8043972127770980378799767)
            ·
              refine ⟨12065958191656470568199651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043972127770980378799767 12065958191656470568199651)
              ·
                refine ⟨18098937287484705852299477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12065958191656470568199651 18098937287484705852299477)
                ·
                  refine ⟨424193842675422793413269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18098937287484705852299477 424193842675422793413269)
                  ·
                    rfl

theorem cell23_7435031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 7].length) (baseStart_7435031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435031 prefixEnd_7435031 := by exact prefixLift 7435031
  have htrace : WordTrace (prefixWord ++ tailWord_7435031) baseStart_7435031 baseEnd_7435031 := by
    simpa [prefixWord, tailWord_7435031, baseEnd_7435031] using wordTrace_append hprefix tailTrace_7435031
  have hstable : (prefixWord ++ tailWord_7435031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435031).length < 2 ^ (prefixWord ++ tailWord_7435031).sum := by decide
  have hdescent : baseEnd_7435031 < baseStart_7435031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435034 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2]
def baseStart_7435034 : Nat := 118140960795 + 7435034 * 2 ^ 59
def prefixEnd_7435034 : Nat := 4983230072969 + 3 ^ 40 * 7435034 * 2
def baseEnd_7435034 : Nat := 3817746124520768628981907

theorem tailTrace_7435034 : CollatzResearch.WordTrace tailWord_7435034 prefixEnd_7435034 3817746124520768628981907 := by
  unfold tailWord_7435034
  simp only [CollatzResearch.WordTrace]
  refine ⟨67794492036537273889538039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180785312097432730372101437 67794492036537273889538039)
  ·
    refine ⟨101691738054805910834307059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67794492036537273889538039 101691738054805910834307059)
    ·
      refine ⟨152537607082208866251460589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101691738054805910834307059 152537607082208866251460589)
      ·
        refine ⟨57201602655828324844297721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152537607082208866251460589 57201602655828324844297721)
        ·
          refine ⟨42901201991871243633223291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57201602655828324844297721 42901201991871243633223291)
          ·
            refine ⟨64351802987806865449834937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42901201991871243633223291 64351802987806865449834937)
            ·
              refine ⟨48263852240855149087376203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64351802987806865449834937 48263852240855149087376203)
              ·
                refine ⟨72395778361282723631064305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48263852240855149087376203 72395778361282723631064305)
                ·
                  refine ⟨54296833770962042723298229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72395778361282723631064305 54296833770962042723298229)
                  ·
                    refine ⟨5090328166027691505309209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54296833770962042723298229 5090328166027691505309209)
                    ·
                      refine ⟨3817746124520768628981907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090328166027691505309209 3817746124520768628981907)
                      ·
                        rfl

theorem cell23_7435034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_7435034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435034 prefixEnd_7435034 := by exact prefixLift 7435034
  have htrace : WordTrace (prefixWord ++ tailWord_7435034) baseStart_7435034 baseEnd_7435034 := by
    simpa [prefixWord, tailWord_7435034, baseEnd_7435034] using wordTrace_append hprefix tailTrace_7435034
  have hstable : (prefixWord ++ tailWord_7435034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435034).length < 2 ^ (prefixWord ++ tailWord_7435034).sum := by decide
  have hdescent : baseEnd_7435034 < baseStart_7435034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435064 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_7435064 : Nat := 118140960795 + 7435064 * 2 ^ 59
def prefixEnd_7435064 : Nat := 4983230072969 + 3 ^ 40 * 7435064 * 2
def baseEnd_7435064 : Nat := 3817761528940403511606769

theorem tailTrace_7435064 : CollatzResearch.WordTrace tailWord_7435064 prefixEnd_7435064 3817761528940403511606769 := by
  unfold tailWord_7435064
  simp only [CollatzResearch.WordTrace]
  refine ⟨135589531168020205340872123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180786041557360273787829497 135589531168020205340872123)
  ·
    refine ⟨203384296752030308011308185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135589531168020205340872123 203384296752030308011308185)
    ·
      refine ⟨152538222564022731008481139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203384296752030308011308185 152538222564022731008481139)
      ·
        refine ⟨228807333846034096512721709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152538222564022731008481139 228807333846034096512721709)
        ·
          refine ⟨85802750192262786192270641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228807333846034096512721709 85802750192262786192270641)
          ·
            refine ⟨64352062644197089644202981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85802750192262786192270641 64352062644197089644202981)
            ·
              refine ⟨12066011745786954308288059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64352062644197089644202981 12066011745786954308288059)
              ·
                refine ⟨18099017618680431462432089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12066011745786954308288059 18099017618680431462432089)
                ·
                  refine ⟨13574263214010323596824067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18099017618680431462432089 13574263214010323596824067)
                  ·
                    refine ⟨20361394821015485395236101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13574263214010323596824067 20361394821015485395236101)
                    ·
                      refine ⟨3817761528940403511606769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20361394821015485395236101 3817761528940403511606769)
                      ·
                        rfl

theorem cell23_7435064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_7435064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435064 prefixEnd_7435064 := by exact prefixLift 7435064
  have htrace : WordTrace (prefixWord ++ tailWord_7435064) baseStart_7435064 baseEnd_7435064 := by
    simpa [prefixWord, tailWord_7435064, baseEnd_7435064] using wordTrace_append hprefix tailTrace_7435064
  have hstable : (prefixWord ++ tailWord_7435064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435064).length < 2 ^ (prefixWord ++ tailWord_7435064).sum := by decide
  have hdescent : baseEnd_7435064 < baseStart_7435064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435138 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_7435138 : Nat := 118140960795 + 7435138 * 2 ^ 59
def prefixEnd_7435138 : Nat := 4983230072969 + 3 ^ 40 * 7435138 * 2
def baseEnd_7435138 : Nat := 424199947389870691342381

theorem tailTrace_7435138 : CollatzResearch.WordTrace tailWord_7435138 prefixEnd_7435138 424199947389870691342381 := by
  unfold tailWord_7435138
  simp only [CollatzResearch.WordTrace]
  refine ⟨67795440334443080329984517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180787840891848214213292045 67795440334443080329984517)
  ·
    refine ⟨12711645062708077561872097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67795440334443080329984517 12711645062708077561872097)
    ·
      refine ⟨9533733797031058171404073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12711645062708077561872097 9533733797031058171404073)
      ·
        refine ⟨7150300347773293628553055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9533733797031058171404073 7150300347773293628553055)
        ·
          refine ⟨10725450521659940442829583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150300347773293628553055 10725450521659940442829583)
          ·
            refine ⟨16088175782489910664244375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10725450521659940442829583 16088175782489910664244375)
            ·
              refine ⟨24132263673734865996366563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16088175782489910664244375 24132263673734865996366563)
              ·
                refine ⟨36198395510602298994549845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24132263673734865996366563 36198395510602298994549845)
                ·
                  refine ⟨424199947389870691342381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36198395510602298994549845 424199947389870691342381)
                  ·
                    rfl

theorem cell23_7435138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_7435138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435138 prefixEnd_7435138 := by exact prefixLift 7435138
  have htrace : WordTrace (prefixWord ++ tailWord_7435138) baseStart_7435138 baseEnd_7435138 := by
    simpa [prefixWord, tailWord_7435138, baseEnd_7435138] using wordTrace_append hprefix tailTrace_7435138
  have hstable : (prefixWord ++ tailWord_7435138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435138).length < 2 ^ (prefixWord ++ tailWord_7435138).sum := by decide
  have hdescent : baseEnd_7435138 < baseStart_7435138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435147 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 3, 6]
def baseStart_7435147 : Nat := 118140960795 + 7435147 * 2 ^ 59
def prefixEnd_7435147 : Nat := 4983230072969 + 3 ^ 40 * 7435147 * 2
def baseEnd_7435147 : Nat := 1272601382611575562289629

theorem tailTrace_7435147 : CollatzResearch.WordTrace tailWord_7435147 prefixEnd_7435147 1272601382611575562289629 := by
  unfold tailWord_7435147
  simp only [CollatzResearch.WordTrace]
  refine ⟨271182089594739715857015695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180788059729826477238010463 271182089594739715857015695)
  ·
    refine ⟨406773134392109573785523543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271182089594739715857015695 406773134392109573785523543)
    ·
      refine ⟨610159701588164360678285315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406773134392109573785523543 610159701588164360678285315)
      ·
        refine ⟨915239552382246541017427973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610159701588164360678285315 915239552382246541017427973)
        ·
          refine ⟨171607416071671226440767745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 915239552382246541017427973 171607416071671226440767745)
          ·
            refine ⟨128705562053753419830575809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171607416071671226440767745 128705562053753419830575809)
            ·
              refine ⟨96529171540315064872931857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128705562053753419830575809 96529171540315064872931857)
              ·
                refine ⟨72396878655236298654698893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96529171540315064872931857 72396878655236298654698893)
                ·
                  refine ⟨27148829495713611995512085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72396878655236298654698893 27148829495713611995512085)
                  ·
                    refine ⟨1272601382611575562289629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27148829495713611995512085 1272601382611575562289629)
                    ·
                      rfl

theorem cell23_7435147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 6].length) (baseStart_7435147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435147 prefixEnd_7435147 := by exact prefixLift 7435147
  have htrace : WordTrace (prefixWord ++ tailWord_7435147) baseStart_7435147 baseEnd_7435147 := by
    simpa [prefixWord, tailWord_7435147, baseEnd_7435147] using wordTrace_append hprefix tailTrace_7435147
  have hstable : (prefixWord ++ tailWord_7435147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435147).length < 2 ^ (prefixWord ++ tailWord_7435147).sum := by decide
  have hdescent : baseEnd_7435147 < baseStart_7435147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435148 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 1, 1, 3]
def baseStart_7435148 : Nat := 118140960795 + 7435148 * 2 ^ 59
def prefixEnd_7435148 : Nat := 4983230072969 + 3 ^ 40 * 7435148 * 2
def baseEnd_7435148 : Nat := 3817804661315381182956383

theorem tailTrace_7435148 : CollatzResearch.WordTrace tailWord_7435148 prefixEnd_7435148 3817804661315381182956383 := by
  unfold tailWord_7435148
  simp only [CollatzResearch.WordTrace]
  refine ⟨135591063033868046513901049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180788084045157395351868065 135591063033868046513901049)
  ·
    refine ⟨101693297275401034885425787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135591063033868046513901049 101693297275401034885425787)
    ·
      refine ⟨152539945913101552328138681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101693297275401034885425787 152539945913101552328138681)
      ·
        refine ⟨114404959434826164246104011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152539945913101552328138681 114404959434826164246104011)
        ·
          refine ⟨171607439152239246369156017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114404959434826164246104011 171607439152239246369156017)
          ·
            refine ⟨128705579364179434776867013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171607439152239246369156017 128705579364179434776867013)
            ·
              refine ⟨24132296130783644020662565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128705579364179434776867013 24132296130783644020662565)
              ·
                refine ⟨4524805524521933253874231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24132296130783644020662565 4524805524521933253874231)
                ·
                  refine ⟨6787208286782899880811347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524805524521933253874231 6787208286782899880811347)
                  ·
                    refine ⟨10180812430174349821217021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6787208286782899880811347 10180812430174349821217021)
                    ·
                      refine ⟨3817804661315381182956383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180812430174349821217021 3817804661315381182956383)
                      ·
                        rfl

theorem cell23_7435148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_7435148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435148 prefixEnd_7435148 := by exact prefixLift 7435148
  have htrace : WordTrace (prefixWord ++ tailWord_7435148) baseStart_7435148 baseEnd_7435148 := by
    simpa [prefixWord, tailWord_7435148, baseEnd_7435148] using wordTrace_append hprefix tailTrace_7435148
  have hstable : (prefixWord ++ tailWord_7435148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435148).length < 2 ^ (prefixWord ++ tailWord_7435148).sum := by decide
  have hdescent : baseEnd_7435148 < baseStart_7435148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435177 : List Nat := [1, 2, 1, 1, 1, 1, 7, 9]
def baseStart_7435177 : Nat := 118140960795 + 7435177 * 2 ^ 59
def prefixEnd_7435177 : Nat := 4983230072969 + 3 ^ 40 * 7435177 * 2
def baseEnd_7435177 : Nat := 141400724157568947018287

theorem tailTrace_7435177 : CollatzResearch.WordTrace tailWord_7435177 prefixEnd_7435177 141400724157568947018287 := by
  unfold tailWord_7435177
  simp only [CollatzResearch.WordTrace]
  refine ⟨271183183784631030980607785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180788789189754020653738523 271183183784631030980607785)
  ·
    refine ⟨203387387838473273235455839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271183183784631030980607785 203387387838473273235455839)
    ·
      refine ⟨305081081757709909853183759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203387387838473273235455839 305081081757709909853183759)
      ·
        refine ⟨457621622636564864779775639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305081081757709909853183759 457621622636564864779775639)
        ·
          refine ⟨686432433954847297169663459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457621622636564864779775639 686432433954847297169663459)
          ·
            refine ⟨1029648650932270945754495189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686432433954847297169663459 1029648650932270945754495189)
            ·
              refine ⟨24132390256225100291120981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1029648650932270945754495189 24132390256225100291120981)
              ·
                refine ⟨141400724157568947018287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24132390256225100291120981 141400724157568947018287)
                ·
                  rfl

theorem cell23_7435177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 9].length) (baseStart_7435177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435177 prefixEnd_7435177 := by exact prefixLift 7435177
  have htrace : WordTrace (prefixWord ++ tailWord_7435177) baseStart_7435177 baseEnd_7435177 := by
    simpa [prefixWord, tailWord_7435177, baseEnd_7435177] using wordTrace_append hprefix tailTrace_7435177
  have hstable : (prefixWord ++ tailWord_7435177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435177).length < 2 ^ (prefixWord ++ tailWord_7435177).sum := by decide
  have hdescent : baseEnd_7435177 < baseStart_7435177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435191 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_7435191 : Nat := 118140960795 + 7435191 * 2 ^ 59
def prefixEnd_7435191 : Nat := 4983230072969 + 3 ^ 40 * 7435191 * 2
def baseEnd_7435191 : Nat := 3817826740983524514718685

theorem tailTrace_7435191 : CollatzResearch.WordTrace tailWord_7435191 prefixEnd_7435191 3817826740983524514718685 := by
  unfold tailWord_7435191
  simp only [CollatzResearch.WordTrace]
  refine ⟨271183694406580311371617427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180789129604386874247744951 271183694406580311371617427)
  ·
    refine ⟨406775541609870467057426141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271183694406580311371617427 406775541609870467057426141)
    ·
      refine ⟨152540828103701425146534803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406775541609870467057426141 152540828103701425146534803)
      ·
        refine ⟨228811242155552137719802205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152540828103701425146534803 228811242155552137719802205)
        ·
          refine ⟨85804215808332051644925827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228811242155552137719802205 85804215808332051644925827)
          ·
            refine ⟨128706323712498077467388741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85804215808332051644925827 128706323712498077467388741)
            ·
              refine ⟨24132435696093389525135389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128706323712498077467388741 24132435696093389525135389)
              ·
                refine ⟨9049663386035021071925771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24132435696093389525135389 9049663386035021071925771)
                ·
                  refine ⟨13574495079052531607888657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9049663386035021071925771 13574495079052531607888657)
                  ·
                    refine ⟨10180871309289398705916493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13574495079052531607888657 10180871309289398705916493)
                    ·
                      refine ⟨3817826740983524514718685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10180871309289398705916493 3817826740983524514718685)
                      ·
                        rfl

theorem cell23_7435191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_7435191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435191 prefixEnd_7435191 := by exact prefixLift 7435191
  have htrace : WordTrace (prefixWord ++ tailWord_7435191) baseStart_7435191 baseEnd_7435191 := by
    simpa [prefixWord, tailWord_7435191, baseEnd_7435191] using wordTrace_append hprefix tailTrace_7435191
  have hstable : (prefixWord ++ tailWord_7435191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435191).length < 2 ^ (prefixWord ++ tailWord_7435191).sum := by decide
  have hdescent : baseEnd_7435191 < baseStart_7435191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435206 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_7435206 : Nat := 118140960795 + 7435206 * 2 ^ 59
def prefixEnd_7435206 : Nat := 4983230072969 + 3 ^ 40 * 7435206 * 2
def baseEnd_7435206 : Nat := 424203827021482439559013

theorem tailTrace_7435206 : CollatzResearch.WordTrace tailWord_7435206 prefixEnd_7435206 424203827021482439559013 := by
  unfold tailWord_7435206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474507546922686529169171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180789494334350645955608981 8474507546922686529169171)
  ·
    refine ⟨12711761320384029793753757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8474507546922686529169171 12711761320384029793753757)
    ·
      refine ⟨4766910495144011172657659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12711761320384029793753757 4766910495144011172657659)
      ·
        refine ⟨7150365742716016758986489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766910495144011172657659 7150365742716016758986489)
        ·
          refine ⟨5362774307037012569239867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7150365742716016758986489 5362774307037012569239867)
          ·
            refine ⟨8044161460555518853859801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362774307037012569239867 8044161460555518853859801)
            ·
              refine ⟨6033121095416639140394851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8044161460555518853859801 6033121095416639140394851)
              ·
                refine ⟨9049681643124958710592277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033121095416639140394851 9049681643124958710592277)
                ·
                  refine ⟨424203827021482439559013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9049681643124958710592277 424203827021482439559013)
                  ·
                    rfl

theorem cell23_7435206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_7435206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435206 prefixEnd_7435206 := by exact prefixLift 7435206
  have htrace : WordTrace (prefixWord ++ tailWord_7435206) baseStart_7435206 baseEnd_7435206 := by
    simpa [prefixWord, tailWord_7435206, baseEnd_7435206] using wordTrace_append hprefix tailTrace_7435206
  have hstable : (prefixWord ++ tailWord_7435206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435206).length < 2 ^ (prefixWord ++ tailWord_7435206).sum := by decide
  have hdescent : baseEnd_7435206 < baseStart_7435206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435261 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 5, 4, 2]
def baseStart_7435261 : Nat := 118140960795 + 7435261 * 2 ^ 59
def prefixEnd_7435261 : Nat := 4983230072969 + 3 ^ 40 * 7435261 * 2
def baseEnd_7435261 : Nat := 3817862684629339240843363

theorem tailTrace_7435261 : CollatzResearch.WordTrace tailWord_7435261 prefixEnd_7435261 3817862684629339240843363 := by
  unfold tailWord_7435261
  simp only [CollatzResearch.WordTrace]
  refine ⟨271186247516326713326665637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180790831677551142217777091 271186247516326713326665637)
  ·
    refine ⟨50847421409311258748749807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271186247516326713326665637 50847421409311258748749807)
    ·
      refine ⟨76271132113966888123124711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50847421409311258748749807 76271132113966888123124711)
      ·
        refine ⟨114406698170950332184687067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76271132113966888123124711 114406698170950332184687067)
        ·
          refine ⟨171610047256425498277030601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114406698170950332184687067 171610047256425498277030601)
          ·
            refine ⟨128707535442319123707772951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171610047256425498277030601 128707535442319123707772951)
            ·
              refine ⟨193061303163478685561659427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128707535442319123707772951 193061303163478685561659427)
              ·
                refine ⟨289591954745218028342489141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193061303163478685561659427 289591954745218028342489141)
                ·
                  refine ⟨27149245757364190157108357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289591954745218028342489141 27149245757364190157108357)
                  ·
                    refine ⟨5090483579505785654457817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27149245757364190157108357 5090483579505785654457817)
                    ·
                      refine ⟨3817862684629339240843363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090483579505785654457817 3817862684629339240843363)
                      ·
                        rfl

theorem cell23_7435261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_7435261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435261 prefixEnd_7435261 := by exact prefixLift 7435261
  have htrace : WordTrace (prefixWord ++ tailWord_7435261) baseStart_7435261 baseEnd_7435261 := by
    simpa [prefixWord, tailWord_7435261, baseEnd_7435261] using wordTrace_append hprefix tailTrace_7435261
  have hstable : (prefixWord ++ tailWord_7435261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435261).length < 2 ^ (prefixWord ++ tailWord_7435261).sum := by decide
  have hdescent : baseEnd_7435261 < baseStart_7435261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435278 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7435278 : Nat := 118140960795 + 7435278 * 2 ^ 59
def prefixEnd_7435278 : Nat := 4983230072969 + 3 ^ 40 * 7435278 * 2
def baseEnd_7435278 : Nat := 3817871413800465674330785

theorem tailTrace_7435278 : CollatzResearch.WordTrace tailWord_7435278 prefixEnd_7435278 3817871413800465674330785 := by
  unfold tailWord_7435278
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898358444658140653754311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180791245038176750153356325 33898358444658140653754311)
  ·
    refine ⟨50847537666987210980631467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33898358444658140653754311 50847537666987210980631467)
    ·
      refine ⟨76271306500480816470947201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50847537666987210980631467 76271306500480816470947201)
      ·
        refine ⟨57203479875360612353210401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76271306500480816470947201 57203479875360612353210401)
        ·
          refine ⟨42902609906520459264907801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57203479875360612353210401 42902609906520459264907801)
          ·
            refine ⟨32176957429890344448680851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42902609906520459264907801 32176957429890344448680851)
            ·
              refine ⟨48265436144835516673021277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32176957429890344448680851 48265436144835516673021277)
              ·
                refine ⟨18099538554313318752382979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48265436144835516673021277 18099538554313318752382979)
                ·
                  refine ⟨27149307831469978128574469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18099538554313318752382979 27149307831469978128574469)
                  ·
                    refine ⟨5090495218400620899107713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27149307831469978128574469 5090495218400620899107713)
                    ·
                      refine ⟨3817871413800465674330785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090495218400620899107713 3817871413800465674330785)
                      ·
                        rfl

theorem cell23_7435278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7435278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435278 prefixEnd_7435278 := by exact prefixLift 7435278
  have htrace : WordTrace (prefixWord ++ tailWord_7435278) baseStart_7435278 baseEnd_7435278 := by
    simpa [prefixWord, tailWord_7435278, baseEnd_7435278] using wordTrace_append hprefix tailTrace_7435278
  have hstable : (prefixWord ++ tailWord_7435278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435278).length < 2 ^ (prefixWord ++ tailWord_7435278).sum := by decide
  have hdescent : baseEnd_7435278 < baseStart_7435278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435318 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_7435318 : Nat := 118140960795 + 7435318 * 2 ^ 59
def prefixEnd_7435318 : Nat := 4983230072969 + 3 ^ 40 * 7435318 * 2
def baseEnd_7435318 : Nat := 424210217002960613092289

theorem tailTrace_7435318 : CollatzResearch.WordTrace tailWord_7435318 prefixEnd_7435318 424210217002960613092289 := by
  unfold tailWord_7435318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949270404820013253843163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180792217651413474707660405 16949270404820013253843163)
  ·
    refine ⟨25423905607230019880764745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16949270404820013253843163 25423905607230019880764745)
    ·
      refine ⟨19067929205422514910573559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25423905607230019880764745 19067929205422514910573559)
      ·
        refine ⟨28601893808133772365860339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19067929205422514910573559 28601893808133772365860339)
        ·
          refine ⟨42902840712200658548790509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28601893808133772365860339 42902840712200658548790509)
          ·
            refine ⟨16088565267075246955796441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42902840712200658548790509 16088565267075246955796441)
            ·
              refine ⟨12066423950306435216847331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16088565267075246955796441 12066423950306435216847331)
              ·
                refine ⟨18099635925459652825270997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12066423950306435216847331 18099635925459652825270997)
                ·
                  refine ⟨424210217002960613092289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18099635925459652825270997 424210217002960613092289)
                  ·
                    rfl

theorem cell23_7435318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_7435318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435318 prefixEnd_7435318 := by exact prefixLift 7435318
  have htrace : WordTrace (prefixWord ++ tailWord_7435318) baseStart_7435318 baseEnd_7435318 := by
    simpa [prefixWord, tailWord_7435318, baseEnd_7435318] using wordTrace_append hprefix tailTrace_7435318
  have hstable : (prefixWord ++ tailWord_7435318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435318).length < 2 ^ (prefixWord ++ tailWord_7435318).sum := by decide
  have hdescent : baseEnd_7435318 < baseStart_7435318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435329 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7435329 : Nat := 118140960795 + 7435329 * 2 ^ 59
def prefixEnd_7435329 : Nat := 4983230072969 + 3 ^ 40 * 7435329 * 2
def baseEnd_7435329 : Nat := 3817897601313844974793051

theorem tailTrace_7435329 : CollatzResearch.WordTrace tailWord_7435329 prefixEnd_7435329 3817897601313844974793051 := by
  unfold tailWord_7435329
  simp only [CollatzResearch.WordTrace]
  refine ⟨271188727680080360940141041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180792485120053573960094027 271188727680080360940141041)
  ·
    refine ⟨203391545760060270705105781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271188727680080360940141041 203391545760060270705105781)
    ·
      refine ⟨19067957415005650378603667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203391545760060270705105781 19067957415005650378603667)
      ·
        refine ⟨28601936122508475567905501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19067957415005650378603667 28601936122508475567905501)
        ·
          refine ⟨10725726045940678337964563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28601936122508475567905501 10725726045940678337964563)
          ·
            refine ⟨16088589068911017506946845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10725726045940678337964563 16088589068911017506946845)
            ·
              refine ⟨6033220900841631565105067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16088589068911017506946845 6033220900841631565105067)
              ·
                refine ⟨9049831351262447347657601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033220900841631565105067 9049831351262447347657601)
                ·
                  refine ⟨6787373513446835510743201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9049831351262447347657601 6787373513446835510743201)
                  ·
                    refine ⟨5090530135085126633057401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6787373513446835510743201 5090530135085126633057401)
                    ·
                      refine ⟨3817897601313844974793051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090530135085126633057401 3817897601313844974793051)
                      ·
                        rfl

theorem cell23_7435329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7435329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435329 prefixEnd_7435329 := by exact prefixLift 7435329
  have htrace : WordTrace (prefixWord ++ tailWord_7435329) baseStart_7435329 baseEnd_7435329 := by
    simpa [prefixWord, tailWord_7435329, baseEnd_7435329] using wordTrace_append hprefix tailTrace_7435329
  have hstable : (prefixWord ++ tailWord_7435329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435329).length < 2 ^ (prefixWord ++ tailWord_7435329).sum := by decide
  have hdescent : baseEnd_7435329 < baseStart_7435329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435351 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_7435351 : Nat := 118140960795 + 7435351 * 2 ^ 59
def prefixEnd_7435351 : Nat := 4983230072969 + 3 ^ 40 * 7435351 * 2
def baseEnd_7435351 : Nat := 3817908897888243888717949

theorem tailTrace_7435351 : CollatzResearch.WordTrace tailWord_7435351 prefixEnd_7435351 3817908897888243888717949 := by
  unfold tailWord_7435351
  simp only [CollatzResearch.WordTrace]
  refine ⟨271189530086000658697441907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180793020057333772464961271 271189530086000658697441907)
  ·
    refine ⟨406784295129000988046162861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271189530086000658697441907 406784295129000988046162861)
    ·
      refine ⟨152544110673375370517311073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406784295129000988046162861 152544110673375370517311073)
      ·
        refine ⟨114408083005031527887983305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152544110673375370517311073 114408083005031527887983305)
        ·
          refine ⟨85806062253773645915987479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114408083005031527887983305 85806062253773645915987479)
          ·
            refine ⟨128709093380660468873981219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85806062253773645915987479 128709093380660468873981219)
            ·
              refine ⟨193063640070990703310971829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128709093380660468873981219 193063640070990703310971829)
              ·
                refine ⟨18099716256655378435403609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193063640070990703310971829 18099716256655378435403609)
                ·
                  refine ⟨13574787192491533826552707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18099716256655378435403609 13574787192491533826552707)
                  ·
                    refine ⟨20362180788737300739829061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13574787192491533826552707 20362180788737300739829061)
                    ·
                      refine ⟨3817908897888243888717949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20362180788737300739829061 3817908897888243888717949)
                      ·
                        rfl

theorem cell23_7435351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_7435351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435351 prefixEnd_7435351 := by exact prefixLift 7435351
  have htrace : WordTrace (prefixWord ++ tailWord_7435351) baseStart_7435351 baseEnd_7435351 := by
    simpa [prefixWord, tailWord_7435351, baseEnd_7435351] using wordTrace_append hprefix tailTrace_7435351
  have hstable : (prefixWord ++ tailWord_7435351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435351).length < 2 ^ (prefixWord ++ tailWord_7435351).sum := by decide
  have hdescent : baseEnd_7435351 < baseStart_7435351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435361 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 5, 4]
def baseStart_7435361 : Nat := 118140960795 + 7435361 * 2 ^ 59
def prefixEnd_7435361 : Nat := 4983230072969 + 3 ^ 40 * 7435361 * 2
def baseEnd_7435361 : Nat := 1272638010898262949864301

theorem tailTrace_7435361 : CollatzResearch.WordTrace tailWord_7435361 prefixEnd_7435361 1272638010898262949864301 := by
  unfold tailWord_7435361
  simp only [CollatzResearch.WordTrace]
  refine ⟨271189894815964430405305937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180793263210642953603537291 271189894815964430405305937)
  ·
    refine ⟨203392421111973322803979453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271189894815964430405305937 203392421111973322803979453)
    ·
      refine ⟨76272157916989996051492295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203392421111973322803979453 76272157916989996051492295)
      ·
        refine ⟨114408236875484994077238443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76272157916989996051492295 114408236875484994077238443)
        ·
          refine ⟨171612355313227491115857665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114408236875484994077238443 171612355313227491115857665)
          ·
            refine ⟨128709266484920618336893249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171612355313227491115857665 128709266484920618336893249)
            ·
              refine ⟨96531949863690463752669937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128709266484920618336893249 96531949863690463752669937)
              ·
                refine ⟨72398962397767847814502453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96531949863690463752669937 72398962397767847814502453)
                ·
                  refine ⟨6787402724790735732609605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72398962397767847814502453 6787402724790735732609605)
                  ·
                    refine ⟨1272638010898262949864301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6787402724790735732609605 1272638010898262949864301)
                    ·
                      rfl

theorem cell23_7435361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_7435361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435361 prefixEnd_7435361 := by exact prefixLift 7435361
  have htrace : WordTrace (prefixWord ++ tailWord_7435361) baseStart_7435361 baseEnd_7435361 := by
    simpa [prefixWord, tailWord_7435361, baseEnd_7435361] using wordTrace_append hprefix tailTrace_7435361
  have hstable : (prefixWord ++ tailWord_7435361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435361).length < 2 ^ (prefixWord ++ tailWord_7435361).sum := by decide
  have hdescent : baseEnd_7435361 < baseStart_7435361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435471 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_7435471 : Nat := 118140960795 + 7435471 * 2 ^ 59
def prefixEnd_7435471 : Nat := 4983230072969 + 3 ^ 40 * 7435471 * 2
def baseEnd_7435471 : Nat := 3817970515566783419217397

theorem tailTrace_7435471 : CollatzResearch.WordTrace tailWord_7435471 prefixEnd_7435471 3817970515566783419217397 := by
  unfold tailWord_7435471
  simp only [CollatzResearch.WordTrace]
  refine ⟨271193906845565919191810267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180795937897043946127873511 271193906845565919191810267)
  ·
    refine ⟨406790860268348878787715401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271193906845565919191810267 406790860268348878787715401)
    ·
      refine ⟨305093145201261659090786551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406790860268348878787715401 305093145201261659090786551)
      ·
        refine ⟨457639717801892488636179827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305093145201261659090786551 457639717801892488636179827)
        ·
          refine ⟨686459576702838732954269741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457639717801892488636179827 686459576702838732954269741)
          ·
            refine ⟨257422341263564524857851153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686459576702838732954269741 257422341263564524857851153)
            ·
              refine ⟨193066755947673393643388365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257422341263564524857851153 193066755947673393643388365)
              ·
                refine ⟨72400033480377522616270637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193066755947673393643388365 72400033480377522616270637)
                ·
                  refine ⟨27150012555141570981101489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72400033480377522616270637 27150012555141570981101489)
                  ·
                    refine ⟨20362509416356178235826117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27150012555141570981101489 20362509416356178235826117)
                    ·
                      refine ⟨3817970515566783419217397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20362509416356178235826117 3817970515566783419217397)
                      ·
                        rfl

theorem cell23_7435471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_7435471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435471 prefixEnd_7435471 := by exact prefixLift 7435471
  have htrace : WordTrace (prefixWord ++ tailWord_7435471) baseStart_7435471 baseEnd_7435471 := by
    simpa [prefixWord, tailWord_7435471, baseEnd_7435471] using wordTrace_append hprefix tailTrace_7435471
  have hstable : (prefixWord ++ tailWord_7435471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435471).length < 2 ^ (prefixWord ++ tailWord_7435471).sum := by decide
  have hdescent : baseEnd_7435471 < baseStart_7435471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435495 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7435495 : Nat := 118140960795 + 7435495 * 2 ^ 59
def prefixEnd_7435495 : Nat := 4983230072969 + 3 ^ 40 * 7435495 * 2
def baseEnd_7435495 : Nat := 3817982839102491325317287

theorem tailTrace_7435495 : CollatzResearch.WordTrace tailWord_7435495 prefixEnd_7435495 3817982839102491325317287 := by
  unfold tailWord_7435495
  simp only [CollatzResearch.WordTrace]
  refine ⟨271194782197478971290683939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180796521464985980860455959 271194782197478971290683939)
  ·
    refine ⟨406792173296218456936025909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271194782197478971290683939 406792173296218456936025909)
    ·
      refine ⟨38136766246520480337752429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406792173296218456936025909 38136766246520480337752429)
      ·
        refine ⟨14301287342445180126657161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38136766246520480337752429 14301287342445180126657161)
        ·
          refine ⟨10725965506833885094992871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14301287342445180126657161 10725965506833885094992871)
          ·
            refine ⟨16088948260250827642489307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10725965506833885094992871 16088948260250827642489307)
            ·
              refine ⟨24133422390376241463733961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16088948260250827642489307 24133422390376241463733961)
              ·
                refine ⟨18100066792782181097800471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24133422390376241463733961 18100066792782181097800471)
                ·
                  refine ⟨27150100189173271646700707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18100066792782181097800471 27150100189173271646700707)
                  ·
                    refine ⟨40725150283759907470051061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27150100189173271646700707 40725150283759907470051061)
                    ·
                      refine ⟨3817982839102491325317287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40725150283759907470051061 3817982839102491325317287)
                      ·
                        rfl

theorem cell23_7435495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7435495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435495 prefixEnd_7435495 := by exact prefixLift 7435495
  have htrace : WordTrace (prefixWord ++ tailWord_7435495) baseStart_7435495 baseEnd_7435495 := by
    simpa [prefixWord, tailWord_7435495, baseEnd_7435495] using wordTrace_append hprefix tailTrace_7435495
  have hstable : (prefixWord ++ tailWord_7435495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435495).length < 2 ^ (prefixWord ++ tailWord_7435495).sum := by decide
  have hdescent : baseEnd_7435495 < baseStart_7435495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435569 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 1, 3, 2]
def baseStart_7435569 : Nat := 118140960795 + 7435569 * 2 ^ 59
def prefixEnd_7435569 : Nat := 4983230072969 + 3 ^ 40 * 7435569 * 2
def baseEnd_7435569 : Nat := 3818020836670924035791947

theorem tailTrace_7435569 : CollatzResearch.WordTrace tailWord_7435569 prefixEnd_7435569 3818020836670924035791947 := by
  unfold tailWord_7435569
  simp only [CollatzResearch.WordTrace]
  refine ⟨271197481199210881928877761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180798320799473921285918507 271197481199210881928877761)
  ·
    refine ⟨203398110899408161446658321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271197481199210881928877761 203398110899408161446658321)
    ·
      refine ⟨152548583174556121084993741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203398110899408161446658321 152548583174556121084993741)
      ·
        refine ⟨57205718690458545406872653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152548583174556121084993741 57205718690458545406872653)
        ·
          refine ⟨21452144508921954527577245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57205718690458545406872653 21452144508921954527577245)
          ·
            refine ⟨8044554190845732947841467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21452144508921954527577245 8044554190845732947841467)
            ·
              refine ⟨12066831286268599421762201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044554190845732947841467 12066831286268599421762201)
              ·
                refine ⟨9050123464701449566321651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12066831286268599421762201 9050123464701449566321651)
                ·
                  refine ⟨13575185197052174349482477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9050123464701449566321651 13575185197052174349482477)
                  ·
                    refine ⟨5090694448894565381055929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13575185197052174349482477 5090694448894565381055929)
                    ·
                      refine ⟨3818020836670924035791947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090694448894565381055929 3818020836670924035791947)
                      ·
                        rfl

theorem cell23_7435569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_7435569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435569 prefixEnd_7435569 := by exact prefixLift 7435569
  have htrace : WordTrace (prefixWord ++ tailWord_7435569) baseStart_7435569 baseEnd_7435569 := by
    simpa [prefixWord, tailWord_7435569, baseEnd_7435569] using wordTrace_append hprefix tailTrace_7435569
  have hstable : (prefixWord ++ tailWord_7435569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435569).length < 2 ^ (prefixWord ++ tailWord_7435569).sum := by decide
  have hdescent : baseEnd_7435569 < baseStart_7435569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435582 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_7435582 : Nat := 118140960795 + 7435582 * 2 ^ 59
def prefixEnd_7435582 : Nat := 4983230072969 + 3 ^ 40 * 7435582 * 2
def baseEnd_7435582 : Nat := 3818027511919432484929387

theorem tailTrace_7435582 : CollatzResearch.WordTrace tailWord_7435582 prefixEnd_7435582 3818027511919432484929387 := by
  unfold tailWord_7435582
  simp only [CollatzResearch.WordTrace]
  refine ⟨33899744418520473143637625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180798636898775856766067333 33899744418520473143637625)
  ·
    refine ⟨25424808313890354857728219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33899744418520473143637625 25424808313890354857728219)
    ·
      refine ⟨38137212470835532286592329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25424808313890354857728219 38137212470835532286592329)
      ·
        refine ⟨28602909353126649214944247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38137212470835532286592329 28602909353126649214944247)
        ·
          refine ⟨42904364029689973822416371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28602909353126649214944247 42904364029689973822416371)
          ·
            refine ⟨64356546044534960733624557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42904364029689973822416371 64356546044534960733624557)
            ·
              refine ⟨24133704766700610275109209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64356546044534960733624557 24133704766700610275109209)
              ·
                refine ⟨18100278575025457706331907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24133704766700610275109209 18100278575025457706331907)
                ·
                  refine ⟨27150417862538186559497861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18100278575025457706331907 27150417862538186559497861)
                  ·
                    refine ⟨5090703349225909979905849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27150417862538186559497861 5090703349225909979905849)
                    ·
                      refine ⟨3818027511919432484929387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090703349225909979905849 3818027511919432484929387)
                      ·
                        rfl

theorem cell23_7435582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_7435582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435582 prefixEnd_7435582 := by exact prefixLift 7435582
  have htrace : WordTrace (prefixWord ++ tailWord_7435582) baseStart_7435582 baseEnd_7435582 := by
    simpa [prefixWord, tailWord_7435582, baseEnd_7435582] using wordTrace_append hprefix tailTrace_7435582
  have hstable : (prefixWord ++ tailWord_7435582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435582).length < 2 ^ (prefixWord ++ tailWord_7435582).sum := by decide
  have hdescent : baseEnd_7435582 < baseStart_7435582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435585 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7435585 : Nat := 118140960795 + 7435585 * 2 ^ 59
def prefixEnd_7435585 : Nat := 4983230072969 + 3 ^ 40 * 7435585 * 2
def baseEnd_7435585 : Nat := 3818029052361395973191873

theorem tailTrace_7435585 : CollatzResearch.WordTrace tailWord_7435585 prefixEnd_7435585 3818029052361395973191873 := by
  unfold tailWord_7435585
  simp only [CollatzResearch.WordTrace]
  refine ⟨271198064767152916661460209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180798709844768611107640139 271198064767152916661460209)
  ·
    refine ⟨203398548575364687496095157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271198064767152916661460209 203398548575364687496095157)
    ·
      refine ⟨19068613928940439452758921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203398548575364687496095157 19068613928940439452758921)
      ·
        refine ⟨14301460446705329589569191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19068613928940439452758921 14301460446705329589569191)
        ·
          refine ⟨21452190670057994384353787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14301460446705329589569191 21452190670057994384353787)
          ·
            refine ⟨32178286005086991576530681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21452190670057994384353787 32178286005086991576530681)
            ·
              refine ⟨24133714503815243682398011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32178286005086991576530681 24133714503815243682398011)
              ·
                refine ⟨36200571755722865523597017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24133714503815243682398011 36200571755722865523597017)
                ·
                  refine ⟨27150428816792149142697763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36200571755722865523597017 27150428816792149142697763)
                  ·
                    refine ⟨40725643225188223714046645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27150428816792149142697763 40725643225188223714046645)
                    ·
                      refine ⟨3818029052361395973191873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40725643225188223714046645 3818029052361395973191873)
                      ·
                        rfl

theorem cell23_7435585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7435585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435585 prefixEnd_7435585 := by exact prefixLift 7435585
  have htrace : WordTrace (prefixWord ++ tailWord_7435585) baseStart_7435585 baseEnd_7435585 := by
    simpa [prefixWord, tailWord_7435585, baseEnd_7435585] using wordTrace_append hprefix tailTrace_7435585
  have hstable : (prefixWord ++ tailWord_7435585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435585).length < 2 ^ (prefixWord ++ tailWord_7435585).sum := by decide
  have hdescent : baseEnd_7435585 < baseStart_7435585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435682 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7435682 : Nat := 118140960795 + 7435682 * 2 ^ 59
def prefixEnd_7435682 : Nat := 4983230072969 + 3 ^ 40 * 7435682 * 2
def baseEnd_7435682 : Nat := 1272692953328294031226309

theorem tailTrace_7435682 : CollatzResearch.WordTrace tailWord_7435682 prefixEnd_7435682 1272692953328294031226309 := by
  unfold tailWord_7435682
  simp only [CollatzResearch.WordTrace]
  refine ⟨67800400661950375556935325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180801068431867668151827533 67800400661950375556935325)
  ·
    refine ⟨25425150248231390833850747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67800400661950375556935325 25425150248231390833850747)
    ·
      refine ⟨38137725372347086250776121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25425150248231390833850747 38137725372347086250776121)
      ·
        refine ⟨28603294029260314688082091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38137725372347086250776121 28603294029260314688082091)
        ·
          refine ⟨42904941043890472032123137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28603294029260314688082091 42904941043890472032123137)
          ·
            refine ⟨32178705782917854024092353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42904941043890472032123137 32178705782917854024092353)
            ·
              refine ⟨24134029337188390518069265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32178705782917854024092353 24134029337188390518069265)
              ·
                refine ⟨18100522002891292888551949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24134029337188390518069265 18100522002891292888551949)
                ·
                  refine ⟨6787695751084234833206981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18100522002891292888551949 6787695751084234833206981)
                  ·
                    refine ⟨1272692953328294031226309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6787695751084234833206981 1272692953328294031226309)
                    ·
                      rfl

theorem cell23_7435682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7435682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435682 prefixEnd_7435682 := by exact prefixLift 7435682
  have htrace : WordTrace (prefixWord ++ tailWord_7435682) baseStart_7435682 baseEnd_7435682 := by
    simpa [prefixWord, tailWord_7435682, baseEnd_7435682] using wordTrace_append hprefix tailTrace_7435682
  have hstable : (prefixWord ++ tailWord_7435682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435682).length < 2 ^ (prefixWord ++ tailWord_7435682).sum := by decide
  have hdescent : baseEnd_7435682 < baseStart_7435682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435698 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_7435698 : Nat := 118140960795 + 7435698 * 2 ^ 59
def prefixEnd_7435698 : Nat := 4983230072969 + 3 ^ 40 * 7435698 * 2
def baseEnd_7435698 : Nat := 3818087075675354031078853

theorem tailTrace_7435698 : CollatzResearch.WordTrace tailWord_7435698 prefixEnd_7435698 3818087075675354031078853 := by
  unfold tailWord_7435698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67800546553935884240080937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180801457477162357973549165 67800546553935884240080937)
  ·
    refine ⟨50850409915451913180060703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67800546553935884240080937 50850409915451913180060703)
    ·
      refine ⟨76275614873177869770091055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50850409915451913180060703 76275614873177869770091055)
      ·
        refine ⟨114413422309766804655136583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76275614873177869770091055 114413422309766804655136583)
        ·
          refine ⟨171620133464650206982704875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114413422309766804655136583 171620133464650206982704875)
          ·
            refine ⟨257430200196975310474057313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171620133464650206982704875 257430200196975310474057313)
            ·
              refine ⟨193072650147731482855542985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257430200196975310474057313 193072650147731482855542985)
              ·
                refine ⟨144804487610798612141657239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193072650147731482855542985 144804487610798612141657239)
                ·
                  refine ⟨217206731416197918212485859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144804487610798612141657239 217206731416197918212485859)
                  ·
                    refine ⟨325810097124296877318728789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217206731416197918212485859 325810097124296877318728789)
                    ·
                      refine ⟨3818087075675354031078853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 325810097124296877318728789 3818087075675354031078853)
                      ·
                        rfl

theorem cell23_7435698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_7435698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435698 prefixEnd_7435698 := by exact prefixLift 7435698
  have htrace : WordTrace (prefixWord ++ tailWord_7435698) baseStart_7435698 baseEnd_7435698 := by
    simpa [prefixWord, tailWord_7435698, baseEnd_7435698] using wordTrace_append hprefix tailTrace_7435698
  have hstable : (prefixWord ++ tailWord_7435698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435698).length < 2 ^ (prefixWord ++ tailWord_7435698).sum := by decide
  have hdescent : baseEnd_7435698 < baseStart_7435698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435749 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7435749 : Nat := 118140960795 + 7435749 * 2 ^ 59
def prefixEnd_7435749 : Nat := 4983230072969 + 3 ^ 40 * 7435749 * 2
def baseEnd_7435749 : Nat := 3818113263188733331541119

theorem tailTrace_7435749 : CollatzResearch.WordTrace tailWord_7435749 prefixEnd_7435749 3818113263188733331541119 := by
  unfold tailWord_7435749
  simp only [CollatzResearch.WordTrace]
  refine ⟨271204046338558772670430301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180802697559039181780286867 271204046338558772670430301)
  ·
    refine ⟨101701517376959539751411363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271204046338558772670430301 101701517376959539751411363)
    ·
      refine ⟨152552276065439309627117045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101701517376959539751411363 152552276065439309627117045)
      ·
        refine ⟨14301775881134935277542223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152552276065439309627117045 14301775881134935277542223)
        ·
          refine ⟨21452663821702402916313335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14301775881134935277542223 21452663821702402916313335)
          ·
            refine ⟨32178995732553604374470003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21452663821702402916313335 32178995732553604374470003)
            ·
              refine ⟨48268493598830406561705005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32178995732553604374470003 48268493598830406561705005)
              ·
                refine ⟨18100685099561402460639377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48268493598830406561705005 18100685099561402460639377)
                ·
                  refine ⟨13575513824671051845479533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18100685099561402460639377 13575513824671051845479533)
                  ·
                    refine ⟨5090817684251644442054825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13575513824671051845479533 5090817684251644442054825)
                    ·
                      refine ⟨3818113263188733331541119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090817684251644442054825 3818113263188733331541119)
                      ·
                        rfl

theorem cell23_7435749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7435749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435749 prefixEnd_7435749 := by exact prefixLift 7435749
  have htrace : WordTrace (prefixWord ++ tailWord_7435749) baseStart_7435749 baseEnd_7435749 := by
    simpa [prefixWord, tailWord_7435749, baseEnd_7435749] using wordTrace_append hprefix tailTrace_7435749
  have hstable : (prefixWord ++ tailWord_7435749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435749).length < 2 ^ (prefixWord ++ tailWord_7435749).sum := by decide
  have hdescent : baseEnd_7435749 < baseStart_7435749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435755 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 4, 4]
def baseStart_7435755 : Nat := 118140960795 + 7435755 * 2 ^ 59
def prefixEnd_7435755 : Nat := 4983230072969 + 3 ^ 40 * 7435755 * 2
def baseEnd_7435755 : Nat := 1272705448024220102688697

theorem tailTrace_7435755 : CollatzResearch.WordTrace tailWord_7435755 prefixEnd_7435755 1272705448024220102688697 := by
  unfold tailWord_7435755
  simp only [CollatzResearch.WordTrace]
  refine ⟨271204265176537035695148719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180802843451024690463432479 271204265176537035695148719)
  ·
    refine ⟨406806397764805553542723079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271204265176537035695148719 406806397764805553542723079)
    ·
      refine ⟨610209596647208330314084619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406806397764805553542723079 610209596647208330314084619)
      ·
        refine ⟨915314394970812495471126929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610209596647208330314084619 915314394970812495471126929)
        ·
          refine ⟨686485796228109371603345197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915314394970812495471126929 686485796228109371603345197)
          ·
            refine ⟨257432173585541014351254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686485796228109371603345197 257432173585541014351254449)
            ·
              refine ⟨193074130189155760763440837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257432173585541014351254449 193074130189155760763440837)
              ·
                refine ⟨36201399410466705143145157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193074130189155760763440837 36201399410466705143145157)
                ·
                  refine ⟨6787762389462507214339717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36201399410466705143145157 6787762389462507214339717)
                  ·
                    refine ⟨1272705448024220102688697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6787762389462507214339717 1272705448024220102688697)
                    ·
                      rfl

theorem cell23_7435755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 4].length) (baseStart_7435755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435755 prefixEnd_7435755 := by exact prefixLift 7435755
  have htrace : WordTrace (prefixWord ++ tailWord_7435755) baseStart_7435755 baseEnd_7435755 := by
    simpa [prefixWord, tailWord_7435755, baseEnd_7435755] using wordTrace_append hprefix tailTrace_7435755
  have hstable : (prefixWord ++ tailWord_7435755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435755).length < 2 ^ (prefixWord ++ tailWord_7435755).sum := by decide
  have hdescent : baseEnd_7435755 < baseStart_7435755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435768 : List Nat := [2, 1, 2, 1, 1, 16]
def baseStart_7435768 : Nat := 118140960795 + 7435768 * 2 ^ 59
def prefixEnd_7435768 : Nat := 4983230072969 + 3 ^ 40 * 7435768 * 2
def baseEnd_7435768 : Nat := 15712440408729089535817

theorem tailTrace_7435768 : CollatzResearch.WordTrace tailWord_7435768 prefixEnd_7435768 15712440408729089535817 := by
  unfold tailWord_7435768
  simp only [CollatzResearch.WordTrace]
  refine ⟨135602369662744969457685979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180803159550326625943581305 135602369662744969457685979)
  ·
    refine ⟨203403554494117454186528969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135602369662744969457685979 203403554494117454186528969)
    ·
      refine ⟨152552665870588090639896727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203403554494117454186528969 152552665870588090639896727)
      ·
        refine ⟨228828998805882135959845091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152552665870588090639896727 228828998805882135959845091)
        ·
          refine ⟨343243498208823203939767637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228828998805882135959845091 343243498208823203939767637)
          ·
            refine ⟨15712440408729089535817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 343243498208823203939767637 15712440408729089535817)
            ·
              rfl

theorem cell23_7435768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 16].length) (baseStart_7435768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435768 prefixEnd_7435768 := by exact prefixLift 7435768
  have htrace : WordTrace (prefixWord ++ tailWord_7435768) baseStart_7435768 baseEnd_7435768 := by
    simpa [prefixWord, tailWord_7435768, baseEnd_7435768] using wordTrace_append hprefix tailTrace_7435768
  have hstable : (prefixWord ++ tailWord_7435768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435768).length < 2 ^ (prefixWord ++ tailWord_7435768).sum := by decide
  have hdescent : baseEnd_7435768 < baseStart_7435768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435772 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_7435772 : Nat := 118140960795 + 7435772 * 2 ^ 59
def prefixEnd_7435772 : Nat := 4983230072969 + 3 ^ 40 * 7435772 * 2
def baseEnd_7435772 : Nat := 1272708357747928913851171

theorem tailTrace_7435772 : CollatzResearch.WordTrace tailWord_7435772 prefixEnd_7435772 1272708357747928913851171 := by
  unfold tailWord_7435772
  simp only [CollatzResearch.WordTrace]
  refine ⟨135602442608737723799258785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180803256811650298399011713 135602442608737723799258785)
  ·
    refine ⟨101701831956553292849444089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135602442608737723799258785 101701831956553292849444089)
    ·
      refine ⟨76276373967414969637083067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101701831956553292849444089 76276373967414969637083067)
      ·
        refine ⟨114414560951122454455624601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76276373967414969637083067 114414560951122454455624601)
        ·
          refine ⟨85810920713341840841718451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114414560951122454455624601 85810920713341840841718451)
          ·
            refine ⟨128716381070012761262577677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85810920713341840841718451 128716381070012761262577677)
            ·
              refine ⟨48268642901254785473466629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128716381070012761262577677 48268642901254785473466629)
              ·
                refine ⟨9050370543985272276274993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48268642901254785473466629 9050370543985272276274993)
                ·
                  refine ⟨6787777907988954207206245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9050370543985272276274993 6787777907988954207206245)
                  ·
                    refine ⟨1272708357747928913851171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6787777907988954207206245 1272708357747928913851171)
                    ·
                      rfl

theorem cell23_7435772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_7435772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435772 prefixEnd_7435772 := by exact prefixLift 7435772
  have htrace : WordTrace (prefixWord ++ tailWord_7435772) baseStart_7435772 baseEnd_7435772 := by
    simpa [prefixWord, tailWord_7435772, baseEnd_7435772] using wordTrace_append hprefix tailTrace_7435772
  have hstable : (prefixWord ++ tailWord_7435772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435772).length < 2 ^ (prefixWord ++ tailWord_7435772).sum := by decide
  have hdescent : baseEnd_7435772 < baseStart_7435772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435773 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 1, 1, 3]
def baseStart_7435773 : Nat := 118140960795 + 7435773 * 2 ^ 59
def prefixEnd_7435773 : Nat := 4983230072969 + 3 ^ 40 * 7435773 * 2
def baseEnd_7435773 : Nat := 3818125586724441237641009

theorem tailTrace_7435773 : CollatzResearch.WordTrace tailWord_7435773 prefixEnd_7435773 3818125586724441237641009 := by
  unfold tailWord_7435773
  simp only [CollatzResearch.WordTrace]
  refine ⟨271204921690471824769303973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180803281126981216512869315 271204921690471824769303973)
  ·
    refine ⟨50850922816963467144244495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271204921690471824769303973 50850922816963467144244495)
    ·
      refine ⟨76276384225445200716366743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50850922816963467144244495 76276384225445200716366743)
      ·
        refine ⟨114414576338167801074550115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76276384225445200716366743 114414576338167801074550115)
        ·
          refine ⟨171621864507251701611825173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114414576338167801074550115 171621864507251701611825173)
          ·
            refine ⟨8044774898777423513054305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171621864507251701611825173 8044774898777423513054305)
            ·
              refine ⟨6033581174083067634790729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8044774898777423513054305 6033581174083067634790729)
              ·
                refine ⟨4525185880562300726093047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033581174083067634790729 4525185880562300726093047)
                ·
                  refine ⟨6787778820843451089139571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525185880562300726093047 6787778820843451089139571)
                  ·
                    refine ⟨10181668231265176633709357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6787778820843451089139571 10181668231265176633709357)
                    ·
                      refine ⟨3818125586724441237641009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10181668231265176633709357 3818125586724441237641009)
                      ·
                        rfl

theorem cell23_7435773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_7435773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435773 prefixEnd_7435773 := by exact prefixLift 7435773
  have htrace : WordTrace (prefixWord ++ tailWord_7435773) baseStart_7435773 baseEnd_7435773 := by
    simpa [prefixWord, tailWord_7435773, baseEnd_7435773] using wordTrace_append hprefix tailTrace_7435773
  have hstable : (prefixWord ++ tailWord_7435773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435773).length < 2 ^ (prefixWord ++ tailWord_7435773).sum := by decide
  have hdescent : baseEnd_7435773 < baseStart_7435773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435816 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7435816 : Nat := 118140960795 + 7435816 * 2 ^ 59
def prefixEnd_7435816 : Nat := 4983230072969 + 3 ^ 40 * 7435816 * 2
def baseEnd_7435816 : Nat := 3818147666392584569403311

theorem tailTrace_7435816 : CollatzResearch.WordTrace tailWord_7435816 prefixEnd_7435816 3818147666392584569403311 := by
  unfold tailWord_7435816
  simp only [CollatzResearch.WordTrace]
  refine ⟨135603245014658021556559651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180804326686210695408746201 135603245014658021556559651)
  ·
    refine ⟨203404867521987032334839477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135603245014658021556559651 203404867521987032334839477)
    ·
      refine ⟨19069206330186284281391201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203404867521987032334839477 19069206330186284281391201)
      ·
        refine ⟨14301904747639713211043401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19069206330186284281391201 14301904747639713211043401)
        ·
          refine ⟨10726428560729784908282551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14301904747639713211043401 10726428560729784908282551)
          ·
            refine ⟨16089642841094677362423827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726428560729784908282551 16089642841094677362423827)
            ·
              refine ⟨24134464261642016043635741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16089642841094677362423827 24134464261642016043635741)
              ·
                refine ⟨9050424098115756016363403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24134464261642016043635741 9050424098115756016363403)
                ·
                  refine ⟨13575636147173634024545105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9050424098115756016363403 13575636147173634024545105)
                  ·
                    refine ⟨10181727110380225518408829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13575636147173634024545105 10181727110380225518408829)
                    ·
                      refine ⟨3818147666392584569403311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10181727110380225518408829 3818147666392584569403311)
                      ·
                        rfl

theorem cell23_7435816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7435816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435816 prefixEnd_7435816 := by exact prefixLift 7435816
  have htrace : WordTrace (prefixWord ++ tailWord_7435816) baseStart_7435816 baseEnd_7435816 := by
    simpa [prefixWord, tailWord_7435816, baseEnd_7435816] using wordTrace_append hprefix tailTrace_7435816
  have hstable : (prefixWord ++ tailWord_7435816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435816).length < 2 ^ (prefixWord ++ tailWord_7435816).sum := by decide
  have hdescent : baseEnd_7435816 < baseStart_7435816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435829 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_7435829 : Nat := 118140960795 + 7435829 * 2 ^ 59
def prefixEnd_7435829 : Nat := 4983230072969 + 3 ^ 40 * 7435829 * 2
def baseEnd_7435829 : Nat := 3818154341641093018540751

theorem tailTrace_7435829 : CollatzResearch.WordTrace tailWord_7435829 prefixEnd_7435829 3818154341641093018540751 := by
  unfold tailWord_7435829
  simp only [CollatzResearch.WordTrace]
  refine ⟨271206964178268946333342541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180804642785512630888895027 271206964178268946333342541)
  ·
    refine ⟨101702611566850854875003453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271206964178268946333342541 101702611566850854875003453)
    ·
      refine ⟨38138479337569070578126295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101702611566850854875003453 38138479337569070578126295)
      ·
        refine ⟨57207719006353605867189443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38138479337569070578126295 57207719006353605867189443)
        ·
          refine ⟨85811578509530408800784165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57207719006353605867189443 85811578509530408800784165)
          ·
            refine ⟨16089670970536951650147031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85811578509530408800784165 16089670970536951650147031)
            ·
              refine ⟨24134506455805427475220547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16089670970536951650147031 24134506455805427475220547)
              ·
                refine ⟨36201759683708141212830821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24134506455805427475220547 36201759683708141212830821)
                ·
                  refine ⟨6787829940695276477405779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36201759683708141212830821 6787829940695276477405779)
                  ·
                    refine ⟨10181744911042914716108669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6787829940695276477405779 10181744911042914716108669)
                    ·
                      refine ⟨3818154341641093018540751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10181744911042914716108669 3818154341641093018540751)
                      ·
                        rfl

theorem cell23_7435829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_7435829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435829 prefixEnd_7435829 := by exact prefixLift 7435829
  have htrace : WordTrace (prefixWord ++ tailWord_7435829) baseStart_7435829 baseEnd_7435829 := by
    simpa [prefixWord, tailWord_7435829, baseEnd_7435829] using wordTrace_append hprefix tailTrace_7435829
  have hstable : (prefixWord ++ tailWord_7435829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435829).length < 2 ^ (prefixWord ++ tailWord_7435829).sum := by decide
  have hdescent : baseEnd_7435829 < baseStart_7435829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435845 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_7435845 : Nat := 118140960795 + 7435845 * 2 ^ 59
def prefixEnd_7435845 : Nat := 4983230072969 + 3 ^ 40 * 7435845 * 2
def baseEnd_7435845 : Nat := 1272720852443854985313559

theorem tailTrace_7435845 : CollatzResearch.WordTrace tailWord_7435845 prefixEnd_7435845 1272720852443854985313559 := by
  unfold tailWord_7435845
  simp only [CollatzResearch.WordTrace]
  refine ⟨271207547746210981065924989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180805031830807320710616659 271207547746210981065924989)
  ·
    refine ⟨101702830404829117899721871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271207547746210981065924989 101702830404829117899721871)
    ·
      refine ⟨152554245607243676849582807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101702830404829117899721871 152554245607243676849582807)
      ·
        refine ⟨228831368410865515274374211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152554245607243676849582807 228831368410865515274374211)
        ·
          refine ⟨343247052616298272911561317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228831368410865515274374211 343247052616298272911561317)
          ·
            refine ⟨64358822365555926170917747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343247052616298272911561317 64358822365555926170917747)
            ·
              refine ⟨96538233548333889256376621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64358822365555926170917747 96538233548333889256376621)
              ·
                refine ⟨36201837580625208471141233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96538233548333889256376621 36201837580625208471141233)
                ·
                  refine ⟨27151378185468906353355925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36201837580625208471141233 27151378185468906353355925)
                  ·
                    refine ⟨1272720852443854985313559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27151378185468906353355925 1272720852443854985313559)
                    ·
                      rfl

theorem cell23_7435845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_7435845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435845 prefixEnd_7435845 := by exact prefixLift 7435845
  have htrace : WordTrace (prefixWord ++ tailWord_7435845) baseStart_7435845 baseEnd_7435845 := by
    simpa [prefixWord, tailWord_7435845, baseEnd_7435845] using wordTrace_append hprefix tailTrace_7435845
  have hstable : (prefixWord ++ tailWord_7435845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435845).length < 2 ^ (prefixWord ++ tailWord_7435845).sum := by decide
  have hdescent : baseEnd_7435845 < baseStart_7435845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435855 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_7435855 : Nat := 118140960795 + 7435855 * 2 ^ 59
def prefixEnd_7435855 : Nat := 4983230072969 + 3 ^ 40 * 7435855 * 2
def baseEnd_7435855 : Nat := 3818167692138109916815631

theorem tailTrace_7435855 : CollatzResearch.WordTrace tailWord_7435855 prefixEnd_7435855 3818167692138109916815631 := by
  unfold tailWord_7435855
  simp only [CollatzResearch.WordTrace]
  refine ⟨271207912476174752773789019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180805274984116501849192679 271207912476174752773789019)
  ·
    refine ⟨406811868714262129160683529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271207912476174752773789019 406811868714262129160683529)
    ·
      refine ⟨305108901535696596870512647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406811868714262129160683529 305108901535696596870512647)
      ·
        refine ⟨457663352303544895305768971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305108901535696596870512647 457663352303544895305768971)
        ·
          refine ⟨686495028455317342958653457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457663352303544895305768971 686495028455317342958653457)
          ·
            refine ⟨514871271341488007218990093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686495028455317342958653457 514871271341488007218990093)
            ·
              refine ⟨193076726753058002707121285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514871271341488007218990093 193076726753058002707121285)
              ·
                refine ⟨36201886266198375507585241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193076726753058002707121285 36201886266198375507585241)
                ·
                  refine ⟨27151414699648781630688931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36201886266198375507585241 27151414699648781630688931)
                  ·
                    refine ⟨40727122049473172446033397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27151414699648781630688931 40727122049473172446033397)
                    ·
                      refine ⟨3818167692138109916815631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40727122049473172446033397 3818167692138109916815631)
                      ·
                        rfl

theorem cell23_7435855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_7435855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435855 prefixEnd_7435855 := by exact prefixLift 7435855
  have htrace : WordTrace (prefixWord ++ tailWord_7435855) baseStart_7435855 baseEnd_7435855 := by
    simpa [prefixWord, tailWord_7435855, baseEnd_7435855] using wordTrace_append hprefix tailTrace_7435855
  have hstable : (prefixWord ++ tailWord_7435855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435855).length < 2 ^ (prefixWord ++ tailWord_7435855).sum := by decide
  have hdescent : baseEnd_7435855 < baseStart_7435855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435865 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_7435865 : Nat := 118140960795 + 7435865 * 2 ^ 59
def prefixEnd_7435865 : Nat := 4983230072969 + 3 ^ 40 * 7435865 * 2
def baseEnd_7435865 : Nat := 3818172826944654877690585

theorem tailTrace_7435865 : CollatzResearch.WordTrace tailWord_7435865 prefixEnd_7435865 3818172826944654877690585 := by
  unfold tailWord_7435865
  simp only [CollatzResearch.WordTrace]
  refine ⟨271208277206138524481653049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180805518137425682987768699 271208277206138524481653049)
  ·
    refine ⟨203406207904603893361239787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271208277206138524481653049 203406207904603893361239787)
    ·
      refine ⟨305109311856905840041859681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203406207904603893361239787 305109311856905840041859681)
      ·
        refine ⟨228831983892679380031394761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305109311856905840041859681 228831983892679380031394761)
        ·
          refine ⟨171623987919509535023546071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228831983892679380031394761 171623987919509535023546071)
          ·
            refine ⟨257435981879264302535319107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171623987919509535023546071 257435981879264302535319107)
            ·
              refine ⟨386153972818896453802978661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257435981879264302535319107 386153972818896453802978661)
              ·
                refine ⟨72403869903543085088058499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386153972818896453802978661 72403869903543085088058499)
                ·
                  refine ⟨108605804855314627632087749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72403869903543085088058499 108605804855314627632087749)
                  ·
                    refine ⟨20363588410371492681016453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108605804855314627632087749 20363588410371492681016453)
                    ·
                      refine ⟨3818172826944654877690585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20363588410371492681016453 3818172826944654877690585)
                      ·
                        rfl

theorem cell23_7435865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_7435865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435865 prefixEnd_7435865 := by exact prefixLift 7435865
  have htrace : WordTrace (prefixWord ++ tailWord_7435865) baseStart_7435865 baseEnd_7435865 := by
    simpa [prefixWord, tailWord_7435865, baseEnd_7435865] using wordTrace_append hprefix tailTrace_7435865
  have hstable : (prefixWord ++ tailWord_7435865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435865).length < 2 ^ (prefixWord ++ tailWord_7435865).sum := by decide
  have hdescent : baseEnd_7435865 < baseStart_7435865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435915 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_7435915 : Nat := 118140960795 + 7435915 * 2 ^ 59
def prefixEnd_7435915 : Nat := 4983230072969 + 3 ^ 40 * 7435915 * 2
def baseEnd_7435915 : Nat := 3818198500977379682065355

theorem tailTrace_7435915 : CollatzResearch.WordTrace tailWord_7435915 prefixEnd_7435915 3818198500977379682065355 := by
  unfold tailWord_7435915
  simp only [CollatzResearch.WordTrace]
  refine ⟨271210100855957383020973199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180806733903971588680648799 271210100855957383020973199)
  ·
    refine ⟨406815151283936074531459799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271210100855957383020973199 406815151283936074531459799)
    ·
      refine ⟨610222726925904111797189699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406815151283936074531459799 610222726925904111797189699)
      ·
        refine ⟨915334090388856167695784549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610222726925904111797189699 915334090388856167695784549)
        ·
          refine ⟨171625141947910531442959603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 915334090388856167695784549 171625141947910531442959603)
          ·
            refine ⟨257437712921865797164439405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171625141947910531442959603 257437712921865797164439405)
            ·
              refine ⟨96539142345699673936664777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257437712921865797164439405 96539142345699673936664777)
              ·
                refine ⟨72404356759274755452498583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96539142345699673936664777 72404356759274755452498583)
                ·
                  refine ⟨108606535138912133178747875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72404356759274755452498583 108606535138912133178747875)
                  ·
                    refine ⟨162909802708368199768121813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108606535138912133178747875 162909802708368199768121813)
                    ·
                      refine ⟨3818198500977379682065355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162909802708368199768121813 3818198500977379682065355)
                      ·
                        rfl

theorem cell23_7435915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_7435915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435915 prefixEnd_7435915 := by exact prefixLift 7435915
  have htrace : WordTrace (prefixWord ++ tailWord_7435915) baseStart_7435915 baseEnd_7435915 := by
    simpa [prefixWord, tailWord_7435915, baseEnd_7435915] using wordTrace_append hprefix tailTrace_7435915
  have hstable : (prefixWord ++ tailWord_7435915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435915).length < 2 ^ (prefixWord ++ tailWord_7435915).sum := by decide
  have hdescent : baseEnd_7435915 < baseStart_7435915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435959 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 6, 2]
def baseStart_7435959 : Nat := 118140960795 + 7435959 * 2 ^ 59
def prefixEnd_7435959 : Nat := 4983230072969 + 3 ^ 40 * 7435959 * 2
def baseEnd_7435959 : Nat := 3818221094126177509915153

theorem tailTrace_7435959 : CollatzResearch.WordTrace tailWord_7435959 prefixEnd_7435959 3818221094126177509915153 := by
  unfold tailWord_7435959
  simp only [CollatzResearch.WordTrace]
  refine ⟨271211705667797978535574931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180807803778531985690383287 271211705667797978535574931)
  ·
    refine ⟨406817558501696967803362397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271211705667797978535574931 406817558501696967803362397)
    ·
      refine ⟨152556584438136362926260899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406817558501696967803362397 152556584438136362926260899)
      ·
        refine ⟨228834876657204544389391349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152556584438136362926260899 228834876657204544389391349)
        ·
          refine ⟨21453269686612926036505439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228834876657204544389391349 21453269686612926036505439)
          ·
            refine ⟨32179904529919389054758159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453269686612926036505439 32179904529919389054758159)
            ·
              refine ⟨48269856794879083582137239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32179904529919389054758159 48269856794879083582137239)
              ·
                refine ⟨72404785192318625373205859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48269856794879083582137239 72404785192318625373205859)
                ·
                  refine ⟨108607177788477938059808789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72404785192318625373205859 108607177788477938059808789)
                  ·
                    refine ⟨5090961458834903346553537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108607177788477938059808789 5090961458834903346553537)
                    ·
                      refine ⟨3818221094126177509915153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5090961458834903346553537 3818221094126177509915153)
                      ·
                        rfl

theorem cell23_7435959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_7435959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435959 prefixEnd_7435959 := by exact prefixLift 7435959
  have htrace : WordTrace (prefixWord ++ tailWord_7435959) baseStart_7435959 baseEnd_7435959 := by
    simpa [prefixWord, tailWord_7435959, baseEnd_7435959] using wordTrace_append hprefix tailTrace_7435959
  have hstable : (prefixWord ++ tailWord_7435959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435959).length < 2 ^ (prefixWord ++ tailWord_7435959).sum := by decide
  have hdescent : baseEnd_7435959 < baseStart_7435959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7435982 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_7435982 : Nat := 118140960795 + 7435982 * 2 ^ 59
def prefixEnd_7435982 : Nat := 4983230072969 + 3 ^ 40 * 7435982 * 2
def baseEnd_7435982 : Nat := 424248100464581213325283

theorem tailTrace_7435982 : CollatzResearch.WordTrace tailWord_7435982 prefixEnd_7435982 424248100464581213325283 := by
  unfold tailWord_7435982
  simp only [CollatzResearch.WordTrace]
  refine ⟨33901568068339331682957775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180808363031143102309108133 33901568068339331682957775)
  ·
    refine ⟨50852352102508997524436663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33901568068339331682957775 50852352102508997524436663)
    ·
      refine ⟨76278528153763496286654995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50852352102508997524436663 76278528153763496286654995)
      ·
        refine ⟨114417792230645244429982493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76278528153763496286654995 114417792230645244429982493)
        ·
          refine ⟨42906672086491966661243435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114417792230645244429982493 42906672086491966661243435)
          ·
            refine ⟨64360008129737949991865153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42906672086491966661243435 64360008129737949991865153)
            ·
              refine ⟨48270006097303462493898865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64360008129737949991865153 48270006097303462493898865)
              ·
                refine ⟨36202504572977596870424149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48270006097303462493898865 36202504572977596870424149)
                ·
                  refine ⟨424248100464581213325283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36202504572977596870424149 424248100464581213325283)
                  ·
                    rfl

theorem cell23_7435982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_7435982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7435982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7435982 prefixEnd_7435982 := by exact prefixLift 7435982
  have htrace : WordTrace (prefixWord ++ tailWord_7435982) baseStart_7435982 baseEnd_7435982 := by
    simpa [prefixWord, tailWord_7435982, baseEnd_7435982] using wordTrace_append hprefix tailTrace_7435982
  have hstable : (prefixWord ++ tailWord_7435982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7435982).length < 2 ^ (prefixWord ++ tailWord_7435982).sum := by decide
  have hdescent : baseEnd_7435982 < baseStart_7435982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7435982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436012 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_7436012 : Nat := 118140960795 + 7436012 * 2 ^ 59
def prefixEnd_7436012 : Nat := 4983230072969 + 3 ^ 40 * 7436012 * 2
def baseEnd_7436012 : Nat := 1272749436200288600850803

theorem tailTrace_7436012 : CollatzResearch.WordTrace tailWord_7436012 prefixEnd_7436012 1272749436200288600850803 := by
  unfold tailWord_7436012
  simp only [CollatzResearch.WordTrace]
  refine ⟨135606819368302984293627145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180809092491070645724836193 135606819368302984293627145)
  ·
    refine ⟨101705114526227238220220359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135606819368302984293627145 101705114526227238220220359)
    ·
      refine ⟨152557671789340857330330539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101705114526227238220220359 152557671789340857330330539)
      ·
        refine ⟨228836507684011285995495809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152557671789340857330330539 228836507684011285995495809)
        ·
          refine ⟨171627380763008464496621857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228836507684011285995495809 171627380763008464496621857)
          ·
            refine ⟨128720535572256348372466393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171627380763008464496621857 128720535572256348372466393)
            ·
              refine ⟨96540401679192261279349795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128720535572256348372466393 96540401679192261279349795)
              ·
                refine ⟨144810602518788391919024693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96540401679192261279349795 144810602518788391919024693)
                ·
                  refine ⟨13575993986136411742408565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144810602518788391919024693 13575993986136411742408565)
                  ·
                    refine ⟨1272749436200288600850803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13575993986136411742408565 1272749436200288600850803)
                    ·
                      rfl

theorem cell23_7436012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_7436012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436012 prefixEnd_7436012 := by exact prefixLift 7436012
  have htrace : WordTrace (prefixWord ++ tailWord_7436012) baseStart_7436012 baseEnd_7436012 := by
    simpa [prefixWord, tailWord_7436012, baseEnd_7436012] using wordTrace_append hprefix tailTrace_7436012
  have hstable : (prefixWord ++ tailWord_7436012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436012).length < 2 ^ (prefixWord ++ tailWord_7436012).sum := by decide
  have hdescent : baseEnd_7436012 < baseStart_7436012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436019 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 1, 5, 2]
def baseStart_7436019 : Nat := 118140960795 + 7436019 * 2 ^ 59
def prefixEnd_7436019 : Nat := 4983230072969 + 3 ^ 40 * 7436019 * 2
def baseEnd_7436019 : Nat := 3818251902965447275164877

theorem tailTrace_7436019 : CollatzResearch.WordTrace tailWord_7436019 prefixEnd_7436019 3818251902965447275164877 := by
  unfold tailWord_7436019
  simp only [CollatzResearch.WordTrace]
  refine ⟨271213894047580608782759111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180809262698387072521839407 271213894047580608782759111)
  ·
    refine ⟨406820841071370913174138667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271213894047580608782759111 406820841071370913174138667)
    ·
      refine ⟨610231261607056369761208001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406820841071370913174138667 610231261607056369761208001)
      ·
        refine ⟨457673446205292277320906001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610231261607056369761208001 457673446205292277320906001)
        ·
          refine ⟨343255084653969207990679501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457673446205292277320906001 343255084653969207990679501)
          ·
            refine ⟨128720656745238452996504813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343255084653969207990679501 128720656745238452996504813)
            ·
              refine ⟨48270246279464419873689305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128720656745238452996504813 48270246279464419873689305)
              ·
                refine ⟨36202684709598314905266979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48270246279464419873689305 36202684709598314905266979)
                ·
                  refine ⟨54304027064397472357900469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36202684709598314905266979 54304027064397472357900469)
                  ·
                    refine ⟨5091002537287263033553169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54304027064397472357900469 5091002537287263033553169)
                    ·
                      refine ⟨3818251902965447275164877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091002537287263033553169 3818251902965447275164877)
                      ·
                        rfl

theorem cell23_7436019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 5, 2].length) (baseStart_7436019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436019 prefixEnd_7436019 := by exact prefixLift 7436019
  have htrace : WordTrace (prefixWord ++ tailWord_7436019) baseStart_7436019 baseEnd_7436019 := by
    simpa [prefixWord, tailWord_7436019, baseEnd_7436019] using wordTrace_append hprefix tailTrace_7436019
  have hstable : (prefixWord ++ tailWord_7436019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436019).length < 2 ^ (prefixWord ++ tailWord_7436019).sum := by decide
  have hdescent : baseEnd_7436019 < baseStart_7436019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436036 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_7436036 : Nat := 118140960795 + 7436036 * 2 ^ 59
def prefixEnd_7436036 : Nat := 4983230072969 + 3 ^ 40 * 7436036 * 2
def baseEnd_7436036 : Nat := 3818260632136573708652299

theorem tailTrace_7436036 : CollatzResearch.WordTrace tailWord_7436036 prefixEnd_7436036 3818260632136573708652299 := by
  unfold tailWord_7436036
  simp only [CollatzResearch.WordTrace]
  refine ⟨135607257044259510343063981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180809676059012680457418641 135607257044259510343063981)
  ·
    refine ⟨50852721391597316378648993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135607257044259510343063981 50852721391597316378648993)
    ·
      refine ⟨38139541043697987283986745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50852721391597316378648993 38139541043697987283986745)
      ·
        refine ⟨28604655782773490462990059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38139541043697987283986745 28604655782773490462990059)
        ·
          refine ⟨42906983674160235694485089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28604655782773490462990059 42906983674160235694485089)
          ·
            refine ⟨32180237755620176770863817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42906983674160235694485089 32180237755620176770863817)
            ·
              refine ⟨24135178316715132578147863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32180237755620176770863817 24135178316715132578147863)
              ·
                refine ⟨36202767475072698867221795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24135178316715132578147863 36202767475072698867221795)
                ·
                  refine ⟨54304151212609048300832693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36202767475072698867221795 54304151212609048300832693)
                  ·
                    refine ⟨5091014176182098278203065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54304151212609048300832693 5091014176182098278203065)
                    ·
                      refine ⟨3818260632136573708652299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091014176182098278203065 3818260632136573708652299)
                      ·
                        rfl

theorem cell23_7436036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_7436036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436036 prefixEnd_7436036 := by exact prefixLift 7436036
  have htrace : WordTrace (prefixWord ++ tailWord_7436036) baseStart_7436036 baseEnd_7436036 := by
    simpa [prefixWord, tailWord_7436036, baseEnd_7436036] using wordTrace_append hprefix tailTrace_7436036
  have hstable : (prefixWord ++ tailWord_7436036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436036).length < 2 ^ (prefixWord ++ tailWord_7436036).sum := by decide
  have hdescent : baseEnd_7436036 < baseStart_7436036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436043 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 1, 1, 3]
def baseStart_7436043 : Nat := 118140960795 + 7436043 * 2 ^ 59
def prefixEnd_7436043 : Nat := 4983230072969 + 3 ^ 40 * 7436043 * 2
def baseEnd_7436043 : Nat := 3818264226501155181264767

theorem tailTrace_7436043 : CollatzResearch.WordTrace tailWord_7436043 prefixEnd_7436043 3818264226501155181264767 := by
  unfold tailWord_7436043
  simp only [CollatzResearch.WordTrace]
  refine ⟨271214769399493660881632783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180809846266329107254421855 271214769399493660881632783)
  ·
    refine ⟨406822154099240491322449175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271214769399493660881632783 406822154099240491322449175)
    ·
      refine ⟨610233231148860736983673763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406822154099240491322449175 610233231148860736983673763)
      ·
        refine ⟨915349846723291105475510645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610233231148860736983673763 915349846723291105475510645)
        ·
          refine ⟨85814048130308541138329123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 915349846723291105475510645 85814048130308541138329123)
          ·
            refine ⟨128721072195462811707493685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85814048130308541138329123 128721072195462811707493685)
            ·
              refine ⟨12067600518324638597577533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128721072195462811707493685 12067600518324638597577533)
              ·
                refine ⟨4525350194371739474091575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12067600518324638597577533 4525350194371739474091575)
                ·
                  refine ⟨6788025291557609211137363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525350194371739474091575 6788025291557609211137363)
                  ·
                    refine ⟨10182037937336413816706045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788025291557609211137363 10182037937336413816706045)
                    ·
                      refine ⟨3818264226501155181264767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10182037937336413816706045 3818264226501155181264767)
                      ·
                        rfl

theorem cell23_7436043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 1, 3].length) (baseStart_7436043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436043 prefixEnd_7436043 := by exact prefixLift 7436043
  have htrace : WordTrace (prefixWord ++ tailWord_7436043) baseStart_7436043 baseEnd_7436043 := by
    simpa [prefixWord, tailWord_7436043, baseEnd_7436043] using wordTrace_append hprefix tailTrace_7436043
  have hstable : (prefixWord ++ tailWord_7436043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436043).length < 2 ^ (prefixWord ++ tailWord_7436043).sum := by decide
  have hdescent : baseEnd_7436043 < baseStart_7436043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436060 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_7436060 : Nat := 118140960795 + 7436060 * 2 ^ 59
def prefixEnd_7436060 : Nat := 4983230072969 + 3 ^ 40 * 7436060 * 2
def baseEnd_7436060 : Nat := 3818272955672281614752189

theorem tailTrace_7436060 : CollatzResearch.WordTrace tailWord_7436060 prefixEnd_7436060 3818272955672281614752189 := by
  unfold tailWord_7436060
  simp only [CollatzResearch.WordTrace]
  refine ⟨135607694720216036392500817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180810259626954715190001089 135607694720216036392500817)
  ·
    refine ⟨101705771040162027294375613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135607694720216036392500817 101705771040162027294375613)
    ·
      refine ⟨38139664140060760235390855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101705771040162027294375613 38139664140060760235390855)
      ·
        refine ⟨57209496210091140353086283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38139664140060760235390855 57209496210091140353086283)
        ·
          refine ⟨85814244315136710529629425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57209496210091140353086283 85814244315136710529629425)
          ·
            refine ⟨64360683236352532897222069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85814244315136710529629425 64360683236352532897222069)
            ·
              refine ⟨6033814053408049959114569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64360683236352532897222069 6033814053408049959114569)
              ·
                refine ⟨4525360540056037469335927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033814053408049959114569 4525360540056037469335927)
                ·
                  refine ⟨6788040810084056204003891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525360540056037469335927 6788040810084056204003891)
                  ·
                    refine ⟨10182061215126084306005837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788040810084056204003891 10182061215126084306005837)
                    ·
                      refine ⟨3818272955672281614752189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10182061215126084306005837 3818272955672281614752189)
                      ·
                        rfl

theorem cell23_7436060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_7436060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436060 prefixEnd_7436060 := by exact prefixLift 7436060
  have htrace : WordTrace (prefixWord ++ tailWord_7436060) baseStart_7436060 baseEnd_7436060 := by
    simpa [prefixWord, tailWord_7436060, baseEnd_7436060] using wordTrace_append hprefix tailTrace_7436060
  have hstable : (prefixWord ++ tailWord_7436060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436060).length < 2 ^ (prefixWord ++ tailWord_7436060).sum := by decide
  have hdescent : baseEnd_7436060 < baseStart_7436060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436069 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_7436069 : Nat := 118140960795 + 7436069 * 2 ^ 59
def prefixEnd_7436069 : Nat := 4983230072969 + 3 ^ 40 * 7436069 * 2
def baseEnd_7436069 : Nat := 3818277576998172079539647

theorem tailTrace_7436069 : CollatzResearch.WordTrace tailWord_7436069 prefixEnd_7436069 3818277576998172079539647 := by
  unfold tailWord_7436069
  simp only [CollatzResearch.WordTrace]
  refine ⟨271215717697399467322079261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180810478464932978214719507 271215717697399467322079261)
  ·
    refine ⟨101705894136524800245779723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271215717697399467322079261 101705894136524800245779723)
    ·
      refine ⟨152558841204787200368669585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101705894136524800245779723 152558841204787200368669585)
      ·
        refine ⟨114419130903590400276502189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152558841204787200368669585 114419130903590400276502189)
        ·
          refine ⟨42907174088846400103688321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114419130903590400276502189 42907174088846400103688321)
          ·
            refine ⟨32180380566634800077766241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42907174088846400103688321 32180380566634800077766241)
            ·
              refine ⟨24135285424976100058324681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32180380566634800077766241 24135285424976100058324681)
              ·
                refine ⟨18101464068732075043743511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24135285424976100058324681 18101464068732075043743511)
                ·
                  refine ⟨27152196103098112565615267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18101464068732075043743511 27152196103098112565615267)
                  ·
                    refine ⟨40728294154647168848422901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27152196103098112565615267 40728294154647168848422901)
                    ·
                      refine ⟨3818277576998172079539647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40728294154647168848422901 3818277576998172079539647)
                      ·
                        rfl

theorem cell23_7436069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_7436069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436069 prefixEnd_7436069 := by exact prefixLift 7436069
  have htrace : WordTrace (prefixWord ++ tailWord_7436069) baseStart_7436069 baseEnd_7436069 := by
    simpa [prefixWord, tailWord_7436069, baseEnd_7436069] using wordTrace_append hprefix tailTrace_7436069
  have hstable : (prefixWord ++ tailWord_7436069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436069).length < 2 ^ (prefixWord ++ tailWord_7436069).sum := by decide
  have hdescent : baseEnd_7436069 < baseStart_7436069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436076 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_7436076 : Nat := 118140960795 + 7436076 * 2 ^ 59
def prefixEnd_7436076 : Nat := 4983230072969 + 3 ^ 40 * 7436076 * 2
def baseEnd_7436076 : Nat := 1272760390454251184050705

theorem tailTrace_7436076 : CollatzResearch.WordTrace tailWord_7436076 prefixEnd_7436076 1272760390454251184050705 := by
  unfold tailWord_7436076
  simp only [CollatzResearch.WordTrace]
  refine ⟨135607986504187053758792041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180810648672249405011722721 135607986504187053758792041)
  ·
    refine ⟨101705989878140290319094031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135607986504187053758792041 101705989878140290319094031)
    ·
      refine ⟨152558984817210435478641047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101705989878140290319094031 152558984817210435478641047)
      ·
        refine ⟨228838477225815653217961571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152558984817210435478641047 228838477225815653217961571)
        ·
          refine ⟨343257715838723479826942357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228838477225815653217961571 343257715838723479826942357)
          ·
            refine ⟨16090205429940163116887923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 343257715838723479826942357 16090205429940163116887923)
            ·
              refine ⟨24135308144910244675331885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16090205429940163116887923 24135308144910244675331885)
              ·
                refine ⟨9050740554341341753249457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24135308144910244675331885 9050740554341341753249457)
                ·
                  refine ⟨6788055415756006314937093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9050740554341341753249457 6788055415756006314937093)
                  ·
                    refine ⟨1272760390454251184050705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788055415756006314937093 1272760390454251184050705)
                    ·
                      rfl

theorem cell23_7436076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_7436076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436076 prefixEnd_7436076 := by exact prefixLift 7436076
  have htrace : WordTrace (prefixWord ++ tailWord_7436076) baseStart_7436076 baseEnd_7436076 := by
    simpa [prefixWord, tailWord_7436076, baseEnd_7436076] using wordTrace_append hprefix tailTrace_7436076
  have hstable : (prefixWord ++ tailWord_7436076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436076).length < 2 ^ (prefixWord ++ tailWord_7436076).sum := by decide
  have hdescent : baseEnd_7436076 < baseStart_7436076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436083 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 4]
def baseStart_7436083 : Nat := 118140960795 + 7436083 * 2 ^ 59
def prefixEnd_7436083 : Nat := 4983230072969 + 3 ^ 40 * 7436083 * 2
def baseEnd_7436083 : Nat := 3818284765727335024764583

theorem tailTrace_7436083 : CollatzResearch.WordTrace tailWord_7436083 prefixEnd_7436083 3818284765727335024764583 := by
  unfold tailWord_7436083
  simp only [CollatzResearch.WordTrace]
  refine ⟨271216228319348747713088903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180810818879565831808725935 271216228319348747713088903)
  ·
    refine ⟨406824342479023121569633355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271216228319348747713088903 406824342479023121569633355)
    ·
      refine ⟨610236513718534682354450033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406824342479023121569633355 610236513718534682354450033)
      ·
        refine ⟨457677385288901011765837525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610236513718534682354450033 457677385288901011765837525)
        ·
          refine ⟨10726813717708617463261817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 457677385288901011765837525 10726813717708617463261817)
          ·
            refine ⟨8045110288281463097446363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10726813717708617463261817 8045110288281463097446363)
            ·
              refine ⟨12067665432422194646169545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045110288281463097446363 12067665432422194646169545)
              ·
                refine ⟨9050749074316645984627159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12067665432422194646169545 9050749074316645984627159)
                ·
                  refine ⟨13576123611474968976940739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9050749074316645984627159 13576123611474968976940739)
                  ·
                    refine ⟨20364185417212453465411109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13576123611474968976940739 20364185417212453465411109)
                    ·
                      refine ⟨3818284765727335024764583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20364185417212453465411109 3818284765727335024764583)
                      ·
                        rfl

theorem cell23_7436083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_7436083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436083 prefixEnd_7436083 := by exact prefixLift 7436083
  have htrace : WordTrace (prefixWord ++ tailWord_7436083) baseStart_7436083 baseEnd_7436083 := by
    simpa [prefixWord, tailWord_7436083, baseEnd_7436083] using wordTrace_append hprefix tailTrace_7436083
  have hstable : (prefixWord ++ tailWord_7436083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436083).length < 2 ^ (prefixWord ++ tailWord_7436083).sum := by decide
  have hdescent : baseEnd_7436083 < baseStart_7436083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436099 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 3]
def baseStart_7436099 : Nat := 118140960795 + 7436099 * 2 ^ 59
def prefixEnd_7436099 : Nat := 4983230072969 + 3 ^ 40 * 7436099 * 2
def baseEnd_7436099 : Nat := 3818292981417806962164509

theorem tailTrace_7436099 : CollatzResearch.WordTrace tailWord_7436099 prefixEnd_7436099 3818292981417806962164509 := by
  unfold tailWord_7436099
  simp only [CollatzResearch.WordTrace]
  refine ⟨271216811887290782445671351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180811207924860521630447567 271216811887290782445671351)
  ·
    refine ⟨406825217830936173668507027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271216811887290782445671351 406825217830936173668507027)
    ·
      refine ⟨610237826746404260502760541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406825217830936173668507027 610237826746404260502760541)
      ·
        refine ⟨228839185029901597688535203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610237826746404260502760541 228839185029901597688535203)
        ·
          refine ⟨343258777544852396532802805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228839185029901597688535203 343258777544852396532802805)
          ·
            refine ⟨32180510394829912174950263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343258777544852396532802805 32180510394829912174950263)
            ·
              refine ⟨48270765592244868262425395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32180510394829912174950263 48270765592244868262425395)
              ·
                refine ⟨72406148388367302393638093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48270765592244868262425395 72406148388367302393638093)
                ·
                  refine ⟨27152305645637738397614285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72406148388367302393638093 27152305645637738397614285)
                  ·
                    refine ⟨10182114617114151899105357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27152305645637738397614285 10182114617114151899105357)
                    ·
                      refine ⟨3818292981417806962164509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10182114617114151899105357 3818292981417806962164509)
                      ·
                        rfl

theorem cell23_7436099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_7436099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436099 prefixEnd_7436099 := by exact prefixLift 7436099
  have htrace : WordTrace (prefixWord ++ tailWord_7436099) baseStart_7436099 baseEnd_7436099 := by
    simpa [prefixWord, tailWord_7436099, baseEnd_7436099] using wordTrace_append hprefix tailTrace_7436099
  have hstable : (prefixWord ++ tailWord_7436099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436099).length < 2 ^ (prefixWord ++ tailWord_7436099).sum := by decide
  have hdescent : baseEnd_7436099 < baseStart_7436099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436117 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 1, 2, 2]
def baseStart_7436117 : Nat := 118140960795 + 7436117 * 2 ^ 59
def prefixEnd_7436117 : Nat := 4983230072969 + 3 ^ 40 * 7436117 * 2
def baseEnd_7436117 : Nat := 3818302224069587891739427

theorem tailTrace_7436117 : CollatzResearch.WordTrace tailWord_7436117 prefixEnd_7436117 3818302224069587891739427 := by
  unfold tailWord_7436117
  simp only [CollatzResearch.WordTrace]
  refine ⟨271217468401225571519826605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180811645600817047679884403 271217468401225571519826605)
  ·
    refine ⟨101706550650459589319934977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271217468401225571519826605 101706550650459589319934977)
    ·
      refine ⟨76279912987844691989951233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101706550650459589319934977 76279912987844691989951233)
      ·
        refine ⟨57209934740883518992463425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76279912987844691989951233 57209934740883518992463425)
        ·
          refine ⟨42907451055662639244347569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57209934740883518992463425 42907451055662639244347569)
          ·
            refine ⟨32180588291746979433260677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42907451055662639244347569 32180588291746979433260677)
            ·
              refine ⟨6033860304702558643736377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32180588291746979433260677 6033860304702558643736377)
              ·
                refine ⟨4525395228526918982802283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033860304702558643736377 4525395228526918982802283)
                ·
                  refine ⟨6788092842790378474203425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525395228526918982802283 6788092842790378474203425)
                  ·
                    refine ⟨5091069632092783855652569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788092842790378474203425 5091069632092783855652569)
                    ·
                      refine ⟨3818302224069587891739427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091069632092783855652569 3818302224069587891739427)
                      ·
                        rfl

theorem cell23_7436117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_7436117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436117 prefixEnd_7436117 := by exact prefixLift 7436117
  have htrace : WordTrace (prefixWord ++ tailWord_7436117) baseStart_7436117 baseEnd_7436117 := by
    simpa [prefixWord, tailWord_7436117, baseEnd_7436117] using wordTrace_append hprefix tailTrace_7436117
  have hstable : (prefixWord ++ tailWord_7436117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436117).length < 2 ^ (prefixWord ++ tailWord_7436117).sum := by decide
  have hdescent : baseEnd_7436117 < baseStart_7436117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436149 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7436149 : Nat := 118140960795 + 7436149 * 2 ^ 59
def prefixEnd_7436149 : Nat := 4983230072969 + 3 ^ 40 * 7436149 * 2
def baseEnd_7436149 : Nat := 1272772885150177255513093

theorem tailTrace_7436149 : CollatzResearch.WordTrace tailWord_7436149 prefixEnd_7436149 1272772885150177255513093 := by
  unfold tailWord_7436149
  simp only [CollatzResearch.WordTrace]
  refine ⟨271218635537109640984991501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180812423691406427323327667 271218635537109640984991501)
  ·
    refine ⟨101706988326416115369371813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271218635537109640984991501 101706988326416115369371813)
    ·
      refine ⟨19070060311203021631757215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101706988326416115369371813 19070060311203021631757215)
      ·
        refine ⟨28605090466804532447635823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19070060311203021631757215 28605090466804532447635823)
        ·
          refine ⟨42907635700206798671453735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28605090466804532447635823 42907635700206798671453735)
          ·
            refine ⟨64361453550310198007180603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42907635700206798671453735 64361453550310198007180603)
            ·
              refine ⟨96542180325465297010770905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64361453550310198007180603 96542180325465297010770905)
              ·
                refine ⟨72406635244098972758078179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96542180325465297010770905 72406635244098972758078179)
                ·
                  refine ⟨108609952866148459137117269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72406635244098972758078179 108609952866148459137117269)
                  ·
                    refine ⟨1272772885150177255513093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108609952866148459137117269 1272772885150177255513093)
                    ·
                      rfl

theorem cell23_7436149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7436149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436149 prefixEnd_7436149 := by exact prefixLift 7436149
  have htrace : WordTrace (prefixWord ++ tailWord_7436149) baseStart_7436149 baseEnd_7436149 := by
    simpa [prefixWord, tailWord_7436149, baseEnd_7436149] using wordTrace_append hprefix tailTrace_7436149
  have hstable : (prefixWord ++ tailWord_7436149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436149).length < 2 ^ (prefixWord ++ tailWord_7436149).sum := by decide
  have hdescent : baseEnd_7436149 < baseStart_7436149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436167 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_7436167 : Nat := 118140960795 + 7436167 * 2 ^ 59
def prefixEnd_7436167 : Nat := 4983230072969 + 3 ^ 40 * 7436167 * 2
def baseEnd_7436167 : Nat := 3818327898102312696114197

theorem tailTrace_7436167 : CollatzResearch.WordTrace tailWord_7436167 prefixEnd_7436167 3818327898102312696114197 := by
  unfold tailWord_7436167
  simp only [CollatzResearch.WordTrace]
  refine ⟨271219292051044430059146755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180812861367362953372764503 271219292051044430059146755)
  ·
    refine ⟨406828938076566645088720133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271219292051044430059146755 406828938076566645088720133)
    ·
      refine ⟨76280425889356245954135025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406828938076566645088720133 76280425889356245954135025)
      ·
        refine ⟨57210319417017184465601269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76280425889356245954135025 57210319417017184465601269)
        ·
          refine ⟨5363467445345361043650119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57210319417017184465601269 5363467445345361043650119)
          ·
            refine ⟨8045201168018041565475179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363467445345361043650119 8045201168018041565475179)
            ·
              refine ⟨12067801752027062348212769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045201168018041565475179 12067801752027062348212769)
              ·
                refine ⟨9050851314020296761159577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12067801752027062348212769 9050851314020296761159577)
                ·
                  refine ⟨6788138485515222570869683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9050851314020296761159577 6788138485515222570869683)
                  ·
                    refine ⟨10182207728272833856304525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788138485515222570869683 10182207728272833856304525)
                    ·
                      refine ⟨3818327898102312696114197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10182207728272833856304525 3818327898102312696114197)
                      ·
                        rfl

theorem cell23_7436167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_7436167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436167 prefixEnd_7436167 := by exact prefixLift 7436167
  have htrace : WordTrace (prefixWord ++ tailWord_7436167) baseStart_7436167 baseEnd_7436167 := by
    simpa [prefixWord, tailWord_7436167, baseEnd_7436167] using wordTrace_append hprefix tailTrace_7436167
  have hstable : (prefixWord ++ tailWord_7436167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436167).length < 2 ^ (prefixWord ++ tailWord_7436167).sum := by decide
  have hdescent : baseEnd_7436167 < baseStart_7436167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436169 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_7436169 : Nat := 118140960795 + 7436169 * 2 ^ 59
def prefixEnd_7436169 : Nat := 4983230072969 + 3 ^ 40 * 7436169 * 2
def baseEnd_7436169 : Nat := 3818328925063621688289187

theorem tailTrace_7436169 : CollatzResearch.WordTrace tailWord_7436169 prefixEnd_7436169 3818328925063621688289187 := by
  unfold tailWord_7436169
  simp only [CollatzResearch.WordTrace]
  refine ⟨271219364997037184400719561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180812909998024789600479707 271219364997037184400719561)
  ·
    refine ⟨203414523747777888300539671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271219364997037184400719561 203414523747777888300539671)
    ·
      refine ⟨305121785621666832450809507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203414523747777888300539671 305121785621666832450809507)
      ·
        refine ⟨457682678432500248676214261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305121785621666832450809507 457682678432500248676214261)
        ·
          refine ⟨42907751103046898313395087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457682678432500248676214261 42907751103046898313395087)
          ·
            refine ⟨64361626654570347470092631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42907751103046898313395087 64361626654570347470092631)
            ·
              refine ⟨96542439981855521205138947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64361626654570347470092631 96542439981855521205138947)
              ·
                refine ⟨144813659972783281807708421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96542439981855521205138947 144813659972783281807708421)
                ·
                  refine ⟨27152561244896865338945329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144813659972783281807708421 27152561244896865338945329)
                  ·
                    refine ⟨20364420933672649004208997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27152561244896865338945329 20364420933672649004208997)
                    ·
                      refine ⟨3818328925063621688289187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20364420933672649004208997 3818328925063621688289187)
                      ·
                        rfl

theorem cell23_7436169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_7436169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436169 prefixEnd_7436169 := by exact prefixLift 7436169
  have htrace : WordTrace (prefixWord ++ tailWord_7436169) baseStart_7436169 baseEnd_7436169 := by
    simpa [prefixWord, tailWord_7436169, baseEnd_7436169] using wordTrace_append hprefix tailTrace_7436169
  have hstable : (prefixWord ++ tailWord_7436169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436169).length < 2 ^ (prefixWord ++ tailWord_7436169).sum := by decide
  have hdescent : baseEnd_7436169 < baseStart_7436169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436186 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7436186 : Nat := 118140960795 + 7436186 * 2 ^ 59
def prefixEnd_7436186 : Nat := 4983230072969 + 3 ^ 40 * 7436186 * 2
def baseEnd_7436186 : Nat := 3818337654234748121776609

theorem tailTrace_7436186 : CollatzResearch.WordTrace tailWord_7436186 prefixEnd_7436186 3818337654234748121776609 := by
  unfold tailWord_7436186
  simp only [CollatzResearch.WordTrace]
  refine ⟨67804996259493899076022103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180813323358650397536058941 67804996259493899076022103)
  ·
    refine ⟨101707494389240848614033155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67804996259493899076022103 101707494389240848614033155)
    ·
      refine ⟨152561241583861272921049733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101707494389240848614033155 152561241583861272921049733)
      ·
        refine ⟨28605232796973988672696825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152561241583861272921049733 28605232796973988672696825)
        ·
          refine ⟨21453924597730491504522619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28605232796973988672696825 21453924597730491504522619)
          ·
            refine ⟨32180886896595737256783929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453924597730491504522619 32180886896595737256783929)
            ·
              refine ⟨24135665172446802942587947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32180886896595737256783929 24135665172446802942587947)
              ·
                refine ⟨36203497758670204413881921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24135665172446802942587947 36203497758670204413881921)
                ·
                  refine ⟨27152623319002653310411441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36203497758670204413881921 27152623319002653310411441)
                  ·
                    refine ⟨20364467489251989982808581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27152623319002653310411441 20364467489251989982808581)
                    ·
                      refine ⟨3818337654234748121776609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20364467489251989982808581 3818337654234748121776609)
                      ·
                        rfl

theorem cell23_7436186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7436186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436186 prefixEnd_7436186 := by exact prefixLift 7436186
  have htrace : WordTrace (prefixWord ++ tailWord_7436186) baseStart_7436186 baseEnd_7436186 := by
    simpa [prefixWord, tailWord_7436186, baseEnd_7436186] using wordTrace_append hprefix tailTrace_7436186
  have hstable : (prefixWord ++ tailWord_7436186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436186).length < 2 ^ (prefixWord ++ tailWord_7436186).sum := by decide
  have hdescent : baseEnd_7436186 < baseStart_7436186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436213 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 5]
def baseStart_7436213 : Nat := 118140960795 + 7436213 * 2 ^ 59
def prefixEnd_7436213 : Nat := 4983230072969 + 3 ^ 40 * 7436213 * 2
def baseEnd_7436213 : Nat := 424261279801379946237665

theorem tailTrace_7436213 : CollatzResearch.WordTrace tailWord_7436213 prefixEnd_7436213 424261279801379946237665 := by
  unfold tailWord_7436213
  simp only [CollatzResearch.WordTrace]
  refine ⟨271220969808877779915321293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180813979872585186610214195 271220969808877779915321293)
  ·
    refine ⟨101707863678329167468245485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271220969808877779915321293 101707863678329167468245485)
    ·
      refine ⟨38140448879373437800592057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101707863678329167468245485 38140448879373437800592057)
      ·
        refine ⟨28605336659530078350444043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38140448879373437800592057 28605336659530078350444043)
        ·
          refine ⟨42908004989295117525666065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28605336659530078350444043 42908004989295117525666065)
          ·
            refine ⟨32181003741971338144249549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42908004989295117525666065 32181003741971338144249549)
            ·
              refine ⟨12067876403239251804093581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32181003741971338144249549 12067876403239251804093581)
              ·
                refine ⟨4525453651214719426535093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12067876403239251804093581 4525453651214719426535093)
                ·
                  refine ⟨424261279801379946237665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4525453651214719426535093 424261279801379946237665)
                  ·
                    rfl

theorem cell23_7436213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_7436213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436213 prefixEnd_7436213 := by exact prefixLift 7436213
  have htrace : WordTrace (prefixWord ++ tailWord_7436213) baseStart_7436213 baseEnd_7436213 := by
    simpa [prefixWord, tailWord_7436213, baseEnd_7436213] using wordTrace_append hprefix tailTrace_7436213
  have hstable : (prefixWord ++ tailWord_7436213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436213).length < 2 ^ (prefixWord ++ tailWord_7436213).sum := by decide
  have hdescent : baseEnd_7436213 < baseStart_7436213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436229 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_7436229 : Nat := 118140960795 + 7436229 * 2 ^ 59
def prefixEnd_7436229 : Nat := 4983230072969 + 3 ^ 40 * 7436229 * 2
def baseEnd_7436229 : Nat := 3818359733902891453538911

theorem tailTrace_7436229 : CollatzResearch.WordTrace tailWord_7436229 prefixEnd_7436229 3818359733902891453538911 := by
  unfold tailWord_7436229
  simp only [CollatzResearch.WordTrace]
  refine ⟨271221553376819814647903741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180814368917879876431935827 271221553376819814647903741)
  ·
    refine ⟨101708082516307430492963903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271221553376819814647903741 101708082516307430492963903)
    ·
      refine ⟨152562123774461145739445855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101708082516307430492963903 152562123774461145739445855)
      ·
        refine ⟨228843185661691718609168783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152562123774461145739445855 228843185661691718609168783)
        ·
          refine ⟨343264778492537577913753175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228843185661691718609168783 343264778492537577913753175)
          ·
            refine ⟨514897167738806366870629763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343264778492537577913753175 514897167738806366870629763)
            ·
              refine ⟨772345751608209550305944645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514897167738806366870629763 772345751608209550305944645)
              ·
                refine ⟨144814828426539290682364621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772345751608209550305944645 144814828426539290682364621)
                ·
                  refine ⟨54305560659952234005886733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144814828426539290682364621 54305560659952234005886733)
                  ·
                    refine ⟨20364585247482087752207525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54305560659952234005886733 20364585247482087752207525)
                    ·
                      refine ⟨3818359733902891453538911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20364585247482087752207525 3818359733902891453538911)
                      ·
                        rfl

theorem cell23_7436229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_7436229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436229 prefixEnd_7436229 := by exact prefixLift 7436229
  have htrace : WordTrace (prefixWord ++ tailWord_7436229) baseStart_7436229 baseEnd_7436229 := by
    simpa [prefixWord, tailWord_7436229, baseEnd_7436229] using wordTrace_append hprefix tailTrace_7436229
  have hstable : (prefixWord ++ tailWord_7436229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436229).length < 2 ^ (prefixWord ++ tailWord_7436229).sum := by decide
  have hdescent : baseEnd_7436229 < baseStart_7436229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436236 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7436236 : Nat := 118140960795 + 7436236 * 2 ^ 59
def prefixEnd_7436236 : Nat := 4983230072969 + 3 ^ 40 * 7436236 * 2
def baseEnd_7436236 : Nat := 3818363328267472926151379

theorem tailTrace_7436236 : CollatzResearch.WordTrace tailWord_7436236 prefixEnd_7436236 3818363328267472926151379 := by
  unfold tailWord_7436236
  simp only [CollatzResearch.WordTrace]
  refine ⟨135610904343897227421704281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180814539125196303228939041 135610904343897227421704281)
  ·
    refine ⟨101708178257922920566278211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135610904343897227421704281 101708178257922920566278211)
    ·
      refine ⟨152562267386884380849417317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101708178257922920566278211 152562267386884380849417317)
      ·
        refine ⟨28605425135040821409265747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152562267386884380849417317 28605425135040821409265747)
        ·
          refine ⟨42908137702561232113898621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28605425135040821409265747 42908137702561232113898621)
          ·
            refine ⟨16090551638460462042711983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42908137702561232113898621 16090551638460462042711983)
            ·
              refine ⟨24135827457690693064067975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16090551638460462042711983 24135827457690693064067975)
              ·
                refine ⟨36203741186536039596101963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24135827457690693064067975 36203741186536039596101963)
                ·
                  refine ⟨54305611779804059394152945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36203741186536039596101963 54305611779804059394152945)
                  ·
                    refine ⟨40729208834853044545614709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54305611779804059394152945 40729208834853044545614709)
                    ·
                      refine ⟨3818363328267472926151379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40729208834853044545614709 3818363328267472926151379)
                      ·
                        rfl

theorem cell23_7436236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7436236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436236 prefixEnd_7436236 := by exact prefixLift 7436236
  have htrace : WordTrace (prefixWord ++ tailWord_7436236) baseStart_7436236 baseEnd_7436236 := by
    simpa [prefixWord, tailWord_7436236, baseEnd_7436236] using wordTrace_append hprefix tailTrace_7436236
  have hstable : (prefixWord ++ tailWord_7436236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436236).length < 2 ^ (prefixWord ++ tailWord_7436236).sum := by decide
  have hdescent : baseEnd_7436236 < baseStart_7436236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436256 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 3, 4]
def baseStart_7436256 : Nat := 118140960795 + 7436256 * 2 ^ 59
def prefixEnd_7436256 : Nat := 4983230072969 + 3 ^ 40 * 7436256 * 2
def baseEnd_7436256 : Nat := 1272791199293520949300429

theorem tailTrace_7436256 : CollatzResearch.WordTrace tailWord_7436256 prefixEnd_7436256 1272791199293520949300429 := by
  unfold tailWord_7436256
  simp only [CollatzResearch.WordTrace]
  refine ⟨135611269073860999129568311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180815025431814665506091081 135611269073860999129568311)
  ·
    refine ⟨203416903610791498694352467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135611269073860999129568311 203416903610791498694352467)
    ·
      refine ⟨305125355416187248041528701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203416903610791498694352467 305125355416187248041528701)
      ·
        refine ⟨114422008281070218015573263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305125355416187248041528701 114422008281070218015573263)
        ·
          refine ⟨171633012421605327023359895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114422008281070218015573263 171633012421605327023359895)
          ·
            refine ⟨257449518632407990535039843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171633012421605327023359895 257449518632407990535039843)
            ·
              refine ⟨386174277948611985802559765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257449518632407990535039843 386174277948611985802559765)
              ·
                refine ⟨18101919278841186834494989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 386174277948611985802559765 18101919278841186834494989)
                ·
                  refine ⟨6788219729565445062935621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18101919278841186834494989 6788219729565445062935621)
                  ·
                    refine ⟨1272791199293520949300429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788219729565445062935621 1272791199293520949300429)
                    ·
                      rfl

theorem cell23_7436256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_7436256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436256 prefixEnd_7436256 := by exact prefixLift 7436256
  have htrace : WordTrace (prefixWord ++ tailWord_7436256) baseStart_7436256 baseEnd_7436256 := by
    simpa [prefixWord, tailWord_7436256, baseEnd_7436256] using wordTrace_append hprefix tailTrace_7436256
  have hstable : (prefixWord ++ tailWord_7436256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436256).length < 2 ^ (prefixWord ++ tailWord_7436256).sum := by decide
  have hdescent : baseEnd_7436256 < baseStart_7436256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436323 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 1, 5, 2]
def baseStart_7436323 : Nat := 118140960795 + 7436323 * 2 ^ 59
def prefixEnd_7436323 : Nat := 4983230072969 + 3 ^ 40 * 7436323 * 2
def baseEnd_7436323 : Nat := 3818408001084414085763479

theorem tailTrace_7436323 : CollatzResearch.WordTrace tailWord_7436323 prefixEnd_7436323 3818408001084414085763479 := by
  unfold tailWord_7436323
  simp only [CollatzResearch.WordTrace]
  refine ⟨271224981838479268701825623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180816654558986179134550415 271224981838479268701825623)
  ·
    refine ⟨406837472757718903052738435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271224981838479268701825623 406837472757718903052738435)
    ·
      refine ⟨610256209136578354579107653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406837472757718903052738435 610256209136578354579107653)
      ·
        refine ⟨114423039213108441483582685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610256209136578354579107653 114423039213108441483582685)
        ·
          refine ⟨42908639704915665556343507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114423039213108441483582685 42908639704915665556343507)
          ·
            refine ⟨64362959557373498334515261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42908639704915665556343507 64362959557373498334515261)
            ·
              refine ⟨24136109834015061875443223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64362959557373498334515261 24136109834015061875443223)
              ·
                refine ⟨36204164751022592813164835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24136109834015061875443223 36204164751022592813164835)
                ·
                  refine ⟨54306247126533889219747253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36204164751022592813164835 54306247126533889219747253)
                  ·
                    refine ⟨5091210668112552114351305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54306247126533889219747253 5091210668112552114351305)
                    ·
                      refine ⟨3818408001084414085763479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091210668112552114351305 3818408001084414085763479)
                      ·
                        rfl

theorem cell23_7436323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_7436323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436323 prefixEnd_7436323 := by exact prefixLift 7436323
  have htrace : WordTrace (prefixWord ++ tailWord_7436323) baseStart_7436323 baseEnd_7436323 := by
    simpa [prefixWord, tailWord_7436323, baseEnd_7436323] using wordTrace_append hprefix tailTrace_7436323
  have hstable : (prefixWord ++ tailWord_7436323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436323).length < 2 ^ (prefixWord ++ tailWord_7436323).sum := by decide
  have hdescent : baseEnd_7436323 < baseStart_7436323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436329 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_7436329 : Nat := 118140960795 + 7436329 * 2 ^ 59
def prefixEnd_7436329 : Nat := 4983230072969 + 3 ^ 40 * 7436329 * 2
def baseEnd_7436329 : Nat := 1272803693989447020762817

theorem tailTrace_7436329 : CollatzResearch.WordTrace tailWord_7436329 prefixEnd_7436329 1272803693989447020762817 := by
  unfold tailWord_7436329
  simp only [CollatzResearch.WordTrace]
  refine ⟨271225200676457531726544041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180816800450971687817696027 271225200676457531726544041)
  ·
    refine ⟨203418900507343148794908031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271225200676457531726544041 203418900507343148794908031)
    ·
      refine ⟨305128350761014723192362047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203418900507343148794908031 305128350761014723192362047)
      ·
        refine ⟨457692526141522084788543071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305128350761014723192362047 457692526141522084788543071)
        ·
          refine ⟨686538789212283127182814607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457692526141522084788543071 686538789212283127182814607)
          ·
            refine ⟨1029808183818424690774221911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686538789212283127182814607 1029808183818424690774221911)
            ·
              refine ⟨1544712275727637036161332867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029808183818424690774221911 1544712275727637036161332867)
              ·
                refine ⟨2317068413591455554241999301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1544712275727637036161332867 2317068413591455554241999301)
                ·
                  refine ⟨434450327548397916420374869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317068413591455554241999301 434450327548397916420374869)
                  ·
                    refine ⟨1272803693989447020762817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 434450327548397916420374869 1272803693989447020762817)
                    ·
                      rfl

theorem cell23_7436329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_7436329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436329 prefixEnd_7436329 := by exact prefixLift 7436329
  have htrace : WordTrace (prefixWord ++ tailWord_7436329) baseStart_7436329 baseEnd_7436329 := by
    simpa [prefixWord, tailWord_7436329, baseEnd_7436329] using wordTrace_append hprefix tailTrace_7436329
  have hstable : (prefixWord ++ tailWord_7436329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436329).length < 2 ^ (prefixWord ++ tailWord_7436329).sum := by decide
  have hdescent : baseEnd_7436329 < baseStart_7436329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436376 : List Nat := [2, 1, 2, 2, 1, 5, 1, 9]
def baseStart_7436376 : Nat := 118140960795 + 7436376 * 2 ^ 59
def prefixEnd_7436376 : Nat := 4983230072969 + 3 ^ 40 * 7436376 * 2
def baseEnd_7436376 : Nat := 141423526502188976977805

theorem tailTrace_7436376 : CollatzResearch.WordTrace tailWord_7436376 prefixEnd_7436376 141423526502188976977805 := by
  unfold tailWord_7436376
  simp only [CollatzResearch.WordTrace]
  refine ⟨135613457453643629376752491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180817943271524839169003321 135613457453643629376752491)
  ·
    refine ⟨203420186180465444065128737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135613457453643629376752491 203420186180465444065128737)
    ·
      refine ⟨152565139635349083048846553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203420186180465444065128737 152565139635349083048846553)
      ·
        refine ⟨114423854726511812286634915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152565139635349083048846553 114423854726511812286634915)
        ·
          refine ⟨171635782089767718429952373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114423854726511812286634915 171635782089767718429952373)
          ·
            refine ⟨16090854570915723602808035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171635782089767718429952373 16090854570915723602808035)
            ·
              refine ⟨24136281856373585404212053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16090854570915723602808035 24136281856373585404212053)
              ·
                refine ⟨141423526502188976977805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24136281856373585404212053 141423526502188976977805)
                ·
                  rfl

theorem cell23_7436376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 9].length) (baseStart_7436376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436376 prefixEnd_7436376 := by exact prefixLift 7436376
  have htrace : WordTrace (prefixWord ++ tailWord_7436376) baseStart_7436376 baseEnd_7436376 := by
    simpa [prefixWord, tailWord_7436376, baseEnd_7436376] using wordTrace_append hprefix tailTrace_7436376
  have hstable : (prefixWord ++ tailWord_7436376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436376).length < 2 ^ (prefixWord ++ tailWord_7436376).sum := by decide
  have hdescent : baseEnd_7436376 < baseStart_7436376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436381 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7436381 : Nat := 118140960795 + 7436381 * 2 ^ 59
def prefixEnd_7436381 : Nat := 4983230072969 + 3 ^ 40 * 7436381 * 2
def baseEnd_7436381 : Nat := 3818437782962374858838213

theorem tailTrace_7436381 : CollatzResearch.WordTrace tailWord_7436381 prefixEnd_7436381 3818437782962374858838213 := by
  unfold tailWord_7436381
  simp only [CollatzResearch.WordTrace]
  refine ⟨271227097272269144607436997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180818064848179429738291331 271227097272269144607436997)
  ·
    refine ⟨50855080738550464613894437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271227097272269144607436997 50855080738550464613894437)
    ·
      refine ⟨9535327638478212115105207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50855080738550464613894437 9535327638478212115105207)
      ·
        refine ⟨14302991457717318172657811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535327638478212115105207 14302991457717318172657811)
        ·
          refine ⟨21454487186575977258986717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14302991457717318172657811 21454487186575977258986717)
          ·
            refine ⟨8045432694965991472120019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21454487186575977258986717 8045432694965991472120019)
            ·
              refine ⟨12068149042448987208180029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045432694965991472120019 12068149042448987208180029)
              ·
                refine ⟨4525555890918370203067511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12068149042448987208180029 4525555890918370203067511)
                ·
                  refine ⟨6788333836377555304601267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525555890918370203067511 6788333836377555304601267)
                  ·
                    refine ⟨10182500754566332956901901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788333836377555304601267 10182500754566332956901901)
                    ·
                      refine ⟨3818437782962374858838213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10182500754566332956901901 3818437782962374858838213)
                      ·
                        rfl

theorem cell23_7436381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7436381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436381 prefixEnd_7436381 := by exact prefixLift 7436381
  have htrace : WordTrace (prefixWord ++ tailWord_7436381) baseStart_7436381 baseEnd_7436381 := by
    simpa [prefixWord, tailWord_7436381, baseEnd_7436381] using wordTrace_append hprefix tailTrace_7436381
  have hstable : (prefixWord ++ tailWord_7436381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436381).length < 2 ^ (prefixWord ++ tailWord_7436381).sum := by decide
  have hdescent : baseEnd_7436381 < baseStart_7436381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436455 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_7436455 : Nat := 118140960795 + 7436455 * 2 ^ 59
def prefixEnd_7436455 : Nat := 4983230072969 + 3 ^ 40 * 7436455 * 2
def baseEnd_7436455 : Nat := 3818475780530807569312873

theorem tailTrace_7436455 : CollatzResearch.WordTrace tailWord_7436455 prefixEnd_7436455 3818475780530807569312873 := by
  unfold tailWord_7436455
  simp only [CollatzResearch.WordTrace]
  refine ⟨271229796274001055245630819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180819864182667370163753879 271229796274001055245630819)
  ·
    refine ⟨406844694411001582868446229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271229796274001055245630819 406844694411001582868446229)
    ·
      refine ⟨19070845050515699196958417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 406844694411001582868446229 19070845050515699196958417)
      ·
        refine ⟨14303133787886774397718813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19070845050515699196958417 14303133787886774397718813)
        ·
          refine ⟨5363675170457540399144555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14303133787886774397718813 5363675170457540399144555)
          ·
            refine ⟨8045512755686310598716833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363675170457540399144555 8045512755686310598716833)
            ·
              refine ⟨6034134566764732949037625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8045512755686310598716833 6034134566764732949037625)
              ·
                refine ⟨4525600925073549711778219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6034134566764732949037625 4525600925073549711778219)
                ·
                  refine ⟨6788401387610324567667329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525600925073549711778219 6788401387610324567667329)
                  ·
                    refine ⟨5091301040707743425750497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788401387610324567667329 5091301040707743425750497)
                    ·
                      refine ⟨3818475780530807569312873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091301040707743425750497 3818475780530807569312873)
                      ·
                        rfl

theorem cell23_7436455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_7436455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436455 prefixEnd_7436455 := by exact prefixLift 7436455
  have htrace : WordTrace (prefixWord ++ tailWord_7436455) baseStart_7436455 baseEnd_7436455 := by
    simpa [prefixWord, tailWord_7436455, baseEnd_7436455] using wordTrace_append hprefix tailTrace_7436455
  have hstable : (prefixWord ++ tailWord_7436455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436455).length < 2 ^ (prefixWord ++ tailWord_7436455).sum := by decide
  have hdescent : baseEnd_7436455 < baseStart_7436455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436460 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 8, 2, 2]
def baseStart_7436460 : Nat := 118140960795 + 7436460 * 2 ^ 59
def prefixEnd_7436460 : Nat := 4983230072969 + 3 ^ 40 * 7436460 * 2
def baseEnd_7436460 : Nat := 3818478347934080049750349

theorem tailTrace_7436460 : CollatzResearch.WordTrace tailWord_7436460 prefixEnd_7436460 3818478347934080049750349 := by
  unfold tailWord_7436460
  simp only [CollatzResearch.WordTrace]
  refine ⟨135614989319491470549781417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180819985759321960733041889 135614989319491470549781417)
  ·
    refine ⟨101711241989618602912336063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135614989319491470549781417 101711241989618602912336063)
    ·
      refine ⟨152566862984427904368504095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101711241989618602912336063 152566862984427904368504095)
      ·
        refine ⟨228850294476641856552756143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152566862984427904368504095 228850294476641856552756143)
        ·
          refine ⟨343275441714962784829134215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228850294476641856552756143 343275441714962784829134215)
          ·
            refine ⟨514913162572444177243701323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343275441714962784829134215 514913162572444177243701323)
            ·
              refine ⟨772369743858666265865551985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514913162572444177243701323 772369743858666265865551985)
              ·
                refine ⟨579277307893999699399163989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772369743858666265865551985 579277307893999699399163989)
                ·
                  refine ⟨6788405951882808977333953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 579277307893999699399163989 6788405951882808977333953)
                  ·
                    refine ⟨5091304463912106733000465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788405951882808977333953 5091304463912106733000465)
                    ·
                      refine ⟨3818478347934080049750349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091304463912106733000465 3818478347934080049750349)
                      ·
                        rfl

theorem cell23_7436460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_7436460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436460 prefixEnd_7436460 := by exact prefixLift 7436460
  have htrace : WordTrace (prefixWord ++ tailWord_7436460) baseStart_7436460 baseEnd_7436460 := by
    simpa [prefixWord, tailWord_7436460, baseEnd_7436460] using wordTrace_append hprefix tailTrace_7436460
  have hstable : (prefixWord ++ tailWord_7436460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436460).length < 2 ^ (prefixWord ++ tailWord_7436460).sum := by decide
  have hdescent : baseEnd_7436460 < baseStart_7436460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436473 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7436473 : Nat := 118140960795 + 7436473 * 2 ^ 59
def prefixEnd_7436473 : Nat := 4983230072969 + 3 ^ 40 * 7436473 * 2
def baseEnd_7436473 : Nat := 3818485023182588498887789

theorem tailTrace_7436473 : CollatzResearch.WordTrace tailWord_7436473 prefixEnd_7436473 3818485023182588498887789 := by
  unfold tailWord_7436473
  simp only [CollatzResearch.WordTrace]
  refine ⟨271230452787935844319786073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180820301858623896213190715 271230452787935844319786073)
  ·
    refine ⟨203422839590951883239839555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271230452787935844319786073 203422839590951883239839555)
    ·
      refine ⟨305134259386427824859759333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203422839590951883239839555 305134259386427824859759333)
      ·
        refine ⟨57212673634955217161204875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305134259386427824859759333 57212673634955217161204875)
        ·
          refine ⟨85819010452432825741807313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57212673634955217161204875 85819010452432825741807313)
          ·
            refine ⟨64364257839324619306355485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85819010452432825741807313 64364257839324619306355485)
            ·
              refine ⟨24136596689746732239883307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64364257839324619306355485 24136596689746732239883307)
              ·
                refine ⟨36204895034620098359824961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24136596689746732239883307 36204895034620098359824961)
                ·
                  refine ⟨27153671275965073769868721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36204895034620098359824961 27153671275965073769868721)
                  ·
                    refine ⟨20365253456973805327401541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27153671275965073769868721 20365253456973805327401541)
                    ·
                      refine ⟨3818485023182588498887789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20365253456973805327401541 3818485023182588498887789)
                      ·
                        rfl

theorem cell23_7436473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7436473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436473 prefixEnd_7436473 := by exact prefixLift 7436473
  have htrace : WordTrace (prefixWord ++ tailWord_7436473) baseStart_7436473 baseEnd_7436473 := by
    simpa [prefixWord, tailWord_7436473, baseEnd_7436473] using wordTrace_append hprefix tailTrace_7436473
  have hstable : (prefixWord ++ tailWord_7436473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436473).length < 2 ^ (prefixWord ++ tailWord_7436473).sum := by decide
  have hdescent : baseEnd_7436473 < baseStart_7436473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436513 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_7436513 : Nat := 118140960795 + 7436513 * 2 ^ 59
def prefixEnd_7436513 : Nat := 4983230072969 + 3 ^ 40 * 7436513 * 2
def baseEnd_7436513 : Nat := 1272835187469589447462535

theorem tailTrace_7436513 : CollatzResearch.WordTrace tailWord_7436513 prefixEnd_7436513 1272835187469589447462535 := by
  unfold tailWord_7436513
  simp only [CollatzResearch.WordTrace]
  refine ⟨271231911707790931151242193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180821274471860620767494795 271231911707790931151242193)
  ·
    refine ⟨203423933780843198363431645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271231911707790931151242193 203423933780843198363431645)
    ·
      refine ⟨76283975167816199386286867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203423933780843198363431645 76283975167816199386286867)
      ·
        refine ⟨114425962751724299079430301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76283975167816199386286867 114425962751724299079430301)
        ·
          refine ⟨42909736031896612154786363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114425962751724299079430301 42909736031896612154786363)
          ·
            refine ⟨64364604047844918232179545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42909736031896612154786363 64364604047844918232179545)
            ·
              refine ⟨48273453035883688674134659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64364604047844918232179545 48273453035883688674134659)
              ·
                refine ⟨72410179553825533011201989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48273453035883688674134659 72410179553825533011201989)
                ·
                  refine ⟨13576908666342287439600373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72410179553825533011201989 13576908666342287439600373)
                  ·
                    refine ⟨1272835187469589447462535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13576908666342287439600373 1272835187469589447462535)
                    ·
                      rfl

theorem cell23_7436513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_7436513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436513 prefixEnd_7436513 := by exact prefixLift 7436513
  have htrace : WordTrace (prefixWord ++ tailWord_7436513) baseStart_7436513 baseEnd_7436513 := by
    simpa [prefixWord, tailWord_7436513, baseEnd_7436513] using wordTrace_append hprefix tailTrace_7436513
  have hstable : (prefixWord ++ tailWord_7436513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436513).length < 2 ^ (prefixWord ++ tailWord_7436513).sum := by decide
  have hdescent : baseEnd_7436513 < baseStart_7436513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436551 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 5]
def baseStart_7436551 : Nat := 118140960795 + 7436551 * 2 ^ 59
def prefixEnd_7436551 : Nat := 4983230072969 + 3 ^ 40 * 7436551 * 2
def baseEnd_7436551 : Nat := 424280563852626577079159

theorem tailTrace_7436551 : CollatzResearch.WordTrace tailWord_7436551 prefixEnd_7436551 424280563852626577079159 := by
  unfold tailWord_7436551
  simp only [CollatzResearch.WordTrace]
  refine ⟨271233297681653263641125507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180822198454435509094083671 271233297681653263641125507)
  ·
    refine ⟨406849946522479895461688261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271233297681653263641125507 406849946522479895461688261)
    ·
      refine ⟨76284364972964980399066549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406849946522479895461688261 76284364972964980399066549)
      ·
        refine ⟨7151659216215466912412489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76284364972964980399066549 7151659216215466912412489)
        ·
          refine ⟨5363744412161600184309367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7151659216215466912412489 5363744412161600184309367)
          ·
            refine ⟨8045616618242400276464051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363744412161600184309367 8045616618242400276464051)
            ·
              refine ⟨12068424927363600414696077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045616618242400276464051 12068424927363600414696077)
              ·
                refine ⟨4525659347761350155511029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12068424927363600414696077 4525659347761350155511029)
                ·
                  refine ⟨424280563852626577079159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4525659347761350155511029 424280563852626577079159)
                  ·
                    rfl

theorem cell23_7436551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 5].length) (baseStart_7436551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436551 prefixEnd_7436551 := by exact prefixLift 7436551
  have htrace : WordTrace (prefixWord ++ tailWord_7436551) baseStart_7436551 baseEnd_7436551 := by
    simpa [prefixWord, tailWord_7436551, baseEnd_7436551] using wordTrace_append hprefix tailTrace_7436551
  have hstable : (prefixWord ++ tailWord_7436551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436551).length < 2 ^ (prefixWord ++ tailWord_7436551).sum := by decide
  have hdescent : baseEnd_7436551 < baseStart_7436551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436577 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 1, 4]
def baseStart_7436577 : Nat := 118140960795 + 7436577 * 2 ^ 59
def prefixEnd_7436577 : Nat := 4983230072969 + 3 ^ 40 * 7436577 * 2
def baseEnd_7436577 : Nat := 1272846141723552030662437

theorem tailTrace_7436577 : CollatzResearch.WordTrace tailWord_7436577 prefixEnd_7436577 1272846141723552030662437 := by
  unfold tailWord_7436577
  simp only [CollatzResearch.WordTrace]
  refine ⟨271234245979559070081571985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180822830653039380054381323 271234245979559070081571985)
  ·
    refine ⟨203425684484669302561178989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271234245979559070081571985 203425684484669302561178989)
    ·
      refine ⟨76284631681750988460442121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203425684484669302561178989 76284631681750988460442121)
      ·
        refine ⟨57213473761313241345331591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76284631681750988460442121 57213473761313241345331591)
        ·
          refine ⟨85820210641969862017997387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57213473761313241345331591 85820210641969862017997387)
          ·
            refine ⟨128730315962954793026996081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85820210641969862017997387 128730315962954793026996081)
            ·
              refine ⟨96547736972216094770247061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128730315962954793026996081 96547736972216094770247061)
              ·
                refine ⟨4525675170572629442355331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96547736972216094770247061 4525675170572629442355331)
                ·
                  refine ⟨6788512755858944163532997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525675170572629442355331 6788512755858944163532997)
                  ·
                    refine ⟨1272846141723552030662437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788512755858944163532997 1272846141723552030662437)
                    ·
                      rfl

theorem cell23_7436577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_7436577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436577 prefixEnd_7436577 := by exact prefixLift 7436577
  have htrace : WordTrace (prefixWord ++ tailWord_7436577) baseStart_7436577 baseEnd_7436577 := by
    simpa [prefixWord, tailWord_7436577, baseEnd_7436577] using wordTrace_append hprefix tailTrace_7436577
  have hstable : (prefixWord ++ tailWord_7436577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436577).length < 2 ^ (prefixWord ++ tailWord_7436577).sum := by decide
  have hdescent : baseEnd_7436577 < baseStart_7436577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436633 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_7436633 : Nat := 118140960795 + 7436633 * 2 ^ 59
def prefixEnd_7436633 : Nat := 4983230072969 + 3 ^ 40 * 7436633 * 2
def baseEnd_7436633 : Nat := 1272855726695769290962351

theorem tailTrace_7436633 : CollatzResearch.WordTrace tailWord_7436633 prefixEnd_7436633 1272855726695769290962351 := by
  unfold tailWord_7436633
  simp only [CollatzResearch.WordTrace]
  refine ⟨271236288467356191645610553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180824192311570794430407035 271236288467356191645610553)
  ·
    refine ⟨203427216350517143734207915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271236288467356191645610553 203427216350517143734207915)
    ·
      refine ⟨305140824525775715601311873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203427216350517143734207915 305140824525775715601311873)
      ·
        refine ⟨228855618394331786700983905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305140824525775715601311873 228855618394331786700983905)
        ·
          refine ⟨171641713795748840025737929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228855618394331786700983905 171641713795748840025737929)
          ·
            refine ⟨128731285346811630019303447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171641713795748840025737929 128731285346811630019303447)
            ·
              refine ⟨193096928020217445028955171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128731285346811630019303447 193096928020217445028955171)
              ·
                refine ⟨289645392030326167543432757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193096928020217445028955171 289645392030326167543432757)
                ·
                  refine ⟨27154255502843078207196821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289645392030326167543432757 27154255502843078207196821)
                  ·
                    refine ⟨1272855726695769290962351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27154255502843078207196821 1272855726695769290962351)
                    ·
                      rfl

theorem cell23_7436633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_7436633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436633 prefixEnd_7436633 := by exact prefixLift 7436633
  have htrace : WordTrace (prefixWord ++ tailWord_7436633) baseStart_7436633 baseEnd_7436633 := by
    simpa [prefixWord, tailWord_7436633, baseEnd_7436633] using wordTrace_append hprefix tailTrace_7436633
  have hstable : (prefixWord ++ tailWord_7436633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436633).length < 2 ^ (prefixWord ++ tailWord_7436633).sum := by decide
  have hdescent : baseEnd_7436633 < baseStart_7436633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436661 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7436661 : Nat := 118140960795 + 7436661 * 2 ^ 59
def prefixEnd_7436661 : Nat := 4983230072969 + 3 ^ 40 * 7436661 * 2
def baseEnd_7436661 : Nat := 3818581557545633763336925

theorem tailTrace_7436661 : CollatzResearch.WordTrace tailWord_7436661 prefixEnd_7436661 3818581557545633763336925 := by
  unfold tailWord_7436661
  simp only [CollatzResearch.WordTrace]
  refine ⟨271237309711254752427629837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180824873140836501618419891 271237309711254752427629837)
  ·
    refine ⟨101713991141720532160361189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271237309711254752427629837 101713991141720532160361189)
    ·
      refine ⟨19071373339072599780067723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101713991141720532160361189 19071373339072599780067723)
      ·
        refine ⟨28607060008608899670101585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19071373339072599780067723 28607060008608899670101585)
        ·
          refine ⟨21455295006456674752576189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28607060008608899670101585 21455295006456674752576189)
          ·
            refine ⟨8045735627421253032216071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21455295006456674752576189 8045735627421253032216071)
            ·
              refine ⟨12068603441131879548324107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045735627421253032216071 12068603441131879548324107)
              ·
                refine ⟨18102905161697819322486161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12068603441131879548324107 18102905161697819322486161)
                ·
                  refine ⟨13577178871273364491864621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18102905161697819322486161 13577178871273364491864621)
                  ·
                    refine ⟨5091442076727511684449233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13577178871273364491864621 5091442076727511684449233)
                    ·
                      refine ⟨3818581557545633763336925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091442076727511684449233 3818581557545633763336925)
                      ·
                        rfl

theorem cell23_7436661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7436661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436661 prefixEnd_7436661 := by exact prefixLift 7436661
  have htrace : WordTrace (prefixWord ++ tailWord_7436661) baseStart_7436661 baseEnd_7436661 := by
    simpa [prefixWord, tailWord_7436661, baseEnd_7436661] using wordTrace_append hprefix tailTrace_7436661
  have hstable : (prefixWord ++ tailWord_7436661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436661).length < 2 ^ (prefixWord ++ tailWord_7436661).sum := by decide
  have hdescent : baseEnd_7436661 < baseStart_7436661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436684 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_7436684 : Nat := 118140960795 + 7436684 * 2 ^ 59
def prefixEnd_7436684 : Nat := 4983230072969 + 3 ^ 40 * 7436684 * 2
def baseEnd_7436684 : Nat := 1272864455866895724449773

theorem tailTrace_7436684 : CollatzResearch.WordTrace tailWord_7436684 prefixEnd_7436684 1272864455866895724449773 := by
  unfold tailWord_7436684
  simp only [CollatzResearch.WordTrace]
  refine ⟨135619074295085713677858553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180825432393447618237144737 135619074295085713677858553)
  ·
    refine ⟨101714305721314285258393915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135619074295085713677858553 101714305721314285258393915)
    ·
      refine ⟨152571458581971427887590873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101714305721314285258393915 152571458581971427887590873)
      ·
        refine ⟨114428593936478570915693155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152571458581971427887590873 114428593936478570915693155)
        ·
          refine ⟨171642890904717856373539733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114428593936478570915693155 171642890904717856373539733)
          ·
            refine ⟨8045760511158649517509675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171642890904717856373539733 8045760511158649517509675)
            ·
              refine ⟨12068640766737974276264513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045760511158649517509675 12068640766737974276264513)
              ·
                refine ⟨9051480575053480707198385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12068640766737974276264513 9051480575053480707198385)
                ·
                  refine ⟨6788610431290110530398789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051480575053480707198385 6788610431290110530398789)
                  ·
                    refine ⟨1272864455866895724449773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788610431290110530398789 1272864455866895724449773)
                    ·
                      rfl

theorem cell23_7436684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_7436684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436684 prefixEnd_7436684 := by exact prefixLift 7436684
  have htrace : WordTrace (prefixWord ++ tailWord_7436684) baseStart_7436684 baseEnd_7436684 := by
    simpa [prefixWord, tailWord_7436684, baseEnd_7436684] using wordTrace_append hprefix tailTrace_7436684
  have hstable : (prefixWord ++ tailWord_7436684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436684).length < 2 ^ (prefixWord ++ tailWord_7436684).sum := by decide
  have hdescent : baseEnd_7436684 < baseStart_7436684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436701 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_7436701 : Nat := 118140960795 + 7436701 * 2 ^ 59
def prefixEnd_7436701 : Nat := 4983230072969 + 3 ^ 40 * 7436701 * 2
def baseEnd_7436701 : Nat := 1272867365590604535612247

theorem tailTrace_7436701 : CollatzResearch.WordTrace tailWord_7436701 prefixEnd_7436701 1272867365590604535612247 := by
  unfold tailWord_7436701
  simp only [CollatzResearch.WordTrace]
  refine ⟨271238768631109839259085957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180825845754073226172723971 271238768631109839259085957)
  ·
    refine ⟨50857269118333094861078617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271238768631109839259085957 50857269118333094861078617)
    ·
      refine ⟨38142951838749821145808963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50857269118333094861078617 38142951838749821145808963)
      ·
        refine ⟨57214427758124731718713445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38142951838749821145808963 57214427758124731718713445)
        ·
          refine ⟨10727705204648387197258771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57214427758124731718713445 10727705204648387197258771)
          ·
            refine ⟨16091557806972580795888157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10727705204648387197258771 16091557806972580795888157)
            ·
              refine ⟨6034334177614717798458059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16091557806972580795888157 6034334177614717798458059)
              ·
                refine ⟨9051501266422076697687089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034334177614717798458059 9051501266422076697687089)
                ·
                  refine ⟨6788625949816557523265317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051501266422076697687089 6788625949816557523265317)
                  ·
                    refine ⟨1272867365590604535612247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6788625949816557523265317 1272867365590604535612247)
                    ·
                      rfl

theorem cell23_7436701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_7436701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436701 prefixEnd_7436701 := by exact prefixLift 7436701
  have htrace : WordTrace (prefixWord ++ tailWord_7436701) baseStart_7436701 baseEnd_7436701 := by
    simpa [prefixWord, tailWord_7436701, baseEnd_7436701] using wordTrace_append hprefix tailTrace_7436701
  have hstable : (prefixWord ++ tailWord_7436701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436701).length < 2 ^ (prefixWord ++ tailWord_7436701).sum := by decide
  have hdescent : baseEnd_7436701 < baseStart_7436701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436707 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 3]
def baseStart_7436707 : Nat := 118140960795 + 7436707 * 2 ^ 59
def prefixEnd_7436707 : Nat := 4983230072969 + 3 ^ 40 * 7436707 * 2
def baseEnd_7436707 : Nat := 3818605177655740583361713

theorem tailTrace_7436707 : CollatzResearch.WordTrace tailWord_7436707 prefixEnd_7436707 3818605177655740583361713 := by
  unfold tailWord_7436707
  simp only [CollatzResearch.WordTrace]
  refine ⟨271238987469088102283804375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180825991646058734855869583 271238987469088102283804375)
  ·
    refine ⟨406858481203632153425706563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271238987469088102283804375 406858481203632153425706563)
    ·
      refine ⟨610287721805448230138559845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406858481203632153425706563 610287721805448230138559845)
      ·
        refine ⟨114428947838521543150979971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610287721805448230138559845 114428947838521543150979971)
        ·
          refine ⟨171643421757782314726469957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114428947838521543150979971 171643421757782314726469957)
          ·
            refine ⟨32183141579584184011213117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171643421757782314726469957 32183141579584184011213117)
            ·
              refine ⟨12068678092344069004204919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32183141579584184011213117 12068678092344069004204919)
              ·
                refine ⟨18103017138516103506307379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12068678092344069004204919 18103017138516103506307379)
                ·
                  refine ⟨27154525707774155259461069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18103017138516103506307379 27154525707774155259461069)
                  ·
                    refine ⟨10182947140415308222297901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27154525707774155259461069 10182947140415308222297901)
                    ·
                      refine ⟨3818605177655740583361713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10182947140415308222297901 3818605177655740583361713)
                      ·
                        rfl

theorem cell23_7436707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_7436707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436707 prefixEnd_7436707 := by exact prefixLift 7436707
  have htrace : WordTrace (prefixWord ++ tailWord_7436707) baseStart_7436707 baseEnd_7436707 := by
    simpa [prefixWord, tailWord_7436707, baseEnd_7436707] using wordTrace_append hprefix tailTrace_7436707
  have hstable : (prefixWord ++ tailWord_7436707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436707).length < 2 ^ (prefixWord ++ tailWord_7436707).sum := by decide
  have hdescent : baseEnd_7436707 < baseStart_7436707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436725 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_7436725 : Nat := 118140960795 + 7436725 * 2 ^ 59
def prefixEnd_7436725 : Nat := 4983230072969 + 3 ^ 40 * 7436725 * 2
def baseEnd_7436725 : Nat := 3818614420307521512936631

theorem tailTrace_7436725 : CollatzResearch.WordTrace tailWord_7436725 prefixEnd_7436725 3818614420307521512936631 := by
  unfold tailWord_7436725
  simp only [CollatzResearch.WordTrace]
  refine ⟨271239643983022891357959629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180826429322015260905306419 271239643983022891357959629)
  ·
    refine ⟨101714866493633584259234861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271239643983022891357959629 101714866493633584259234861)
    ·
      refine ⟨38143074935112594097213073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101714866493633584259234861 38143074935112594097213073)
      ·
        refine ⟨28607306201334445572909805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38143074935112594097213073 28607306201334445572909805)
        ·
          refine ⟨10727739825500417089841177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28607306201334445572909805 10727739825500417089841177)
          ·
            refine ⟨8045804869125312817380883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10727739825500417089841177 8045804869125312817380883)
            ·
              refine ⟨12068707303687969226071325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045804869125312817380883 12068707303687969226071325)
              ·
                refine ⟨4525765238882988459776747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12068707303687969226071325 4525765238882988459776747)
                ·
                  refine ⟨6788647858324482689665121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525765238882988459776747 6788647858324482689665121)
                  ·
                    refine ⟨5091485893743362017248841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788647858324482689665121 5091485893743362017248841)
                    ·
                      refine ⟨3818614420307521512936631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091485893743362017248841 3818614420307521512936631)
                      ·
                        rfl

theorem cell23_7436725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_7436725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436725 prefixEnd_7436725 := by exact prefixLift 7436725
  have htrace : WordTrace (prefixWord ++ tailWord_7436725) baseStart_7436725 baseEnd_7436725 := by
    simpa [prefixWord, tailWord_7436725, baseEnd_7436725] using wordTrace_append hprefix tailTrace_7436725
  have hstable : (prefixWord ++ tailWord_7436725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436725).length < 2 ^ (prefixWord ++ tailWord_7436725).sum := by decide
  have hdescent : baseEnd_7436725 < baseStart_7436725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436750 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7436750 : Nat := 118140960795 + 7436750 * 2 ^ 59
def prefixEnd_7436750 : Nat := 4983230072969 + 3 ^ 40 * 7436750 * 2
def baseEnd_7436750 : Nat := 3818627257323883915124015

theorem tailTrace_7436750 : CollatzResearch.WordTrace tailWord_7436750 prefixEnd_7436750 3818627257323883915124015 := by
  unfold tailWord_7436750
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905069475991540078452463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180827037205288213751746469 33905069475991540078452463)
  ·
    refine ⟨50857604213987310117678695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33905069475991540078452463 50857604213987310117678695)
    ·
      refine ⟨76286406320980965176518043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50857604213987310117678695 76286406320980965176518043)
      ·
        refine ⟨114429609481471447764777065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76286406320980965176518043 114429609481471447764777065)
        ·
          refine ⟨85822207111103585823582799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114429609481471447764777065 85822207111103585823582799)
          ·
            refine ⟨128733310666655378735374199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85822207111103585823582799 128733310666655378735374199)
            ·
              refine ⟨193099965999983068103061299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128733310666655378735374199 193099965999983068103061299)
              ·
                refine ⟨289649948999974602154591949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193099965999983068103061299 289649948999974602154591949)
                ·
                  refine ⟨108618730874990475807971981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289649948999974602154591949 108618730874990475807971981)
                  ·
                    refine ⟨40732024078121428427989493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108618730874990475807971981 40732024078121428427989493)
                    ·
                      refine ⟨3818627257323883915124015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40732024078121428427989493 3818627257323883915124015)
                      ·
                        rfl

theorem cell23_7436750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7436750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436750 prefixEnd_7436750 := by exact prefixLift 7436750
  have htrace : WordTrace (prefixWord ++ tailWord_7436750) baseStart_7436750 baseEnd_7436750 := by
    simpa [prefixWord, tailWord_7436750, baseEnd_7436750] using wordTrace_append hprefix tailTrace_7436750
  have hstable : (prefixWord ++ tailWord_7436750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436750).length < 2 ^ (prefixWord ++ tailWord_7436750).sum := by decide
  have hdescent : baseEnd_7436750 < baseStart_7436750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436760 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_7436760 : Nat := 118140960795 + 7436760 * 2 ^ 59
def prefixEnd_7436760 : Nat := 4983230072969 + 3 ^ 40 * 7436760 * 2
def baseEnd_7436760 : Nat := 3818632392130428875998969

theorem tailTrace_7436760 : CollatzResearch.WordTrace tailWord_7436760 prefixEnd_7436760 3818632392130428875998969 := by
  unfold tailWord_7436760
  simp only [CollatzResearch.WordTrace]
  refine ⟨135620460268948046167741867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180827280358597394890322489 135620460268948046167741867)
  ·
    refine ⟨203430690403422069251612801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135620460268948046167741867 203430690403422069251612801)
    ·
      refine ⟨152573017802566551938709601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203430690403422069251612801 152573017802566551938709601)
      ·
        refine ⟨114429763351924913954032201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152573017802566551938709601 114429763351924913954032201)
        ·
          refine ⟨85822322513943685465524151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114429763351924913954032201 85822322513943685465524151)
          ·
            refine ⟨128733483770915528198286227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85822322513943685465524151 128733483770915528198286227)
            ·
              refine ⟨193100225656373292297429341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128733483770915528198286227 193100225656373292297429341)
              ·
                refine ⟨72412584621139984611536003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193100225656373292297429341 72412584621139984611536003)
                ·
                  refine ⟨108618876931709976917304005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72412584621139984611536003 108618876931709976917304005)
                  ·
                    refine ⟨20366039424695620671994501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108618876931709976917304005 20366039424695620671994501)
                    ·
                      refine ⟨3818632392130428875998969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20366039424695620671994501 3818632392130428875998969)
                      ·
                        rfl

theorem cell23_7436760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_7436760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436760 prefixEnd_7436760 := by exact prefixLift 7436760
  have htrace : WordTrace (prefixWord ++ tailWord_7436760) baseStart_7436760 baseEnd_7436760 := by
    simpa [prefixWord, tailWord_7436760, baseEnd_7436760] using wordTrace_append hprefix tailTrace_7436760
  have hstable : (prefixWord ++ tailWord_7436760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436760).length < 2 ^ (prefixWord ++ tailWord_7436760).sum := by decide
  have hdescent : baseEnd_7436760 < baseStart_7436760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436781 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7436781 : Nat := 118140960795 + 7436781 * 2 ^ 59
def prefixEnd_7436781 : Nat := 4983230072969 + 3 ^ 40 * 7436781 * 2
def baseEnd_7436781 : Nat := 3818643175224173293836373

theorem tailTrace_7436781 : CollatzResearch.WordTrace tailWord_7436781 prefixEnd_7436781 3818643175224173293836373 := by
  unfold tailWord_7436781
  simp only [CollatzResearch.WordTrace]
  refine ⟨271241686470820012921998197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180827790980546675281332131 271241686470820012921998197)
  ·
    refine ⟨25428908106639376211437331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271241686470820012921998197 25428908106639376211437331)
    ·
      refine ⟨38143362159959064317155997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25428908106639376211437331 38143362159959064317155997)
      ·
        refine ⟨14303760809984649118933499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38143362159959064317155997 14303760809984649118933499)
        ·
          refine ⟨21455641214976973678400249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14303760809984649118933499 21455641214976973678400249)
          ·
            refine ⟨16091730911232730258800187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21455641214976973678400249 16091730911232730258800187)
            ·
              refine ⟨24137596366849095388200281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16091730911232730258800187 24137596366849095388200281)
              ·
                refine ⟨18103197275136821541150211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24137596366849095388200281 18103197275136821541150211)
                ·
                  refine ⟨27154795912705232311725317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18103197275136821541150211 27154795912705232311725317)
                  ·
                    refine ⟨5091524233632231058448497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27154795912705232311725317 5091524233632231058448497)
                    ·
                      refine ⟨3818643175224173293836373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091524233632231058448497 3818643175224173293836373)
                      ·
                        rfl

theorem cell23_7436781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7436781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436781 prefixEnd_7436781 := by exact prefixLift 7436781
  have htrace : WordTrace (prefixWord ++ tailWord_7436781) baseStart_7436781 baseEnd_7436781 := by
    simpa [prefixWord, tailWord_7436781, baseEnd_7436781] using wordTrace_append hprefix tailTrace_7436781
  have hstable : (prefixWord ++ tailWord_7436781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436781).length < 2 ^ (prefixWord ++ tailWord_7436781).sum := by decide
  have hdescent : baseEnd_7436781 < baseStart_7436781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436787 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 5]
def baseStart_7436787 : Nat := 118140960795 + 7436787 * 2 ^ 59
def prefixEnd_7436787 : Nat := 4983230072969 + 3 ^ 40 * 7436787 * 2
def baseEnd_7436787 : Nat := 424294028456455585595705

theorem tailTrace_7436787 : CollatzResearch.WordTrace tailWord_7436787 prefixEnd_7436787 424294028456455585595705 := by
  unfold tailWord_7436787
  simp only [CollatzResearch.WordTrace]
  refine ⟨271241905308798275946716615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180827936872532183964477743 271241905308798275946716615)
  ·
    refine ⟨406862857963197413920074923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271241905308798275946716615 406862857963197413920074923)
    ·
      refine ⟨610294286944796120880112385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406862857963197413920074923 610294286944796120880112385)
      ·
        refine ⟨457720715208597090660084289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610294286944796120880112385 457720715208597090660084289)
        ·
          refine ⟨343290536406447817995063217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457720715208597090660084289 343290536406447817995063217)
          ·
            refine ⟨257467902304835863496297413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343290536406447817995063217 257467902304835863496297413)
            ·
              refine ⟨48275231682156724405555765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257467902304835863496297413 48275231682156724405555765)
              ·
                refine ⟨4525802970202192913020853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48275231682156724405555765 4525802970202192913020853)
                ·
                  refine ⟨424294028456455585595705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4525802970202192913020853 424294028456455585595705)
                  ·
                    rfl

theorem cell23_7436787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 5].length) (baseStart_7436787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436787 prefixEnd_7436787 := by exact prefixLift 7436787
  have htrace : WordTrace (prefixWord ++ tailWord_7436787) baseStart_7436787 baseEnd_7436787 := by
    simpa [prefixWord, tailWord_7436787, baseEnd_7436787] using wordTrace_append hprefix tailTrace_7436787
  have hstable : (prefixWord ++ tailWord_7436787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436787).length < 2 ^ (prefixWord ++ tailWord_7436787).sum := by decide
  have hdescent : baseEnd_7436787 < baseStart_7436787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436797 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_7436797 : Nat := 118140960795 + 7436797 * 2 ^ 59
def prefixEnd_7436797 : Nat := 4983230072969 + 3 ^ 40 * 7436797 * 2
def baseEnd_7436797 : Nat := 3818651390914645231236299

theorem tailTrace_7436797 : CollatzResearch.WordTrace tailWord_7436797 prefixEnd_7436797 3818651390914645231236299 := by
  unfold tailWord_7436797
  simp only [CollatzResearch.WordTrace]
  refine ⟨271242270038762047654580645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180828180025841365103053763 271242270038762047654580645)
  ·
    refine ⟨50857925632267883935233871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271242270038762047654580645 50857925632267883935233871)
    ·
      refine ⟨76286888448401825902850807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50857925632267883935233871 76286888448401825902850807)
      ·
        refine ⟨114430332672602738854276211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76286888448401825902850807 114430332672602738854276211)
        ·
          refine ⟨171645499008904108281414317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114430332672602738854276211 171645499008904108281414317)
          ·
            refine ⟨64367062128339040605530369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171645499008904108281414317 64367062128339040605530369)
            ·
              refine ⟨48275296596254280454147777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64367062128339040605530369 48275296596254280454147777)
              ·
                refine ⟨36206472447190710340610833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48275296596254280454147777 36206472447190710340610833)
                ·
                  refine ⟨27154854335393032755458125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36206472447190710340610833 27154854335393032755458125)
                  ·
                    refine ⟨10183070375772387283296797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27154854335393032755458125 10183070375772387283296797)
                    ·
                      refine ⟨3818651390914645231236299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10183070375772387283296797 3818651390914645231236299)
                      ·
                        rfl

theorem cell23_7436797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_7436797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436797 prefixEnd_7436797 := by exact prefixLift 7436797
  have htrace : WordTrace (prefixWord ++ tailWord_7436797) baseStart_7436797 baseEnd_7436797 := by
    simpa [prefixWord, tailWord_7436797, baseEnd_7436797] using wordTrace_append hprefix tailTrace_7436797
  have hstable : (prefixWord ++ tailWord_7436797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436797).length < 2 ^ (prefixWord ++ tailWord_7436797).sum := by decide
  have hdescent : baseEnd_7436797 < baseStart_7436797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436814 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7436814 : Nat := 118140960795 + 7436814 * 2 ^ 59
def prefixEnd_7436814 : Nat := 4983230072969 + 3 ^ 40 * 7436814 * 2
def baseEnd_7436814 : Nat := 3818660120085771664723721

theorem tailTrace_7436814 : CollatzResearch.WordTrace tailWord_7436814 prefixEnd_7436814 3818660120085771664723721 := by
  unfold tailWord_7436814
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905361259962557444743687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180828593386466973038632997 33905361259962557444743687)
  ·
    refine ⟨50858041889943836167115531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33905361259962557444743687 50858041889943836167115531)
    ·
      refine ⟨76287062834915754250673297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50858041889943836167115531 76287062834915754250673297)
      ·
        refine ⟨57215297126186815688004973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76287062834915754250673297 57215297126186815688004973)
        ·
          refine ⟨21455736422320055883001865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57215297126186815688004973 21455736422320055883001865)
          ·
            refine ⟨16091802316740041912251399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21455736422320055883001865 16091802316740041912251399)
            ·
              refine ⟨24137703475110062868377099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16091802316740041912251399 24137703475110062868377099)
              ·
                refine ⟨36206555212665094302565649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24137703475110062868377099 36206555212665094302565649)
                ·
                  refine ⟨27154916409498820726924237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36206555212665094302565649 27154916409498820726924237)
                  ·
                    refine ⟨10183093653562057772596589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27154916409498820726924237 10183093653562057772596589)
                    ·
                      refine ⟨3818660120085771664723721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10183093653562057772596589 3818660120085771664723721)
                      ·
                        rfl

theorem cell23_7436814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7436814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436814 prefixEnd_7436814 := by exact prefixLift 7436814
  have htrace : WordTrace (prefixWord ++ tailWord_7436814) baseStart_7436814 baseEnd_7436814 := by
    simpa [prefixWord, tailWord_7436814, baseEnd_7436814] using wordTrace_append hprefix tailTrace_7436814
  have hstable : (prefixWord ++ tailWord_7436814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436814).length < 2 ^ (prefixWord ++ tailWord_7436814).sum := by decide
  have hdescent : baseEnd_7436814 < baseStart_7436814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436887 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_7436887 : Nat := 118140960795 + 7436887 * 2 ^ 59
def prefixEnd_7436887 : Nat := 4983230072969 + 3 ^ 40 * 7436887 * 2
def baseEnd_7436887 : Nat := 3818697604173549879110885

theorem tailTrace_7436887 : CollatzResearch.WordTrace tailWord_7436887 prefixEnd_7436887 3818697604173549879110885 := by
  unfold tailWord_7436887
  simp only [CollatzResearch.WordTrace]
  refine ⟨271245552608435993025356915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180830368405623995350237943 271245552608435993025356915)
  ·
    refine ⟨406868328912653989538035373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271245552608435993025356915 406868328912653989538035373)
    ·
      refine ⟨152575623342245246076763265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406868328912653989538035373 152575623342245246076763265)
      ·
        refine ⟨114431717506683934557572449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152575623342245246076763265 114431717506683934557572449)
        ·
          refine ⟨85823788130012950918179337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114431717506683934557572449 85823788130012950918179337)
          ·
            refine ⟨64367841097509713188634503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85823788130012950918179337 64367841097509713188634503)
            ·
              refine ⟨96551761646264569782951755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64367841097509713188634503 96551761646264569782951755)
              ·
                refine ⟨144827642469396854674427633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96551761646264569782951755 144827642469396854674427633)
                ·
                  refine ⟨108620731852047641005820725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144827642469396854674427633 108620731852047641005820725)
                  ·
                    refine ⟨10183193611129466344295693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108620731852047641005820725 10183193611129466344295693)
                    ·
                      refine ⟨3818697604173549879110885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10183193611129466344295693 3818697604173549879110885)
                      ·
                        rfl

theorem cell23_7436887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_7436887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436887 prefixEnd_7436887 := by exact prefixLift 7436887
  have htrace : WordTrace (prefixWord ++ tailWord_7436887) baseStart_7436887 baseEnd_7436887 := by
    simpa [prefixWord, tailWord_7436887, baseEnd_7436887] using wordTrace_append hprefix tailTrace_7436887
  have hstable : (prefixWord ++ tailWord_7436887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436887).length < 2 ^ (prefixWord ++ tailWord_7436887).sum := by decide
  have hdescent : baseEnd_7436887 < baseStart_7436887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436921 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 3]
def baseStart_7436921 : Nat := 118140960795 + 7436921 * 2 ^ 59
def prefixEnd_7436921 : Nat := 4983230072969 + 3 ^ 40 * 7436921 * 2
def baseEnd_7436921 : Nat := 3818715062515802746085729

theorem tailTrace_7436921 : CollatzResearch.WordTrace tailWord_7436921 prefixEnd_7436921 3818715062515802746085729 := by
  unfold tailWord_7436921
  simp only [CollatzResearch.WordTrace]
  refine ⟨271246792690312816832094617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180831195126875211221396411 271246792690312816832094617)
  ·
    refine ⟨203435094517734612624070963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271246792690312816832094617 203435094517734612624070963)
    ·
      refine ⟨305152641776601918936106445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203435094517734612624070963 305152641776601918936106445)
      ·
        refine ⟨114432240666225719601039917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305152641776601918936106445 114432240666225719601039917)
        ·
          refine ⟨42912090249834644850389969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114432240666225719601039917 42912090249834644850389969)
          ·
            refine ⟨32184067687375983637792477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42912090249834644850389969 32184067687375983637792477)
            ·
              refine ⟨12069025382765993864172179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32184067687375983637792477 12069025382765993864172179)
              ·
                refine ⟨18103538074148990796258269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12069025382765993864172179 18103538074148990796258269)
                ·
                  refine ⟨6788826777805871548596851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18103538074148990796258269 6788826777805871548596851)
                  ·
                    refine ⟨10183240166708807322895277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788826777805871548596851 10183240166708807322895277)
                    ·
                      refine ⟨3818715062515802746085729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10183240166708807322895277 3818715062515802746085729)
                      ·
                        rfl

theorem cell23_7436921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_7436921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436921 prefixEnd_7436921 := by exact prefixLift 7436921
  have htrace : WordTrace (prefixWord ++ tailWord_7436921) baseStart_7436921 baseEnd_7436921 := by
    simpa [prefixWord, tailWord_7436921, baseEnd_7436921] using wordTrace_append hprefix tailTrace_7436921
  have hstable : (prefixWord ++ tailWord_7436921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436921).length < 2 ^ (prefixWord ++ tailWord_7436921).sum := by decide
  have hdescent : baseEnd_7436921 < baseStart_7436921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436937 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_7436937 : Nat := 118140960795 + 7436937 * 2 ^ 59
def prefixEnd_7436937 : Nat := 4983230072969 + 3 ^ 40 * 7436937 * 2
def baseEnd_7436937 : Nat := 1272907759402091561161885

theorem tailTrace_7436937 : CollatzResearch.WordTrace tailWord_7436937 prefixEnd_7436937 1272907759402091561161885 := by
  unfold tailWord_7436937
  simp only [CollatzResearch.WordTrace]
  refine ⟨271247376258254851564677065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180831584172169901043118043 271247376258254851564677065)
  ·
    refine ⟨203435532193691138673507799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271247376258254851564677065 203435532193691138673507799)
    ·
      refine ⟨305153298290536708010261699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203435532193691138673507799 305153298290536708010261699)
      ·
        refine ⟨457729947435805062015392549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305153298290536708010261699 457729947435805062015392549)
        ·
          refine ⟨85824365144213449127886103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457729947435805062015392549 85824365144213449127886103)
          ·
            refine ⟨128736547716320173691829155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85824365144213449127886103 128736547716320173691829155)
            ·
              refine ⟨193104821574480260537743733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128736547716320173691829155 193104821574480260537743733)
              ·
                refine ⟨18103577022607524425413475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193104821574480260537743733 18103577022607524425413475)
                ·
                  refine ⟨27155365533911286638120213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18103577022607524425413475 27155365533911286638120213)
                  ·
                    refine ⟨1272907759402091561161885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27155365533911286638120213 1272907759402091561161885)
                    ·
                      rfl

theorem cell23_7436937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_7436937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436937 prefixEnd_7436937 := by exact prefixLift 7436937
  have htrace : WordTrace (prefixWord ++ tailWord_7436937) baseStart_7436937 baseEnd_7436937 := by
    simpa [prefixWord, tailWord_7436937, baseEnd_7436937] using wordTrace_append hprefix tailTrace_7436937
  have hstable : (prefixWord ++ tailWord_7436937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436937).length < 2 ^ (prefixWord ++ tailWord_7436937).sum := by decide
  have hdescent : baseEnd_7436937 < baseStart_7436937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436947 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 3]
def baseStart_7436947 : Nat := 118140960795 + 7436947 * 2 ^ 59
def prefixEnd_7436947 : Nat := 4983230072969 + 3 ^ 40 * 7436947 * 2
def baseEnd_7436947 : Nat := 3818728413012819644360609

theorem tailTrace_7436947 : CollatzResearch.WordTrace tailWord_7436947 prefixEnd_7436947 3818728413012819644360609 := by
  unfold tailWord_7436947
  simp only [CollatzResearch.WordTrace]
  refine ⟨271247740988218623272541095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180831827325479082181694063 271247740988218623272541095)
  ·
    refine ⟨406871611482327934908811643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271247740988218623272541095 406871611482327934908811643)
    ·
      refine ⟨610307417223491902363217465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406871611482327934908811643 610307417223491902363217465)
      ·
        refine ⟨457730562917618926772413099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610307417223491902363217465 457730562917618926772413099)
        ·
          refine ⟨686595844376428390158619649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457730562917618926772413099 686595844376428390158619649)
          ·
            refine ⟨514946883282321292618964737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686595844376428390158619649 514946883282321292618964737)
            ·
              refine ⟨386210162461740969464223553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514946883282321292618964737 386210162461740969464223553)
              ·
                refine ⟨289657621846305727098167665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386210162461740969464223553 289657621846305727098167665)
                ·
                  refine ⟨217243216384729295323625749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289657621846305727098167665 217243216384729295323625749)
                  ·
                    refine ⟨10183275768034185718294957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 217243216384729295323625749 10183275768034185718294957)
                    ·
                      refine ⟨3818728413012819644360609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10183275768034185718294957 3818728413012819644360609)
                      ·
                        rfl

theorem cell23_7436947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_7436947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436947 prefixEnd_7436947 := by exact prefixLift 7436947
  have htrace : WordTrace (prefixWord ++ tailWord_7436947) baseStart_7436947 baseEnd_7436947 := by
    simpa [prefixWord, tailWord_7436947, baseEnd_7436947] using wordTrace_append hprefix tailTrace_7436947
  have hstable : (prefixWord ++ tailWord_7436947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436947).length < 2 ^ (prefixWord ++ tailWord_7436947).sum := by decide
  have hdescent : baseEnd_7436947 < baseStart_7436947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436948 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7436948 : Nat := 118140960795 + 7436948 * 2 ^ 59
def prefixEnd_7436948 : Nat := 4983230072969 + 3 ^ 40 * 7436948 * 2
def baseEnd_7436948 : Nat := 3818728926493474140448105

theorem tailTrace_7436948 : CollatzResearch.WordTrace tailWord_7436948 prefixEnd_7436948 3818728926493474140448105 := by
  unfold tailWord_7436948
  simp only [CollatzResearch.WordTrace]
  refine ⟨135623888730607500221663749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180831851640810000295551665 135623888730607500221663749)
  ·
    refine ⟨25429479136988906291561953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135623888730607500221663749 25429479136988906291561953)
    ·
      refine ⟨19072109352741679718671465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25429479136988906291561953 19072109352741679718671465)
      ·
        refine ⟨14304082014556259789003599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19072109352741679718671465 14304082014556259789003599)
        ·
          refine ⟨21456123021834389683505399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304082014556259789003599 21456123021834389683505399)
          ·
            refine ⟨32184184532751584525258099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21456123021834389683505399 32184184532751584525258099)
            ·
              refine ⟨48276276799127376787887149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32184184532751584525258099 48276276799127376787887149)
              ·
                refine ⟨18103603799672766295457681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48276276799127376787887149 18103603799672766295457681)
                ·
                  refine ⟨13577702849754574721593261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18103603799672766295457681 13577702849754574721593261)
                  ·
                    refine ⟨5091638568657965520597473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13577702849754574721593261 5091638568657965520597473)
                    ·
                      refine ⟨3818728926493474140448105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091638568657965520597473 3818728926493474140448105)
                      ·
                        rfl

theorem cell23_7436948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7436948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436948 prefixEnd_7436948 := by exact prefixLift 7436948
  have htrace : WordTrace (prefixWord ++ tailWord_7436948) baseStart_7436948 baseEnd_7436948 := by
    simpa [prefixWord, tailWord_7436948, baseEnd_7436948] using wordTrace_append hprefix tailTrace_7436948
  have hstable : (prefixWord ++ tailWord_7436948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436948).length < 2 ^ (prefixWord ++ tailWord_7436948).sum := by decide
  have hdescent : baseEnd_7436948 < baseStart_7436948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436958 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_7436958 : Nat := 118140960795 + 7436958 * 2 ^ 59
def prefixEnd_7436958 : Nat := 4983230072969 + 3 ^ 40 * 7436958 * 2
def baseEnd_7436958 : Nat := 1272911353766673033774353

theorem tailTrace_7436958 : CollatzResearch.WordTrace tailWord_7436958 prefixEnd_7436958 1272911353766673033774353 := by
  unfold tailWord_7436958
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906017773897346518898941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180832094794119181434127685 33906017773897346518898941)
  ·
    refine ⟨12714756665211504944587103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33906017773897346518898941 12714756665211504944587103)
    ·
      refine ⟨19072134997817257416880655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12714756665211504944587103 19072134997817257416880655)
      ·
        refine ⟨28608202496725886125320983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19072134997817257416880655 28608202496725886125320983)
        ·
          refine ⟨42912303745088829187981475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28608202496725886125320983 42912303745088829187981475)
          ·
            refine ⟨64368455617633243781972213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42912303745088829187981475 64368455617633243781972213)
            ·
              refine ⟨6034542714153116604559895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64368455617633243781972213 6034542714153116604559895)
              ·
                refine ⟨9051814071229674906839843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034542714153116604559895 9051814071229674906839843)
                ·
                  refine ⟨13577721106844512360259765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9051814071229674906839843 13577721106844512360259765)
                  ·
                    refine ⟨1272911353766673033774353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13577721106844512360259765 1272911353766673033774353)
                    ·
                      rfl

theorem cell23_7436958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_7436958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436958 prefixEnd_7436958 := by exact prefixLift 7436958
  have htrace : WordTrace (prefixWord ++ tailWord_7436958) baseStart_7436958 baseEnd_7436958 := by
    simpa [prefixWord, tailWord_7436958, baseEnd_7436958] using wordTrace_append hprefix tailTrace_7436958
  have hstable : (prefixWord ++ tailWord_7436958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436958).length < 2 ^ (prefixWord ++ tailWord_7436958).sum := by decide
  have hdescent : baseEnd_7436958 < baseStart_7436958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7436981 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_7436981 : Nat := 118140960795 + 7436981 * 2 ^ 59
def prefixEnd_7436981 : Nat := 4983230072969 + 3 ^ 40 * 7436981 * 2
def baseEnd_7436981 : Nat := 3818745871355072511335453

theorem tailTrace_7436981 : CollatzResearch.WordTrace tailWord_7436981 prefixEnd_7436981 3818745871355072511335453 := by
  unfold tailWord_7436981
  simp only [CollatzResearch.WordTrace]
  refine ⟨271248981070095447079278797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180832654046730298052852531 271248981070095447079278797)
  ·
    refine ⟨101718367901285792654729549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271248981070095447079278797 101718367901285792654729549)
    ·
      refine ⟨38144387962982172245523581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101718367901285792654729549 38144387962982172245523581)
      ·
        refine ⟨14304145486118314592071343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38144387962982172245523581 14304145486118314592071343)
        ·
          refine ⟨21456218229177471888107015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304145486118314592071343 21456218229177471888107015)
          ·
            refine ⟨32184327343766207832160523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21456218229177471888107015 32184327343766207832160523)
            ·
              refine ⟨48276491015649311748240785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32184327343766207832160523 48276491015649311748240785)
              ·
                refine ⟨36207368261736983811180589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48276491015649311748240785 36207368261736983811180589)
                ·
                  refine ⟨13577763098151368929192721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36207368261736983811180589 13577763098151368929192721)
                  ·
                    refine ⟨10183322323613526696894541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13577763098151368929192721 10183322323613526696894541)
                    ·
                      refine ⟨3818745871355072511335453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10183322323613526696894541 3818745871355072511335453)
                      ·
                        rfl

theorem cell23_7436981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_7436981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7436981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7436981 prefixEnd_7436981 := by exact prefixLift 7436981
  have htrace : WordTrace (prefixWord ++ tailWord_7436981) baseStart_7436981 baseEnd_7436981 := by
    simpa [prefixWord, tailWord_7436981, baseEnd_7436981] using wordTrace_append hprefix tailTrace_7436981
  have hstable : (prefixWord ++ tailWord_7436981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7436981).length < 2 ^ (prefixWord ++ tailWord_7436981).sum := by decide
  have hdescent : baseEnd_7436981 < baseStart_7436981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7436981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437012 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7437012 : Nat := 118140960795 + 7437012 * 2 ^ 59
def prefixEnd_7437012 : Nat := 4983230072969 + 3 ^ 40 * 7437012 * 2
def baseEnd_7437012 : Nat := 3818761789255361890047811

theorem tailTrace_7437012 : CollatzResearch.WordTrace tailWord_7437012 prefixEnd_7437012 3818761789255361890047811 := by
  unfold tailWord_7437012
  simp only [CollatzResearch.WordTrace]
  refine ⟨135625055866491569686828645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180833407821988759582438193 135625055866491569686828645)
  ·
    refine ⟨25429697974967169316280371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135625055866491569686828645 25429697974967169316280371)
    ·
      refine ⟨38144546962450753974420557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25429697974967169316280371 38144546962450753974420557)
      ·
        refine ⟨14304205110919032740407709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38144546962450753974420557 14304205110919032740407709)
        ·
          refine ⟨5364076916594637277652891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14304205110919032740407709 5364076916594637277652891)
          ·
            refine ⟨8046115374891955916479337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5364076916594637277652891 8046115374891955916479337)
            ·
              refine ⟨6034586531168966937359503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8046115374891955916479337 6034586531168966937359503)
              ·
                refine ⟨9051879796753450406039255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034586531168966937359503 9051879796753450406039255)
                ·
                  refine ⟨13577819695130175609058883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9051879796753450406039255 13577819695130175609058883)
                  ·
                    refine ⟨20366729542695263413588325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13577819695130175609058883 20366729542695263413588325)
                    ·
                      refine ⟨3818761789255361890047811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20366729542695263413588325 3818761789255361890047811)
                      ·
                        rfl

theorem cell23_7437012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7437012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437012 prefixEnd_7437012 := by exact prefixLift 7437012
  have htrace : WordTrace (prefixWord ++ tailWord_7437012) baseStart_7437012 baseEnd_7437012 := by
    simpa [prefixWord, tailWord_7437012, baseEnd_7437012] using wordTrace_append hprefix tailTrace_7437012
  have hstable : (prefixWord ++ tailWord_7437012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437012).length < 2 ^ (prefixWord ++ tailWord_7437012).sum := by decide
  have hdescent : baseEnd_7437012 < baseStart_7437012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437028 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_7437028 : Nat := 118140960795 + 7437028 * 2 ^ 59
def prefixEnd_7437028 : Nat := 4983230072969 + 3 ^ 40 * 7437028 * 2
def baseEnd_7437028 : Nat := 3818770004945833827447737

theorem tailTrace_7437028 : CollatzResearch.WordTrace tailWord_7437028 prefixEnd_7437028 3818770004945833827447737 := by
  unfold tailWord_7437028
  simp only [CollatzResearch.WordTrace]
  refine ⟨135625347650462587053119869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180833796867283449404159825 135625347650462587053119869)
  ·
    refine ⟨50859505368923470144919951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135625347650462587053119869 50859505368923470144919951)
    ·
      refine ⟨76289258053385205217379927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50859505368923470144919951 76289258053385205217379927)
      ·
        refine ⟨114433887080077807826069891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76289258053385205217379927 114433887080077807826069891)
        ·
          refine ⟨171650830620116711739104837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114433887080077807826069891 171650830620116711739104837)
          ·
            refine ⟨32184530741271883451082157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171650830620116711739104837 32184530741271883451082157)
            ·
              refine ⟨12069199027976956294155809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32184530741271883451082157 12069199027976956294155809)
              ·
                refine ⟨9051899270982717220616857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12069199027976956294155809 9051899270982717220616857)
                ·
                  refine ⟨6788924453237037915462643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051899270982717220616857 6788924453237037915462643)
                  ·
                    refine ⟨10183386679855556873193965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788924453237037915462643 10183386679855556873193965)
                    ·
                      refine ⟨3818770004945833827447737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10183386679855556873193965 3818770004945833827447737)
                      ·
                        rfl

theorem cell23_7437028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_7437028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437028 prefixEnd_7437028 := by exact prefixLift 7437028
  have htrace : WordTrace (prefixWord ++ tailWord_7437028) baseStart_7437028 baseEnd_7437028 := by
    simpa [prefixWord, tailWord_7437028, baseEnd_7437028] using wordTrace_append hprefix tailTrace_7437028
  have hstable : (prefixWord ++ tailWord_7437028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437028).length < 2 ^ (prefixWord ++ tailWord_7437028).sum := by decide
  have hdescent : baseEnd_7437028 < baseStart_7437028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437102 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7437102 : Nat := 118140960795 + 7437102 * 2 ^ 59
def prefixEnd_7437102 : Nat := 4983230072969 + 3 ^ 40 * 7437102 * 2
def baseEnd_7437102 : Nat := 3818808002514266537922397

theorem tailTrace_7437102 : CollatzResearch.WordTrace tailWord_7437102 prefixEnd_7437102 3818808002514266537922397 := by
  unfold tailWord_7437102
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906674287832135593054195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180835596201771389829622373 33906674287832135593054195)
  ·
    refine ⟨50860011431748203389581293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33906674287832135593054195 50860011431748203389581293)
    ·
      refine ⟨19072504286905576271092985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50860011431748203389581293 19072504286905576271092985)
      ·
        refine ⟨14304378215179182203319739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19072504286905576271092985 14304378215179182203319739)
        ·
          refine ⟨21456567322768773304979609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304378215179182203319739 21456567322768773304979609)
          ·
            refine ⟨16092425492076579978734707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21456567322768773304979609 16092425492076579978734707)
            ·
              refine ⟨24138638238114869968102061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16092425492076579978734707 24138638238114869968102061)
              ·
                refine ⟨9051989339293076238038273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24138638238114869968102061 9051989339293076238038273)
                ·
                  refine ⟨6788992004469807178528705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051989339293076238038273 6788992004469807178528705)
                  ·
                    refine ⟨5091744003352355383896529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788992004469807178528705 5091744003352355383896529)
                    ·
                      refine ⟨3818808002514266537922397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091744003352355383896529 3818808002514266537922397)
                      ·
                        rfl

theorem cell23_7437102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7437102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437102 prefixEnd_7437102 := by exact prefixLift 7437102
  have htrace : WordTrace (prefixWord ++ tailWord_7437102) baseStart_7437102 baseEnd_7437102 := by
    simpa [prefixWord, tailWord_7437102, baseEnd_7437102] using wordTrace_append hprefix tailTrace_7437102
  have hstable : (prefixWord ++ tailWord_7437102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437102).length < 2 ^ (prefixWord ++ tailWord_7437102).sum := by decide
  have hdescent : baseEnd_7437102 < baseStart_7437102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437141 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7437141 : Nat := 118140960795 + 7437141 * 2 ^ 59
def prefixEnd_7437141 : Nat := 4983230072969 + 3 ^ 40 * 7437141 * 2
def baseEnd_7437141 : Nat := 3818828028259791885334717

theorem tailTrace_7437141 : CollatzResearch.WordTrace tailWord_7437141 prefixEnd_7437141 3818828028259791885334717 := by
  unfold tailWord_7437141
  simp only [CollatzResearch.WordTrace]
  refine ⟨271254816749515794405103277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180836544499677196270068851 271254816749515794405103277)
  ·
    refine ⟨101720556281068422901913729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271254816749515794405103277 101720556281068422901913729)
    ·
      refine ⟨76290417210801317176435297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101720556281068422901913729 76290417210801317176435297)
      ·
        refine ⟨57217812908100987882326473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76290417210801317176435297 57217812908100987882326473)
        ·
          refine ⟨42913359681075740911744855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57217812908100987882326473 42913359681075740911744855)
          ·
            refine ⟨64370039521613611367617283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42913359681075740911744855 64370039521613611367617283)
            ·
              refine ⟨96555059282420417051425925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64370039521613611367617283 96555059282420417051425925)
              ·
                refine ⟨18104073615453828197142361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96555059282420417051425925 18104073615453828197142361)
                ·
                  refine ⟨13578055211590371147856771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18104073615453828197142361 13578055211590371147856771)
                  ·
                    refine ⟨20367082817385556721785157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13578055211590371147856771 20367082817385556721785157)
                    ·
                      refine ⟨3818828028259791885334717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20367082817385556721785157 3818828028259791885334717)
                      ·
                        rfl

theorem cell23_7437141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7437141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437141 prefixEnd_7437141 := by exact prefixLift 7437141
  have htrace : WordTrace (prefixWord ++ tailWord_7437141) baseStart_7437141 baseEnd_7437141 := by
    simpa [prefixWord, tailWord_7437141, baseEnd_7437141] using wordTrace_append hprefix tailTrace_7437141
  have hstable : (prefixWord ++ tailWord_7437141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437141).length < 2 ^ (prefixWord ++ tailWord_7437141).sum := by decide
  have hdescent : baseEnd_7437141 < baseStart_7437141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437151 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 3, 4]
def baseStart_7437151 : Nat := 118140960795 + 7437151 * 2 ^ 59
def prefixEnd_7437151 : Nat := 4983230072969 + 3 ^ 40 * 7437151 * 2
def baseEnd_7437151 : Nat := 1272944387688778948736557

theorem tailTrace_7437151 : CollatzResearch.WordTrace tailWord_7437151 prefixEnd_7437151 1272944387688778948736557 := by
  unfold tailWord_7437151
  simp only [CollatzResearch.WordTrace]
  refine ⟨271255181479479566112967307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180836787652986377408644871 271255181479479566112967307)
  ·
    refine ⟨406882772219219349169450961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271255181479479566112967307 406882772219219349169450961)
    ·
      refine ⟨305162079164414511877088221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406882772219219349169450961 305162079164414511877088221)
      ·
        refine ⟨114435779686655441953908083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305162079164414511877088221 114435779686655441953908083)
        ·
          refine ⟨171653669529983162930862125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114435779686655441953908083 171653669529983162930862125)
          ·
            refine ⟨64370126073743686099073297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171653669529983162930862125 64370126073743686099073297)
            ·
              refine ⟨48277594555307764574304973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64370126073743686099073297 48277594555307764574304973)
              ·
                refine ⟨18104097958240411715364365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48277594555307764574304973 18104097958240411715364365)
                ·
                  refine ⟨6789036734340154393261637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18104097958240411715364365 6789036734340154393261637)
                  ·
                    refine ⟨1272944387688778948736557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789036734340154393261637 1272944387688778948736557)
                    ·
                      rfl

theorem cell23_7437151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_7437151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437151 prefixEnd_7437151 := by exact prefixLift 7437151
  have htrace : WordTrace (prefixWord ++ tailWord_7437151) baseStart_7437151 baseEnd_7437151 := by
    simpa [prefixWord, tailWord_7437151, baseEnd_7437151] using wordTrace_append hprefix tailTrace_7437151
  have hstable : (prefixWord ++ tailWord_7437151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437151).length < 2 ^ (prefixWord ++ tailWord_7437151).sum := by decide
  have hdescent : baseEnd_7437151 < baseStart_7437151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437248 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4]
def baseStart_7437248 : Nat := 118140960795 + 7437248 * 2 ^ 59
def prefixEnd_7437248 : Nat := 4983230072969 + 3 ^ 40 * 7437248 * 2
def baseEnd_7437248 : Nat := 3818882970689822966696725

theorem tailTrace_7437248 : CollatzResearch.WordTrace tailWord_7437248 prefixEnd_7437248 3818882970689822966696725 := by
  unfold tailWord_7437248
  simp only [CollatzResearch.WordTrace]
  refine ⟨135629359680064075839624199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180839146240085434452832265 135629359680064075839624199)
  ·
    refine ⟨203444039520096113759436299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135629359680064075839624199 203444039520096113759436299)
    ·
      refine ⟨305166059280144170639154449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203444039520096113759436299 305166059280144170639154449)
      ·
        refine ⟨228874544460108127979365837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305166059280144170639154449 228874544460108127979365837)
        ·
          refine ⟨85827954172540547992262189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228874544460108127979365837 85827954172540547992262189)
          ·
            refine ⟨32185482814702705497098321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85827954172540547992262189 32185482814702705497098321)
            ·
              refine ⟨24139112111027029122823741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32185482814702705497098321 24139112111027029122823741)
              ·
                refine ⟨9052167041635135921058903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24139112111027029122823741 9052167041635135921058903)
                ·
                  refine ⟨13578250562452703881588355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9052167041635135921058903 13578250562452703881588355)
                  ·
                    refine ⟨20367375843679055822382533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13578250562452703881588355 20367375843679055822382533)
                    ·
                      refine ⟨3818882970689822966696725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20367375843679055822382533 3818882970689822966696725)
                      ·
                        rfl

theorem cell23_7437248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_7437248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437248 prefixEnd_7437248 := by exact prefixLift 7437248
  have htrace : WordTrace (prefixWord ++ tailWord_7437248) baseStart_7437248 baseEnd_7437248 := by
    simpa [prefixWord, tailWord_7437248, baseEnd_7437248] using wordTrace_append hprefix tailTrace_7437248
  have hstable : (prefixWord ++ tailWord_7437248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437248).length < 2 ^ (prefixWord ++ tailWord_7437248).sum := by decide
  have hdescent : baseEnd_7437248 < baseStart_7437248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437258 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_7437258 : Nat := 118140960795 + 7437258 * 2 ^ 59
def prefixEnd_7437258 : Nat := 4983230072969 + 3 ^ 40 * 7437258 * 2
def baseEnd_7437258 : Nat := 1272962701832122642523893

theorem tailTrace_7437258 : CollatzResearch.WordTrace tailWord_7437258 prefixEnd_7437258 1272962701832122642523893 := by
  unfold tailWord_7437258
  simp only [CollatzResearch.WordTrace]
  refine ⟨67814771022522980846778107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180839389393394615591408285 67814771022522980846778107)
  ·
    refine ⟨101722156533784471270167161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67814771022522980846778107 101722156533784471270167161)
    ·
      refine ⟨76291617400338353452625371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101722156533784471270167161 76291617400338353452625371)
      ·
        refine ⟨114437426100507530178938057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76291617400338353452625371 114437426100507530178938057)
        ·
          refine ⟨85828069575380647634203543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114437426100507530178938057 85828069575380647634203543)
          ·
            refine ⟨128742104363070971451305315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85828069575380647634203543 128742104363070971451305315)
            ·
              refine ⟨193113156544606457176957973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128742104363070971451305315 193113156544606457176957973)
              ·
                refine ⟨9052179213028427680169905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193113156544606457176957973 9052179213028427680169905)
                ·
                  refine ⟨6789134409771320760127429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052179213028427680169905 6789134409771320760127429)
                  ·
                    refine ⟨1272962701832122642523893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789134409771320760127429 1272962701832122642523893)
                    ·
                      rfl

theorem cell23_7437258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_7437258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437258 prefixEnd_7437258 := by exact prefixLift 7437258
  have htrace : WordTrace (prefixWord ++ tailWord_7437258) baseStart_7437258 baseEnd_7437258 := by
    simpa [prefixWord, tailWord_7437258, baseEnd_7437258] using wordTrace_append hprefix tailTrace_7437258
  have hstable : (prefixWord ++ tailWord_7437258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437258).length < 2 ^ (prefixWord ++ tailWord_7437258).sum := by decide
  have hdescent : baseEnd_7437258 < baseStart_7437258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437268 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7437268 : Nat := 118140960795 + 7437268 * 2 ^ 59
def prefixEnd_7437268 : Nat := 4983230072969 + 3 ^ 40 * 7437268 * 2
def baseEnd_7437268 : Nat := 3818893240302912888446633

theorem tailTrace_7437268 : CollatzResearch.WordTrace tailWord_7437268 prefixEnd_7437268 3818893240302912888446633 := by
  unfold tailWord_7437268
  simp only [CollatzResearch.WordTrace]
  refine ⟨135629724410027847547488229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180839632546703796729984305 135629724410027847547488229)
  ·
    refine ⟨25430573326880221415154043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135629724410027847547488229 25430573326880221415154043)
    ·
      refine ⟨38145859990320332122731065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25430573326880221415154043 38145859990320332122731065)
      ·
        refine ⟨28609394992740249092048299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38145859990320332122731065 28609394992740249092048299)
        ·
          refine ⟨42914092489110373638072449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28609394992740249092048299 42914092489110373638072449)
          ·
            refine ⟨32185569366832780228554337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42914092489110373638072449 32185569366832780228554337)
            ·
              refine ⟨24139177025124585171415753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32185569366832780228554337 24139177025124585171415753)
              ·
                refine ⟨18104382768843438878561815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24139177025124585171415753 18104382768843438878561815)
                ·
                  refine ⟨27156574153265158317842723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18104382768843438878561815 27156574153265158317842723)
                  ·
                    refine ⟨40734861229897737476764085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27156574153265158317842723 40734861229897737476764085)
                    ·
                      refine ⟨3818893240302912888446633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40734861229897737476764085 3818893240302912888446633)
                      ·
                        rfl

theorem cell23_7437268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7437268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437268 prefixEnd_7437268 := by exact prefixLift 7437268
  have htrace : WordTrace (prefixWord ++ tailWord_7437268) baseStart_7437268 baseEnd_7437268 := by
    simpa [prefixWord, tailWord_7437268, baseEnd_7437268] using wordTrace_append hprefix tailTrace_7437268
  have hstable : (prefixWord ++ tailWord_7437268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437268).length < 2 ^ (prefixWord ++ tailWord_7437268).sum := by decide
  have hdescent : baseEnd_7437268 < baseStart_7437268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437282 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7437282 : Nat := 118140960795 + 7437282 * 2 ^ 59
def prefixEnd_7437282 : Nat := 4983230072969 + 3 ^ 40 * 7437282 * 2
def baseEnd_7437282 : Nat := 3818900429032075833671569

theorem tailTrace_7437282 : CollatzResearch.WordTrace tailWord_7437282 prefixEnd_7437282 3818900429032075833671569 := by
  unfold tailWord_7437282
  simp only [CollatzResearch.WordTrace]
  refine ⟨67814989860501243871496525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180839972961336650323990733 67814989860501243871496525)
  ·
    refine ⟨25430621197687966451811197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67814989860501243871496525 25430621197687966451811197)
    ·
      refine ⟨9536482949132987419429199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25430621197687966451811197 9536482949132987419429199)
      ·
        refine ⟨14304724423699481129143799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536482949132987419429199 14304724423699481129143799)
        ·
          refine ⟨21457086635549221693715699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304724423699481129143799 21457086635549221693715699)
          ·
            refine ⟨32185629953323832540573549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21457086635549221693715699 32185629953323832540573549)
            ·
              refine ⟨12069611232496437202715081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32185629953323832540573549 12069611232496437202715081)
              ·
                refine ⟨9052208424372327902036311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12069611232496437202715081 9052208424372327902036311)
                ·
                  refine ⟨13578312636558491853054467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9052208424372327902036311 13578312636558491853054467)
                  ·
                    refine ⟨20367468954837737779581701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13578312636558491853054467 20367468954837737779581701)
                    ·
                      refine ⟨3818900429032075833671569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20367468954837737779581701 3818900429032075833671569)
                      ·
                        rfl

theorem cell23_7437282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7437282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437282 prefixEnd_7437282 := by exact prefixLift 7437282
  have htrace : WordTrace (prefixWord ++ tailWord_7437282) baseStart_7437282 baseEnd_7437282 := by
    simpa [prefixWord, tailWord_7437282, baseEnd_7437282] using wordTrace_append hprefix tailTrace_7437282
  have hstable : (prefixWord ++ tailWord_7437282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437282).length < 2 ^ (prefixWord ++ tailWord_7437282).sum := by decide
  have hdescent : baseEnd_7437282 < baseStart_7437282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437355 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 4, 2, 2]
def baseStart_7437355 : Nat := 118140960795 + 7437355 * 2 ^ 59
def prefixEnd_7437355 : Nat := 4983230072969 + 3 ^ 40 * 7437355 * 2
def baseEnd_7437355 : Nat := 3818937913119854048058733

theorem tailTrace_7437355 : CollatzResearch.WordTrace tailWord_7437355 prefixEnd_7437355 3818937913119854048058733 := by
  unfold tailWord_7437355
  simp only [CollatzResearch.WordTrace]
  refine ⟨271262621970740508953393519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180841747980493672635595679 271262621970740508953393519)
  ·
    refine ⟨406893932956110763430090279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271262621970740508953393519 406893932956110763430090279)
    ·
      refine ⟨610340899434166145145135419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406893932956110763430090279 610340899434166145145135419)
      ·
        refine ⟨915511349151249217717703129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610340899434166145145135419 915511349151249217717703129)
        ·
          refine ⟨686633511863436913288277347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915511349151249217717703129 686633511863436913288277347)
          ·
            refine ⟨1029950267795155369932416021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686633511863436913288277347 1029950267795155369932416021)
            ·
              refine ⟨48278918802897907965582001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1029950267795155369932416021 48278918802897907965582001)
              ·
                refine ⟨36209189102173430974186501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48278918802897907965582001 36209189102173430974186501)
                ·
                  refine ⟨6789222956657518307659969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36209189102173430974186501 6789222956657518307659969)
                  ·
                    refine ⟨5091917217493138730744977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789222956657518307659969 5091917217493138730744977)
                    ·
                      refine ⟨3818937913119854048058733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091917217493138730744977 3818937913119854048058733)
                      ·
                        rfl

theorem cell23_7437355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 2, 2].length) (baseStart_7437355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437355 prefixEnd_7437355 := by exact prefixLift 7437355
  have htrace : WordTrace (prefixWord ++ tailWord_7437355) baseStart_7437355 baseEnd_7437355 := by
    simpa [prefixWord, tailWord_7437355, baseEnd_7437355] using wordTrace_append hprefix tailTrace_7437355
  have hstable : (prefixWord ++ tailWord_7437355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437355).length < 2 ^ (prefixWord ++ tailWord_7437355).sum := by decide
  have hdescent : baseEnd_7437355 < baseStart_7437355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437358 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7437358 : Nat := 118140960795 + 7437358 * 2 ^ 59
def prefixEnd_7437358 : Nat := 4983230072969 + 3 ^ 40 * 7437358 * 2
def baseEnd_7437358 : Nat := 3818939453561817536321219

theorem tailTrace_7437358 : CollatzResearch.WordTrace tailWord_7437358 prefixEnd_7437358 3818939453561817536321219 := by
  unfold tailWord_7437358
  simp only [CollatzResearch.WordTrace]
  refine ⟨33907841423716205058219091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180841820926486426977168485 33907841423716205058219091)
  ·
    refine ⟨50861762135574307587328637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33907841423716205058219091 50861762135574307587328637)
    ·
      refine ⟨19073160800840365345248239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50861762135574307587328637 19073160800840365345248239)
      ·
        refine ⟨28609741201260548017872359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19073160800840365345248239 28609741201260548017872359)
        ·
          refine ⟨42914611801890822026808539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28609741201260548017872359 42914611801890822026808539)
          ·
            refine ⟨64371917702836233040212809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42914611801890822026808539 64371917702836233040212809)
            ·
              refine ⟨48278938277127174780159607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64371917702836233040212809 48278938277127174780159607)
              ·
                refine ⟨72418407415690762170239411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48278938277127174780159607 72418407415690762170239411)
                ·
                  refine ⟨108627611123536143255359117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72418407415690762170239411 108627611123536143255359117)
                  ·
                    refine ⟨40735354171326053720759669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108627611123536143255359117 40735354171326053720759669)
                    ·
                      refine ⟨3818939453561817536321219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40735354171326053720759669 3818939453561817536321219)
                      ·
                        rfl

theorem cell23_7437358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7437358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437358 prefixEnd_7437358 := by exact prefixLift 7437358
  have htrace : WordTrace (prefixWord ++ tailWord_7437358) baseStart_7437358 baseEnd_7437358 := by
    simpa [prefixWord, tailWord_7437358, baseEnd_7437358] using wordTrace_append hprefix tailTrace_7437358
  have hstable : (prefixWord ++ tailWord_7437358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437358).length < 2 ^ (prefixWord ++ tailWord_7437358).sum := by decide
  have hdescent : baseEnd_7437358 < baseStart_7437358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437361 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 9]
def baseStart_7437361 : Nat := 118140960795 + 7437361 * 2 ^ 59
def prefixEnd_7437361 : Nat := 4983230072969 + 3 ^ 40 * 7437361 * 2
def baseEnd_7437361 : Nat := 424326777111531224953745

theorem tailTrace_7437361 : CollatzResearch.WordTrace tailWord_7437361 prefixEnd_7437361 424326777111531224953745 := by
  unfold tailWord_7437361
  simp only [CollatzResearch.WordTrace]
  refine ⟨271262840808718771978111937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180841893872479181318741291 271262840808718771978111937)
  ·
    refine ⟨203447130606539078983583953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271262840808718771978111937 203447130606539078983583953)
    ·
      refine ⟨152585347954904309237687965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203447130606539078983583953 152585347954904309237687965)
      ·
        refine ⟨57219505483089115964132987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152585347954904309237687965 57219505483089115964132987)
        ·
          refine ⟨85829258224633673946199481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57219505483089115964132987 85829258224633673946199481)
          ·
            refine ⟨64371943668475255459649611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85829258224633673946199481 64371943668475255459649611)
            ·
              refine ⟨96557915502712883189474417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64371943668475255459649611 96557915502712883189474417)
              ·
                refine ⟨72418436627034662392105813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96557915502712883189474417 72418436627034662392105813)
                ·
                  refine ⟨424326777111531224953745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72418436627034662392105813 424326777111531224953745)
                  ·
                    rfl

theorem cell23_7437361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_7437361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437361 prefixEnd_7437361 := by exact prefixLift 7437361
  have htrace : WordTrace (prefixWord ++ tailWord_7437361) baseStart_7437361 baseEnd_7437361 := by
    simpa [prefixWord, tailWord_7437361, baseEnd_7437361] using wordTrace_append hprefix tailTrace_7437361
  have hstable : (prefixWord ++ tailWord_7437361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437361).length < 2 ^ (prefixWord ++ tailWord_7437361).sum := by decide
  have hdescent : baseEnd_7437361 < baseStart_7437361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437368 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_7437368 : Nat := 118140960795 + 7437368 * 2 ^ 59
def prefixEnd_7437368 : Nat := 4983230072969 + 3 ^ 40 * 7437368 * 2
def baseEnd_7437368 : Nat := 3818944588368362497196173

theorem tailTrace_7437368 : CollatzResearch.WordTrace tailWord_7437368 prefixEnd_7437368 3818944588368362497196173 := by
  unfold tailWord_7437368
  simp only [CollatzResearch.WordTrace]
  refine ⟨135631548059846706086808379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180842064079795608115744505 135631548059846706086808379)
  ·
    refine ⟨203447322089770059130212569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135631548059846706086808379 203447322089770059130212569)
    ·
      refine ⟨152585491567327544347659427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203447322089770059130212569 152585491567327544347659427)
      ·
        refine ⟨228878237350991316521489141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152585491567327544347659427 228878237350991316521489141)
        ·
          refine ⟨21457334751655435923889607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228878237350991316521489141 21457334751655435923889607)
          ·
            refine ⟨32186002127483153885834411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21457334751655435923889607 32186002127483153885834411)
            ·
              refine ⟨48279003191224730828751617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32186002127483153885834411 48279003191224730828751617)
              ·
                refine ⟨36209252393418548121563713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48279003191224730828751617 36209252393418548121563713)
                ·
                  refine ⟨27156939295063911091172785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36209252393418548121563713 27156939295063911091172785)
                  ·
                    refine ⟨20367704471297933318379589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27156939295063911091172785 20367704471297933318379589)
                    ·
                      refine ⟨3818944588368362497196173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20367704471297933318379589 3818944588368362497196173)
                      ·
                        rfl

theorem cell23_7437368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_7437368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437368 prefixEnd_7437368 := by exact prefixLift 7437368
  have htrace : WordTrace (prefixWord ++ tailWord_7437368) baseStart_7437368 baseEnd_7437368 := by
    simpa [prefixWord, tailWord_7437368, baseEnd_7437368] using wordTrace_append hprefix tailTrace_7437368
  have hstable : (prefixWord ++ tailWord_7437368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437368).length < 2 ^ (prefixWord ++ tailWord_7437368).sum := by decide
  have hdescent : baseEnd_7437368 < baseStart_7437368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437372 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_7437372 : Nat := 118140960795 + 7437372 * 2 ^ 59
def prefixEnd_7437372 : Nat := 4983230072969 + 3 ^ 40 * 7437372 * 2
def baseEnd_7437372 : Nat := 3818946642290980481546155

theorem tailTrace_7437372 : CollatzResearch.WordTrace tailWord_7437372 prefixEnd_7437372 3818946642290980481546155 := by
  unfold tailWord_7437372
  simp only [CollatzResearch.WordTrace]
  refine ⟨135631621005839460428381185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180842161341119280571174913 135631621005839460428381185)
  ·
    refine ⟨101723715754379595321285889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135631621005839460428381185 101723715754379595321285889)
    ·
      refine ⟨76292786815784696490964417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101723715754379595321285889 76292786815784696490964417)
      ·
        refine ⟨57219590111838522368223313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76292786815784696490964417 57219590111838522368223313)
        ·
          refine ⟨42914692583878891776167485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57219590111838522368223313 42914692583878891776167485)
          ·
            refine ⟨16093009718954584416062807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42914692583878891776167485 16093009718954584416062807)
            ·
              refine ⟨24139514578431876624094211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093009718954584416062807 24139514578431876624094211)
              ·
                refine ⟨36209271867647814936141317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24139514578431876624094211 36209271867647814936141317)
                ·
                  refine ⟨6789238475183965300526497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36209271867647814936141317 6789238475183965300526497)
                  ·
                    refine ⟨5091928856387973975394873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789238475183965300526497 5091928856387973975394873)
                    ·
                      refine ⟨3818946642290980481546155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091928856387973975394873 3818946642290980481546155)
                      ·
                        rfl

theorem cell23_7437372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_7437372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437372 prefixEnd_7437372 := by exact prefixLift 7437372
  have htrace : WordTrace (prefixWord ++ tailWord_7437372) baseStart_7437372 baseEnd_7437372 := by
    simpa [prefixWord, tailWord_7437372, baseEnd_7437372] using wordTrace_append hprefix tailTrace_7437372
  have hstable : (prefixWord ++ tailWord_7437372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437372).length < 2 ^ (prefixWord ++ tailWord_7437372).sum := by decide
  have hdescent : baseEnd_7437372 < baseStart_7437372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437389 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7437389 : Nat := 118140960795 + 7437389 * 2 ^ 59
def prefixEnd_7437389 : Nat := 4983230072969 + 3 ^ 40 * 7437389 * 2
def baseEnd_7437389 : Nat := 3818955371462106915033577

theorem tailTrace_7437389 : CollatzResearch.WordTrace tailWord_7437389 prefixEnd_7437389 3818955371462106915033577 := by
  unfold tailWord_7437389
  simp only [CollatzResearch.WordTrace]
  refine ⟨271263862052617332760131221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180842574701744888506754147 271263862052617332760131221)
  ·
    refine ⟨12715493533716437473131151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271263862052617332760131221 12715493533716437473131151)
    ·
      refine ⟨19073240300574656209696727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12715493533716437473131151 19073240300574656209696727)
      ·
        refine ⟨28609860450861984314545091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19073240300574656209696727 28609860450861984314545091)
        ·
          refine ⟨42914790676292976471817637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28609860450861984314545091 42914790676292976471817637)
          ·
            refine ⟨8046523251804933088465807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42914790676292976471817637 8046523251804933088465807)
            ·
              refine ⟨12069784877707399632698711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8046523251804933088465807 12069784877707399632698711)
              ·
                refine ⟨18104677316561099449048067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12069784877707399632698711 18104677316561099449048067)
                ·
                  refine ⟨27157015974841649173572101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18104677316561099449048067 27157015974841649173572101)
                  ·
                    refine ⟨5091940495282809220044769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27157015974841649173572101 5091940495282809220044769)
                    ·
                      refine ⟨3818955371462106915033577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091940495282809220044769 3818955371462106915033577)
                      ·
                        rfl

theorem cell23_7437389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7437389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437389 prefixEnd_7437389 := by exact prefixLift 7437389
  have htrace : WordTrace (prefixWord ++ tailWord_7437389) baseStart_7437389 baseEnd_7437389 := by
    simpa [prefixWord, tailWord_7437389, baseEnd_7437389] using wordTrace_append hprefix tailTrace_7437389
  have hstable : (prefixWord ++ tailWord_7437389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437389).length < 2 ^ (prefixWord ++ tailWord_7437389).sum := by decide
  have hdescent : baseEnd_7437389 < baseStart_7437389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437401 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_7437401 : Nat := 118140960795 + 7437401 * 2 ^ 59
def prefixEnd_7437401 : Nat := 4983230072969 + 3 ^ 40 * 7437401 * 2
def baseEnd_7437401 : Nat := 3818961533229960868083521

theorem tailTrace_7437401 : CollatzResearch.WordTrace tailWord_7437401 prefixEnd_7437401 3818961533229960868083521 := by
  unfold tailWord_7437401
  simp only [CollatzResearch.WordTrace]
  refine ⟨271264299728573858809568057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180842866485715905873045371 271264299728573858809568057)
  ·
    refine ⟨203448224796430394107176043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271264299728573858809568057 203448224796430394107176043)
    ·
      refine ⟨305172337194645591160764065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203448224796430394107176043 305172337194645591160764065)
      ·
        refine ⟨228879252895984193370573049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305172337194645591160764065 228879252895984193370573049)
        ·
          refine ⟨171659439671988145027929787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228879252895984193370573049 171659439671988145027929787)
          ·
            refine ⟨257489159507982217541894681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171659439671988145027929787 257489159507982217541894681)
            ·
              refine ⟨193116869630986663156421011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257489159507982217541894681 193116869630986663156421011)
              ·
                refine ⟨289675304446479994734631517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193116869630986663156421011 289675304446479994734631517)
                ·
                  refine ⟨108628239167429998025486819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289675304446479994734631517 108628239167429998025486819)
                  ·
                    refine ⟨162942358751144997038230229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108628239167429998025486819 162942358751144997038230229)
                    ·
                      refine ⟨3818961533229960868083521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162942358751144997038230229 3818961533229960868083521)
                      ·
                        rfl

theorem cell23_7437401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_7437401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437401 prefixEnd_7437401 := by exact prefixLift 7437401
  have htrace : WordTrace (prefixWord ++ tailWord_7437401) baseStart_7437401 baseEnd_7437401 := by
    simpa [prefixWord, tailWord_7437401, baseEnd_7437401] using wordTrace_append hprefix tailTrace_7437401
  have hstable : (prefixWord ++ tailWord_7437401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437401).length < 2 ^ (prefixWord ++ tailWord_7437401).sum := by decide
  have hdescent : baseEnd_7437401 < baseStart_7437401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437406 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7437406 : Nat := 118140960795 + 7437406 * 2 ^ 59
def prefixEnd_7437406 : Nat := 4983230072969 + 3 ^ 40 * 7437406 * 2
def baseEnd_7437406 : Nat := 3818964100633233348520999

theorem tailTrace_7437406 : CollatzResearch.WordTrace tailWord_7437406 prefixEnd_7437406 3818964100633233348520999 := by
  unfold tailWord_7437406
  simp only [CollatzResearch.WordTrace]
  refine ⟨33908060261694468082937509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180842988062370496442333381 33908060261694468082937509)
  ·
    refine ⟨6357761299067712765550783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33908060261694468082937509 6357761299067712765550783)
    ·
      refine ⟨9536641948601569148326175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6357761299067712765550783 9536641948601569148326175)
      ·
        refine ⟨14304962922902353722489263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536641948601569148326175 14304962922902353722489263)
        ·
          refine ⟨21457444384353530583733895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304962922902353722489263 21457444384353530583733895)
          ·
            refine ⟨32186166576530295875600843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21457444384353530583733895 32186166576530295875600843)
            ·
              refine ⟨48279249864795443813401265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32186166576530295875600843 48279249864795443813401265)
              ·
                refine ⟨36209437398596582860050949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48279249864795443813401265 36209437398596582860050949)
                ·
                  refine ⟨6789269512236859286259553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36209437398596582860050949 6789269512236859286259553)
                  ·
                    refine ⟨5091952134177644464694665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789269512236859286259553 5091952134177644464694665)
                    ·
                      refine ⟨3818964100633233348520999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5091952134177644464694665 3818964100633233348520999)
                      ·
                        rfl

theorem cell23_7437406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7437406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437406 prefixEnd_7437406 := by exact prefixLift 7437406
  have htrace : WordTrace (prefixWord ++ tailWord_7437406) baseStart_7437406 baseEnd_7437406 := by
    simpa [prefixWord, tailWord_7437406, baseEnd_7437406] using wordTrace_append hprefix tailTrace_7437406
  have hstable : (prefixWord ++ tailWord_7437406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437406).length < 2 ^ (prefixWord ++ tailWord_7437406).sum := by decide
  have hdescent : baseEnd_7437406 < baseStart_7437406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437408 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_7437408 : Nat := 118140960795 + 7437408 * 2 ^ 59
def prefixEnd_7437408 : Nat := 4983230072969 + 3 ^ 40 * 7437408 * 2
def baseEnd_7437408 : Nat := 1272988375864847446898663

theorem tailTrace_7437408 : CollatzResearch.WordTrace tailWord_7437408 prefixEnd_7437408 1272988375864847446898663 := by
  unfold tailWord_7437408
  simp only [CollatzResearch.WordTrace]
  refine ⟨135632277519774249502536439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180843036693032332670048585 135632277519774249502536439)
  ·
    refine ⟨203448416279661374253804659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135632277519774249502536439 203448416279661374253804659)
    ·
      refine ⟨305172624419492061380706989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203448416279661374253804659 305172624419492061380706989)
      ·
        refine ⟨114439734157309523017765121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305172624419492061380706989 114439734157309523017765121)
        ·
          refine ⟨85829800617982142263323841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114439734157309523017765121 85829800617982142263323841)
          ·
            refine ⟨64372350463486606697492881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85829800617982142263323841 64372350463486606697492881)
            ·
              refine ⟨48279262847614955023119661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64372350463486606697492881 48279262847614955023119661)
              ·
                refine ⟨18104723567855608133669873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48279262847614955023119661 18104723567855608133669873)
                ·
                  refine ⟨13578542675891706100252405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18104723567855608133669873 13578542675891706100252405)
                  ·
                    refine ⟨1272988375864847446898663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13578542675891706100252405 1272988375864847446898663)
                    ·
                      rfl

theorem cell23_7437408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_7437408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437408 prefixEnd_7437408 := by exact prefixLift 7437408
  have htrace : WordTrace (prefixWord ++ tailWord_7437408) baseStart_7437408 baseEnd_7437408 := by
    simpa [prefixWord, tailWord_7437408, baseEnd_7437408] using wordTrace_append hprefix tailTrace_7437408
  have hstable : (prefixWord ++ tailWord_7437408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437408).length < 2 ^ (prefixWord ++ tailWord_7437408).sum := by decide
  have hdescent : baseEnd_7437408 < baseStart_7437408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437429 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 7]
def baseStart_7437429 : Nat := 118140960795 + 7437429 * 2 ^ 59
def prefixEnd_7437429 : Nat := 4983230072969 + 3 ^ 40 * 7437429 * 2
def baseEnd_7437429 : Nat := 424330656743142973170377

theorem tailTrace_7437429 : CollatzResearch.WordTrace tailWord_7437429 prefixEnd_7437429 424330656743142973170377 := by
  unfold tailWord_7437429
  simp only [CollatzResearch.WordTrace]
  refine ⟨271265320972472419591587341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180843547314981613061058227 271265320972472419591587341)
  ·
    refine ⟨101724495364677157346845253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271265320972472419591587341 101724495364677157346845253)
    ·
      refine ⟨19073342880876967002533485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101724495364677157346845253 19073342880876967002533485)
      ·
        refine ⟨7152503580328862625950057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19073342880876967002533485 7152503580328862625950057)
        ·
          refine ⟨5364377685246646969462543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7152503580328862625950057 5364377685246646969462543)
          ·
            refine ⟨8046566527869970454193815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5364377685246646969462543 8046566527869970454193815)
            ·
              refine ⟨12069849791804955681290723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8046566527869970454193815 12069849791804955681290723)
              ·
                refine ⟨18104774687707433521936085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12069849791804955681290723 18104774687707433521936085)
                ·
                  refine ⟨424330656743142973170377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18104774687707433521936085 424330656743142973170377)
                  ·
                    rfl

theorem cell23_7437429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_7437429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437429 prefixEnd_7437429 := by exact prefixLift 7437429
  have htrace : WordTrace (prefixWord ++ tailWord_7437429) baseStart_7437429 baseEnd_7437429 := by
    simpa [prefixWord, tailWord_7437429, baseEnd_7437429] using wordTrace_append hprefix tailTrace_7437429
  have hstable : (prefixWord ++ tailWord_7437429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437429).length < 2 ^ (prefixWord ++ tailWord_7437429).sum := by decide
  have hdescent : baseEnd_7437429 < baseStart_7437429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437472 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 1, 4]
def baseStart_7437472 : Nat := 118140960795 + 7437472 * 2 ^ 59
def prefixEnd_7437472 : Nat := 4983230072969 + 3 ^ 40 * 7437472 * 2
def baseEnd_7437472 : Nat := 1272999330118810030098565

theorem tailTrace_7437472 : CollatzResearch.WordTrace tailWord_7437472 prefixEnd_7437472 1272999330118810030098565 := by
  unfold tailWord_7437472
  simp only [CollatzResearch.WordTrace]
  refine ⟨135633444655658318967701335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180844592874211091956935113 135633444655658318967701335)
  ·
    refine ⟨203450166983487478451552003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135633444655658318967701335 203450166983487478451552003)
    ·
      refine ⟨305175250475231217677328005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203450166983487478451552003 305175250475231217677328005)
      ·
        refine ⟨57220359464105853314499001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305175250475231217677328005 57220359464105853314499001)
        ·
          refine ⟨42915269598079389985874251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57220359464105853314499001 42915269598079389985874251)
          ·
            refine ⟨64372904397119084978811377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42915269598079389985874251 64372904397119084978811377)
            ·
              refine ⟨48279678297839313734108533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64372904397119084978811377 48279678297839313734108533)
              ·
                refine ⟨4526219840422435662572675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48279678297839313734108533 4526219840422435662572675)
                ·
                  refine ⟨6789329760633653493859013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526219840422435662572675 6789329760633653493859013)
                  ·
                    refine ⟨1272999330118810030098565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789329760633653493859013 1272999330118810030098565)
                    ·
                      rfl

theorem cell23_7437472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 4].length) (baseStart_7437472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437472 prefixEnd_7437472 := by exact prefixLift 7437472
  have htrace : WordTrace (prefixWord ++ tailWord_7437472) baseStart_7437472 baseEnd_7437472 := by
    simpa [prefixWord, tailWord_7437472, baseEnd_7437472] using wordTrace_append hprefix tailTrace_7437472
  have hstable : (prefixWord ++ tailWord_7437472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437472).length < 2 ^ (prefixWord ++ tailWord_7437472).sum := by decide
  have hdescent : baseEnd_7437472 < baseStart_7437472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437489 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 1, 4]
def baseStart_7437489 : Nat := 118140960795 + 7437489 * 2 ^ 59
def prefixEnd_7437489 : Nat := 4983230072969 + 3 ^ 40 * 7437489 * 2
def baseEnd_7437489 : Nat := 1273002239842518841261039

theorem tailTrace_7437489 : CollatzResearch.WordTrace tailWord_7437489 prefixEnd_7437489 1273002239842518841261039 := by
  unfold tailWord_7437489
  simp only [CollatzResearch.WordTrace]
  refine ⟨271267509352255049838771521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180845006234836699892514347 271267509352255049838771521)
  ·
    refine ⟨203450632014191287379078641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271267509352255049838771521 203450632014191287379078641)
    ·
      refine ⟨152587974010643465534308981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203450632014191287379078641 152587974010643465534308981)
      ·
        refine ⟨14305122563497824893841467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152587974010643465534308981 14305122563497824893841467)
        ·
          refine ⟨21457683845246737340762201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14305122563497824893841467 21457683845246737340762201)
          ·
            refine ⟨16093262883935053005571651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21457683845246737340762201 16093262883935053005571651)
            ·
              refine ⟨24139894325902579508357477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093262883935053005571651 24139894325902579508357477)
              ·
                refine ⟨4526230186106733657817027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24139894325902579508357477 4526230186106733657817027)
                ·
                  refine ⟨6789345279160100486725541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526230186106733657817027 6789345279160100486725541)
                  ·
                    refine ⟨1273002239842518841261039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789345279160100486725541 1273002239842518841261039)
                    ·
                      rfl

theorem cell23_7437489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_7437489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437489 prefixEnd_7437489 := by exact prefixLift 7437489
  have htrace : WordTrace (prefixWord ++ tailWord_7437489) baseStart_7437489 baseEnd_7437489 := by
    simpa [prefixWord, tailWord_7437489, baseEnd_7437489] using wordTrace_append hprefix tailTrace_7437489
  have hstable : (prefixWord ++ tailWord_7437489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437489).length < 2 ^ (prefixWord ++ tailWord_7437489).sum := by decide
  have hdescent : baseEnd_7437489 < baseStart_7437489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437506 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7437506 : Nat := 118140960795 + 7437506 * 2 ^ 59
def prefixEnd_7437506 : Nat := 4983230072969 + 3 ^ 40 * 7437506 * 2
def baseEnd_7437506 : Nat := 1273005149566227652423513

theorem tailTrace_7437506 : CollatzResearch.WordTrace tailWord_7437506 prefixEnd_7437506 1273005149566227652423513 := by
  unfold tailWord_7437506
  simp only [CollatzResearch.WordTrace]
  refine ⟨67817032348298365435535093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180845419595462307828093581 67817032348298365435535093)
  ·
    refine ⟨6357846782652971759581415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67817032348298365435535093 6357846782652971759581415)
    ·
      refine ⟨9536770173979457639372123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6357846782652971759581415 9536770173979457639372123)
      ·
        refine ⟨14305155260969186459058185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536770173979457639372123 14305155260969186459058185)
        ·
          refine ⟨10728866445726889844293639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14305155260969186459058185 10728866445726889844293639)
          ·
            refine ⟨16093299668590334766440459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10728866445726889844293639 16093299668590334766440459)
            ·
              refine ⟨24139949502885502149660689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093299668590334766440459 24139949502885502149660689)
              ·
                refine ⟨18104962127164126612245517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24139949502885502149660689 18104962127164126612245517)
                ·
                  refine ⟨6789360797686547479592069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18104962127164126612245517 6789360797686547479592069)
                  ·
                    refine ⟨1273005149566227652423513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789360797686547479592069 1273005149566227652423513)
                    ·
                      rfl

theorem cell23_7437506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7437506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437506 prefixEnd_7437506 := by exact prefixLift 7437506
  have htrace : WordTrace (prefixWord ++ tailWord_7437506) baseStart_7437506 baseEnd_7437506 := by
    simpa [prefixWord, tailWord_7437506, baseEnd_7437506] using wordTrace_append hprefix tailTrace_7437506
  have hstable : (prefixWord ++ tailWord_7437506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437506).length < 2 ^ (prefixWord ++ tailWord_7437506).sum := by decide
  have hdescent : baseEnd_7437506 < baseStart_7437506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437522 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_7437522 : Nat := 118140960795 + 7437522 * 2 ^ 59
def prefixEnd_7437522 : Nat := 4983230072969 + 3 ^ 40 * 7437522 * 2
def baseEnd_7437522 : Nat := 3819023664389154894670465

theorem tailTrace_7437522 : CollatzResearch.WordTrace tailWord_7437522 prefixEnd_7437522 3819023664389154894670465 := by
  unfold tailWord_7437522
  simp only [CollatzResearch.WordTrace]
  refine ⟨67817178240283874118680705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180845808640756997649815213 67817178240283874118680705)
  ·
    refine ⟨50862883680212905589010529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67817178240283874118680705 50862883680212905589010529)
    ·
      refine ⟨38147162760159679191757897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50862883680212905589010529 38147162760159679191757897)
      ·
        refine ⟨28610372070119759393818423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38147162760159679191757897 28610372070119759393818423)
        ·
          refine ⟨42915558105179639090727635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28610372070119759393818423 42915558105179639090727635)
          ·
            refine ⟨64373337157769458636091453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42915558105179639090727635 64373337157769458636091453)
            ·
              refine ⟨24140001434163546988534295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64373337157769458636091453 24140001434163546988534295)
              ·
                refine ⟨36210002151245320482801443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24140001434163546988534295 36210002151245320482801443)
                ·
                  refine ⟨54315003226867980724202165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36210002151245320482801443 54315003226867980724202165)
                  ·
                    refine ⟨5092031552518873192893953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54315003226867980724202165 5092031552518873192893953)
                    ·
                      refine ⟨3819023664389154894670465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092031552518873192893953 3819023664389154894670465)
                      ·
                        rfl

theorem cell23_7437522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_7437522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437522 prefixEnd_7437522 := by exact prefixLift 7437522
  have htrace : WordTrace (prefixWord ++ tailWord_7437522) baseStart_7437522 baseEnd_7437522 := by
    simpa [prefixWord, tailWord_7437522, baseEnd_7437522] using wordTrace_append hprefix tailTrace_7437522
  have hstable : (prefixWord ++ tailWord_7437522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437522).length < 2 ^ (prefixWord ++ tailWord_7437522).sum := by decide
  have hdescent : baseEnd_7437522 < baseStart_7437522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437555 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5]
def baseStart_7437555 : Nat := 118140960795 + 7437555 * 2 ^ 59
def prefixEnd_7437555 : Nat := 4983230072969 + 3 ^ 40 * 7437555 * 2
def baseEnd_7437555 : Nat := 3819040609250753265557813

theorem tailTrace_7437555 : CollatzResearch.WordTrace tailWord_7437555 prefixEnd_7437555 3819040609250753265557813 := by
  unfold tailWord_7437555
  simp only [CollatzResearch.WordTrace]
  refine ⟨271269916570015943110674119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180846611046677295407116079 271269916570015943110674119)
  ·
    refine ⟨406904874855023914666011179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271269916570015943110674119 406904874855023914666011179)
    ·
      refine ⟨610357312282535871999016769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406904874855023914666011179 610357312282535871999016769)
      ·
        refine ⟨457767984211901903999262577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610357312282535871999016769 457767984211901903999262577)
        ·
          refine ⟨343325988158926427999446933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457767984211901903999262577 343325988158926427999446933)
          ·
            refine ⟨16093405694949676312474075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 343325988158926427999446933 16093405694949676312474075)
            ·
              refine ⟨24140108542424514468711113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093405694949676312474075 24140108542424514468711113)
              ·
                refine ⟨18105081406818385851533335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24140108542424514468711113 18105081406818385851533335)
                ·
                  refine ⟨27157622110227578777300003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18105081406818385851533335 27157622110227578777300003)
                  ·
                    refine ⟨40736433165341368165950005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27157622110227578777300003 40736433165341368165950005)
                    ·
                      refine ⟨3819040609250753265557813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40736433165341368165950005 3819040609250753265557813)
                      ·
                        rfl

theorem cell23_7437555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_7437555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437555 prefixEnd_7437555 := by exact prefixLift 7437555
  have htrace : WordTrace (prefixWord ++ tailWord_7437555) baseStart_7437555 baseEnd_7437555 := by
    simpa [prefixWord, tailWord_7437555, baseEnd_7437555] using wordTrace_append hprefix tailTrace_7437555
  have hstable : (prefixWord ++ tailWord_7437555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437555).length < 2 ^ (prefixWord ++ tailWord_7437555).sum := by decide
  have hdescent : baseEnd_7437555 < baseStart_7437555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437569 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_7437569 : Nat := 118140960795 + 7437569 * 2 ^ 59
def prefixEnd_7437569 : Nat := 4983230072969 + 3 ^ 40 * 7437569 * 2
def baseEnd_7437569 : Nat := 3819047797979916210782749

theorem tailTrace_7437569 : CollatzResearch.WordTrace tailWord_7437569 prefixEnd_7437569 3819047797979916210782749 := by
  unfold tailWord_7437569
  simp only [CollatzResearch.WordTrace]
  refine ⟨271270427191965223501683761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180846951461310149001122507 271270427191965223501683761)
  ·
    refine ⟨203452820393973917626262821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271270427191965223501683761 203452820393973917626262821)
    ·
      refine ⟨38147403823870109554924279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203452820393973917626262821 38147403823870109554924279)
      ·
        refine ⟨57221105735805164332386419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38147403823870109554924279 57221105735805164332386419)
        ·
          refine ⟨85831658603707746498579629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57221105735805164332386419 85831658603707746498579629)
          ·
            refine ⟨32186871976390404936967361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85831658603707746498579629 32186871976390404936967361)
            ·
              refine ⟨24140153982292803702725521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32186871976390404936967361 24140153982292803702725521)
              ·
                refine ⟨18105115486719602777044141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24140153982292803702725521 18105115486719602777044141)
                ·
                  refine ⟨6789418307519851041391553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18105115486719602777044141 6789418307519851041391553)
                  ·
                    refine ⟨5092063730639888281043665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789418307519851041391553 5092063730639888281043665)
                    ·
                      refine ⟨3819047797979916210782749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092063730639888281043665 3819047797979916210782749)
                      ·
                        rfl

theorem cell23_7437569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_7437569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437569 prefixEnd_7437569 := by exact prefixLift 7437569
  have htrace : WordTrace (prefixWord ++ tailWord_7437569) baseStart_7437569 baseEnd_7437569 := by
    simpa [prefixWord, tailWord_7437569, baseEnd_7437569] using wordTrace_append hprefix tailTrace_7437569
  have hstable : (prefixWord ++ tailWord_7437569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437569).length < 2 ^ (prefixWord ++ tailWord_7437569).sum := by decide
  have hdescent : baseEnd_7437569 < baseStart_7437569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437585 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_7437585 : Nat := 118140960795 + 7437585 * 2 ^ 59
def prefixEnd_7437585 : Nat := 4983230072969 + 3 ^ 40 * 7437585 * 2
def baseEnd_7437585 : Nat := 3819056013670388148182675

theorem tailTrace_7437585 : CollatzResearch.WordTrace tailWord_7437585 prefixEnd_7437585 3819056013670388148182675 := by
  unfold tailWord_7437585
  simp only [CollatzResearch.WordTrace]
  refine ⟨271271010759907258234266209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180847340506604838822844139 271271010759907258234266209)
  ·
    refine ⟨203453258069930443675699657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271271010759907258234266209 203453258069930443675699657)
    ·
      refine ⟨152589943552447832756774743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203453258069930443675699657 152589943552447832756774743)
      ·
        refine ⟨228884915328671749135162115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152589943552447832756774743 228884915328671749135162115)
        ·
          refine ⟨343327372993007623702743173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228884915328671749135162115 343327372993007623702743173)
          ·
            refine ⟨64373882436188929444264345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343327372993007623702743173 64373882436188929444264345)
            ·
              refine ⟨48280411827141697083198259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64373882436188929444264345 48280411827141697083198259)
              ·
                refine ⟨72420617740712545624797389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48280411827141697083198259 72420617740712545624797389)
                ·
                  refine ⟨27157731652767204609299021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72420617740712545624797389 27157731652767204609299021)
                  ·
                    refine ⟨10184149369787701728487133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27157731652767204609299021 10184149369787701728487133)
                    ·
                      refine ⟨3819056013670388148182675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10184149369787701728487133 3819056013670388148182675)
                      ·
                        rfl

theorem cell23_7437585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_7437585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437585 prefixEnd_7437585 := by exact prefixLift 7437585
  have htrace : WordTrace (prefixWord ++ tailWord_7437585) baseStart_7437585 baseEnd_7437585 := by
    simpa [prefixWord, tailWord_7437585, baseEnd_7437585] using wordTrace_append hprefix tailTrace_7437585
  have hstable : (prefixWord ++ tailWord_7437585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437585).length < 2 ^ (prefixWord ++ tailWord_7437585).sum := by decide
  have hdescent : baseEnd_7437585 < baseStart_7437585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437603 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 1, 2, 2]
def baseStart_7437603 : Nat := 118140960795 + 7437603 * 2 ^ 59
def prefixEnd_7437603 : Nat := 4983230072969 + 3 ^ 40 * 7437603 * 2
def baseEnd_7437603 : Nat := 3819065256322169077757593

theorem tailTrace_7437603 : CollatzResearch.WordTrace tailWord_7437603 prefixEnd_7437603 3819065256322169077757593 := by
  unfold tailWord_7437603
  simp only [CollatzResearch.WordTrace]
  refine ⟨271271667273842047308421463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180847778182561364872280975 271271667273842047308421463)
  ·
    refine ⟨406907500910763070962632195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271271667273842047308421463 406907500910763070962632195)
    ·
      refine ⟨610361251366144606443948293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406907500910763070962632195 610361251366144606443948293)
      ·
        refine ⟨114442734631152113708240305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610361251366144606443948293 114442734631152113708240305)
        ·
          refine ⟨85832050973364085281180229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114442734631152113708240305 85832050973364085281180229)
          ·
            refine ⟨16093509557505765990221293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85832050973364085281180229 16093509557505765990221293)
            ·
              refine ⟨6035066084064662246332985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16093509557505765990221293 6035066084064662246332985)
              ·
                refine ⟨4526299563048496684749739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035066084064662246332985 4526299563048496684749739)
                ·
                  refine ⟨6789449344572745027124609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526299563048496684749739 6789449344572745027124609)
                  ·
                    refine ⟨5092087008429558770343457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789449344572745027124609 5092087008429558770343457)
                    ·
                      refine ⟨3819065256322169077757593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092087008429558770343457 3819065256322169077757593)
                      ·
                        rfl

theorem cell23_7437603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_7437603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437603 prefixEnd_7437603 := by exact prefixLift 7437603
  have htrace : WordTrace (prefixWord ++ tailWord_7437603) baseStart_7437603 baseEnd_7437603 := by
    simpa [prefixWord, tailWord_7437603, baseEnd_7437603] using wordTrace_append hprefix tailTrace_7437603
  have hstable : (prefixWord ++ tailWord_7437603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437603).length < 2 ^ (prefixWord ++ tailWord_7437603).sum := by decide
  have hdescent : baseEnd_7437603 < baseStart_7437603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437612 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 3, 3, 2]
def baseStart_7437612 : Nat := 118140960795 + 7437612 * 2 ^ 59
def prefixEnd_7437612 : Nat := 4983230072969 + 3 ^ 40 * 7437612 * 2
def baseEnd_7437612 : Nat := 3819069877648059542545051

theorem tailTrace_7437612 : CollatzResearch.WordTrace tailWord_7437612 prefixEnd_7437612 3819069877648059542545051 := by
  unfold tailWord_7437612
  simp only [CollatzResearch.WordTrace]
  refine ⟨135635997765404720922749545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180847997020539627896999393 135635997765404720922749545)
  ·
    refine ⟨101726998324053540692062159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135635997765404720922749545 101726998324053540692062159)
    ·
      refine ⟨152590497486080311038093239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101726998324053540692062159 152590497486080311038093239)
      ·
        refine ⟨228885746229120466557139859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152590497486080311038093239 228885746229120466557139859)
        ·
          refine ⟨343328619343680699835709789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228885746229120466557139859 343328619343680699835709789)
          ·
            refine ⟨128748232253880262438391171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343328619343680699835709789 128748232253880262438391171)
            ·
              refine ⟨193122348380820393657586757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128748232253880262438391171 193122348380820393657586757)
              ·
                refine ⟨36210440321403823810797517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193122348380820393657586757 36210440321403823810797517)
                ·
                  refine ⟨13578915120526433929049069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36210440321403823810797517 13578915120526433929049069)
                  ·
                    refine ⟨5092093170197412723393401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13578915120526433929049069 5092093170197412723393401)
                    ·
                      refine ⟨3819069877648059542545051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092093170197412723393401 3819069877648059542545051)
                      ·
                        rfl

theorem cell23_7437612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_7437612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437612 prefixEnd_7437612 := by exact prefixLift 7437612
  have htrace : WordTrace (prefixWord ++ tailWord_7437612) baseStart_7437612 baseEnd_7437612 := by
    simpa [prefixWord, tailWord_7437612, baseEnd_7437612] using wordTrace_append hprefix tailTrace_7437612
  have hstable : (prefixWord ++ tailWord_7437612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437612).length < 2 ^ (prefixWord ++ tailWord_7437612).sum := by decide
  have hdescent : baseEnd_7437612 < baseStart_7437612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437613 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7437613 : Nat := 118140960795 + 7437613 * 2 ^ 59
def prefixEnd_7437613 : Nat := 4983230072969 + 3 ^ 40 * 7437613 * 2
def baseEnd_7437613 : Nat := 1273023463709571346210849

theorem tailTrace_7437613 : CollatzResearch.WordTrace tailWord_7437613 prefixEnd_7437613 1273023463709571346210849 := by
  unfold tailWord_7437613
  simp only [CollatzResearch.WordTrace]
  refine ⟨271272032003805819016285493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180848021335870546010856995 271272032003805819016285493)
  ·
    refine ⟨25431753000356795532776765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271272032003805819016285493 25431753000356795532776765)
    ·
      refine ⟨9536907375133798324791287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25431753000356795532776765 9536907375133798324791287)
      ·
        refine ⟨14305361062700697487186931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536907375133798324791287 14305361062700697487186931)
        ·
          refine ⟨21458041594051046230780397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14305361062700697487186931 21458041594051046230780397)
          ·
            refine ⟨8046765597769142336542649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21458041594051046230780397 8046765597769142336542649)
            ·
              refine ⟨6035074198326856752406987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8046765597769142336542649 6035074198326856752406987)
              ·
                refine ⟨9052611297490285128610481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035074198326856752406987 9052611297490285128610481)
                ·
                  refine ⟨6789458473117713846457861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052611297490285128610481 6789458473117713846457861)
                  ·
                    refine ⟨1273023463709571346210849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789458473117713846457861 1273023463709571346210849)
                    ·
                      rfl

theorem cell23_7437613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7437613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437613 prefixEnd_7437613 := by exact prefixLift 7437613
  have htrace : WordTrace (prefixWord ++ tailWord_7437613) baseStart_7437613 baseEnd_7437613 := by
    simpa [prefixWord, tailWord_7437613, baseEnd_7437613] using wordTrace_append hprefix tailTrace_7437613
  have hstable : (prefixWord ++ tailWord_7437613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437613).length < 2 ^ (prefixWord ++ tailWord_7437613).sum := by decide
  have hdescent : baseEnd_7437613 < baseStart_7437613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437619 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 3]
def baseStart_7437619 : Nat := 118140960795 + 7437619 * 2 ^ 59
def prefixEnd_7437619 : Nat := 4983230072969 + 3 ^ 40 * 7437619 * 2
def baseEnd_7437619 : Nat := 3819073472012641015157519

theorem tailTrace_7437619 : CollatzResearch.WordTrace tailWord_7437619 prefixEnd_7437619 3819073472012641015157519 := by
  unfold tailWord_7437619
  simp only [CollatzResearch.WordTrace]
  refine ⟨271272250841784082041003911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180848167227856054694002607 271272250841784082041003911)
  ·
    refine ⟨406908376262676123061505867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271272250841784082041003911 406908376262676123061505867)
    ·
      refine ⟨610362564394014184592258801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406908376262676123061505867 610362564394014184592258801)
      ·
        refine ⟨457771923295510638444194101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610362564394014184592258801 457771923295510638444194101)
        ·
          refine ⟨42916117808954122354143197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457771923295510638444194101 42916117808954122354143197)
          ·
            refine ⟨16093544178357795882803699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42916117808954122354143197 16093544178357795882803699)
            ·
              refine ⟨24140316267536693824205549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093544178357795882803699 24140316267536693824205549)
              ·
                refine ⟨9052618600326260184077081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24140316267536693824205549 9052618600326260184077081)
                ·
                  refine ⟨6789463950244695138057811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052618600326260184077081 6789463950244695138057811)
                  ·
                    refine ⟨10184195925367042707086717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6789463950244695138057811 10184195925367042707086717)
                    ·
                      refine ⟨3819073472012641015157519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10184195925367042707086717 3819073472012641015157519)
                      ·
                        rfl

theorem cell23_7437619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_7437619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437619 prefixEnd_7437619 := by exact prefixLift 7437619
  have htrace : WordTrace (prefixWord ++ tailWord_7437619) baseStart_7437619 baseEnd_7437619 := by
    simpa [prefixWord, tailWord_7437619, baseEnd_7437619] using wordTrace_append hprefix tailTrace_7437619
  have hstable : (prefixWord ++ tailWord_7437619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437619).length < 2 ^ (prefixWord ++ tailWord_7437619).sum := by decide
  have hdescent : baseEnd_7437619 < baseStart_7437619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437646 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_7437646 : Nat := 118140960795 + 7437646 * 2 ^ 59
def prefixEnd_7437646 : Nat := 4983230072969 + 3 ^ 40 * 7437646 * 2
def baseEnd_7437646 : Nat := 3819087335990312409519895

theorem tailTrace_7437646 : CollatzResearch.WordTrace tailWord_7437646 prefixEnd_7437646 3819087335990312409519895 := by
  unfold tailWord_7437646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33909154451585783206529599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180848823741790843768157861 33909154451585783206529599)
  ·
    refine ⟨50863731677378674809794399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33909154451585783206529599 50863731677378674809794399)
    ·
      refine ⟨76295597516068012214691599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50863731677378674809794399 76295597516068012214691599)
      ·
        refine ⟨114443396274102018322037399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76295597516068012214691599 114443396274102018322037399)
        ·
          refine ⟨171665094411153027483056099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114443396274102018322037399 171665094411153027483056099)
          ·
            refine ⟨257497641616729541224584149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171665094411153027483056099 257497641616729541224584149)
            ·
              refine ⟨6035100975392098622451191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257497641616729541224584149 6035100975392098622451191)
              ·
                refine ⟨9052651463088147933676787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035100975392098622451191 9052651463088147933676787)
                ·
                  refine ⟨13578977194632221900515181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9052651463088147933676787 13578977194632221900515181)
                  ·
                    refine ⟨5092116447987083212693193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13578977194632221900515181 5092116447987083212693193)
                    ·
                      refine ⟨3819087335990312409519895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092116447987083212693193 3819087335990312409519895)
                      ·
                        rfl

theorem cell23_7437646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_7437646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437646 prefixEnd_7437646 := by exact prefixLift 7437646
  have htrace : WordTrace (prefixWord ++ tailWord_7437646) baseStart_7437646 baseEnd_7437646 := by
    simpa [prefixWord, tailWord_7437646, baseEnd_7437646] using wordTrace_append hprefix tailTrace_7437646
  have hstable : (prefixWord ++ tailWord_7437646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437646).length < 2 ^ (prefixWord ++ tailWord_7437646).sum := by decide
  have hdescent : baseEnd_7437646 < baseStart_7437646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437654 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7437654 : Nat := 118140960795 + 7437654 * 2 ^ 59
def prefixEnd_7437654 : Nat := 4983230072969 + 3 ^ 40 * 7437654 * 2
def baseEnd_7437654 : Nat := 3819091443835548378219859

theorem tailTrace_7437654 : CollatzResearch.WordTrace tailWord_7437654 prefixEnd_7437654 3819091443835548378219859 := by
  unfold tailWord_7437654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954595462291080188658001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180849018264438188679018677 16954595462291080188658001)
  ·
    refine ⟨12715946596718310141493501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16954595462291080188658001 12715946596718310141493501)
    ·
      refine ⟨4768479973769366303060063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12715946596718310141493501 4768479973769366303060063)
      ·
        refine ⟨7152719960654049454590095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768479973769366303060063 7152719960654049454590095)
        ·
          refine ⟨10729079940981074181885143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7152719960654049454590095 10729079940981074181885143)
          ·
            refine ⟨16093619911471611272827715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729079940981074181885143 16093619911471611272827715)
            ·
              refine ⟨24140429867207416909241573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093619911471611272827715 24140429867207416909241573)
              ·
                refine ⟨4526330600101390670482795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24140429867207416909241573 4526330600101390670482795)
                ·
                  refine ⟨6789495900152086005724193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526330600101390670482795 6789495900152086005724193)
                  ·
                    refine ⟨5092121925114064504293145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789495900152086005724193 5092121925114064504293145)
                    ·
                      refine ⟨3819091443835548378219859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092121925114064504293145 3819091443835548378219859)
                      ·
                        rfl

theorem cell23_7437654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7437654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437654 prefixEnd_7437654 := by exact prefixLift 7437654
  have htrace : WordTrace (prefixWord ++ tailWord_7437654) baseStart_7437654 baseEnd_7437654 := by
    simpa [prefixWord, tailWord_7437654, baseEnd_7437654] using wordTrace_append hprefix tailTrace_7437654
  have hstable : (prefixWord ++ tailWord_7437654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437654).length < 2 ^ (prefixWord ++ tailWord_7437654).sum := by decide
  have hdescent : baseEnd_7437654 < baseStart_7437654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437676 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 2, 2, 2]
def baseStart_7437676 : Nat := 118140960795 + 7437676 * 2 ^ 59
def prefixEnd_7437676 : Nat := 4983230072969 + 3 ^ 40 * 7437676 * 2
def baseEnd_7437676 : Nat := 3819102740409947292144757

theorem tailTrace_7437676 : CollatzResearch.WordTrace tailWord_7437676 prefixEnd_7437676 3819102740409947292144757 := by
  unfold tailWord_7437676
  simp only [CollatzResearch.WordTrace]
  refine ⟨135637164901288790387914441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180849553201718387183885921 135637164901288790387914441)
  ·
    refine ⟨101727873675966592790935831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135637164901288790387914441 101727873675966592790935831)
    ·
      refine ⟨152591810513949889186403747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101727873675966592790935831 152591810513949889186403747)
      ·
        refine ⟨228887715770924833779605621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152591810513949889186403747 228887715770924833779605621)
        ·
          refine ⟨21458223353524203166838027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228887715770924833779605621 21458223353524203166838027)
          ·
            refine ⟨32187335030286304750257041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21458223353524203166838027 32187335030286304750257041)
            ·
              refine ⟨24140501272714728562692781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32187335030286304750257041 24140501272714728562692781)
              ·
                refine ⟨9052687977268023211009793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24140501272714728562692781 9052687977268023211009793)
                ·
                  refine ⟨6789515982951017408257345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052687977268023211009793 6789515982951017408257345)
                  ·
                    refine ⟨5092136987213263056193009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789515982951017408257345 5092136987213263056193009)
                    ·
                      refine ⟨3819102740409947292144757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092136987213263056193009 3819102740409947292144757)
                      ·
                        rfl

theorem cell23_7437676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_7437676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437676 prefixEnd_7437676 := by exact prefixLift 7437676
  have htrace : WordTrace (prefixWord ++ tailWord_7437676) baseStart_7437676 baseEnd_7437676 := by
    simpa [prefixWord, tailWord_7437676, baseEnd_7437676] using wordTrace_append hprefix tailTrace_7437676
  have hstable : (prefixWord ++ tailWord_7437676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437676).length < 2 ^ (prefixWord ++ tailWord_7437676).sum := by decide
  have hdescent : baseEnd_7437676 < baseStart_7437676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437699 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 5]
def baseStart_7437699 : Nat := 118140960795 + 7437699 * 2 ^ 59
def prefixEnd_7437699 : Nat := 4983230072969 + 3 ^ 40 * 7437699 * 2
def baseEnd_7437699 : Nat := 424346061162777855795239

theorem tailTrace_7437699 : CollatzResearch.WordTrace tailWord_7437699 prefixEnd_7437699 424346061162777855795239 := by
  unfold tailWord_7437699
  simp only [CollatzResearch.WordTrace]
  refine ⟨271275168681494255703916151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180850112454329503802610767 271275168681494255703916151)
  ·
    refine ⟨406912753022241383555874227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271275168681494255703916151 406912753022241383555874227)
    ·
      refine ⟨610369129533362075333811341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406912753022241383555874227 610369129533362075333811341)
      ·
        refine ⟨228888423575010778250179253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610369129533362075333811341 228888423575010778250179253)
        ·
          refine ⟨21458289710157260460954305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228888423575010778250179253 21458289710157260460954305)
          ·
            refine ⟨16093717282617945345715729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21458289710157260460954305 16093717282617945345715729)
            ·
              refine ⟨12070287961963459009286797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16093717282617945345715729 12070287961963459009286797)
              ·
                refine ⟨4526357985736297128482549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12070287961963459009286797 4526357985736297128482549)
                ·
                  refine ⟨424346061162777855795239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4526357985736297128482549 424346061162777855795239)
                  ·
                    rfl

theorem cell23_7437699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 5].length) (baseStart_7437699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437699 prefixEnd_7437699 := by exact prefixLift 7437699
  have htrace : WordTrace (prefixWord ++ tailWord_7437699) baseStart_7437699 baseEnd_7437699 := by
    simpa [prefixWord, tailWord_7437699, baseEnd_7437699] using wordTrace_append hprefix tailTrace_7437699
  have hstable : (prefixWord ++ tailWord_7437699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437699).length < 2 ^ (prefixWord ++ tailWord_7437699).sum := by decide
  have hdescent : baseEnd_7437699 < baseStart_7437699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437710 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7437710 : Nat := 118140960795 + 7437710 * 2 ^ 59
def prefixEnd_7437710 : Nat := 4983230072969 + 3 ^ 40 * 7437710 * 2
def baseEnd_7437710 : Nat := 3819120198752200159119601

theorem tailTrace_7437710 : CollatzResearch.WordTrace tailWord_7437710 prefixEnd_7437710 3819120198752200159119601 := by
  unfold tailWord_7437710
  simp only [CollatzResearch.WordTrace]
  refine ⟨33909446235556800572820823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180850379922969603055044389 33909446235556800572820823)
  ·
    refine ⟨50864169353335200859231235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33909446235556800572820823 50864169353335200859231235)
    ·
      refine ⟨76296254030002801288846853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50864169353335200859231235 76296254030002801288846853)
      ·
        refine ⟨14305547630625525241658785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76296254030002801288846853 14305547630625525241658785)
        ·
          refine ⟨10729160722969143931244089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14305547630625525241658785 10729160722969143931244089)
          ·
            refine ⟨8046870542226857948433067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10729160722969143931244089 8046870542226857948433067)
            ·
              refine ⟨12070305813340286922649601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8046870542226857948433067 12070305813340286922649601)
              ·
                refine ⟨9052729360005215191987201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12070305813340286922649601 9052729360005215191987201)
                ·
                  refine ⟨6789547020003911393990401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9052729360005215191987201 6789547020003911393990401)
                  ·
                    refine ⟨5092160265002933545492801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789547020003911393990401 5092160265002933545492801)
                    ·
                      refine ⟨3819120198752200159119601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092160265002933545492801 3819120198752200159119601)
                      ·
                        rfl

theorem cell23_7437710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7437710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437710 prefixEnd_7437710 := by exact prefixLift 7437710
  have htrace : WordTrace (prefixWord ++ tailWord_7437710) baseStart_7437710 baseEnd_7437710 := by
    simpa [prefixWord, tailWord_7437710, baseEnd_7437710] using wordTrace_append hprefix tailTrace_7437710
  have hstable : (prefixWord ++ tailWord_7437710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437710).length < 2 ^ (prefixWord ++ tailWord_7437710).sum := by decide
  have hdescent : baseEnd_7437710 < baseStart_7437710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437752 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_7437752 : Nat := 118140960795 + 7437752 * 2 ^ 59
def prefixEnd_7437752 : Nat := 4983230072969 + 3 ^ 40 * 7437752 * 2
def baseEnd_7437752 : Nat := 3819141764939688994794407

theorem tailTrace_7437752 : CollatzResearch.WordTrace tailWord_7437752 prefixEnd_7437752 3819141764939688994794407 := by
  unfold tailWord_7437752
  simp only [CollatzResearch.WordTrace]
  refine ⟨135638550875151122877797755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180851401166868163837063673 135638550875151122877797755)
  ·
    refine ⟨203457826312726684316696633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135638550875151122877797755 203457826312726684316696633)
    ·
      refine ⟨152593369734545013237522475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203457826312726684316696633 152593369734545013237522475)
      ·
        refine ⟨228890054601817519856283713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152593369734545013237522475 228890054601817519856283713)
        ·
          refine ⟨171667540951363139892212785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228890054601817519856283713 171667540951363139892212785)
          ·
            refine ⟨128750655713522354919159589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171667540951363139892212785 128750655713522354919159589)
            ·
              refine ⟨24140747946285441547342423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128750655713522354919159589 24140747946285441547342423)
              ·
                refine ⟨36211121919428162321013635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24140747946285441547342423 36211121919428162321013635)
                ·
                  refine ⟨54316682879142243481520453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36211121919428162321013635 54316682879142243481520453)
                  ·
                    refine ⟨10184378039839170652785085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54316682879142243481520453 10184378039839170652785085)
                    ·
                      refine ⟨3819141764939688994794407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10184378039839170652785085 3819141764939688994794407)
                      ·
                        rfl

theorem cell23_7437752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_7437752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437752 prefixEnd_7437752 := by exact prefixLift 7437752
  have htrace : WordTrace (prefixWord ++ tailWord_7437752) baseStart_7437752 baseEnd_7437752 := by
    simpa [prefixWord, tailWord_7437752, baseEnd_7437752] using wordTrace_append hprefix tailTrace_7437752
  have hstable : (prefixWord ++ tailWord_7437752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437752).length < 2 ^ (prefixWord ++ tailWord_7437752).sum := by decide
  have hdescent : baseEnd_7437752 < baseStart_7437752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437772 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 8]
def baseStart_7437772 : Nat := 118140960795 + 7437772 * 2 ^ 59
def prefixEnd_7437772 : Nat := 4983230072969 + 3 ^ 40 * 7437772 * 2
def baseEnd_7437772 : Nat := 424350226061419879616035

theorem tailTrace_7437772 : CollatzResearch.WordTrace tailWord_7437772 prefixEnd_7437772 424350226061419879616035 := by
  unfold tailWord_7437772
  simp only [CollatzResearch.WordTrace]
  refine ⟨135638915605114894585661785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180851887473486526114215713 135638915605114894585661785)
  ·
    refine ⟨101729186703836170939246339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135638915605114894585661785 101729186703836170939246339)
    ·
      refine ⟨152593780055754256408869509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101729186703836170939246339 152593780055754256408869509)
      ·
        refine ⟨28611333760453923076663033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152593780055754256408869509 28611333760453923076663033)
        ·
          refine ⟨21458500320340442307497275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28611333760453923076663033 21458500320340442307497275)
          ·
            refine ⟨32187750480510663461245913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21458500320340442307497275 32187750480510663461245913)
            ·
              refine ⟨24140812860382997595934435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32187750480510663461245913 24140812860382997595934435)
              ·
                refine ⟨36211219290574496393901653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24140812860382997595934435 36211219290574496393901653)
                ·
                  refine ⟨424350226061419879616035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36211219290574496393901653 424350226061419879616035)
                  ·
                    rfl

theorem cell23_7437772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_7437772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437772 prefixEnd_7437772 := by exact prefixLift 7437772
  have htrace : WordTrace (prefixWord ++ tailWord_7437772) baseStart_7437772 baseEnd_7437772 := by
    simpa [prefixWord, tailWord_7437772, baseEnd_7437772] using wordTrace_append hprefix tailTrace_7437772
  have hstable : (prefixWord ++ tailWord_7437772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437772).length < 2 ^ (prefixWord ++ tailWord_7437772).sum := by decide
  have hdescent : baseEnd_7437772 < baseStart_7437772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437775 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_7437775 : Nat := 118140960795 + 7437775 * 2 ^ 59
def prefixEnd_7437775 : Nat := 4983230072969 + 3 ^ 40 * 7437775 * 2
def baseEnd_7437775 : Nat := 3819153574994742404806801

theorem tailTrace_7437775 : CollatzResearch.WordTrace tailWord_7437775 prefixEnd_7437775 3819153574994742404806801 := by
  unfold tailWord_7437775
  simp only [CollatzResearch.WordTrace]
  refine ⟨271277940629218920683682779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180851960419479280455788519 271277940629218920683682779)
  ·
    refine ⟨406916910943828381025524169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271277940629218920683682779 406916910943828381025524169)
    ·
      refine ⟨305187683207871285769143127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406916910943828381025524169 305187683207871285769143127)
      ·
        refine ⟨457781524811806928653714691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305187683207871285769143127 457781524811806928653714691)
        ·
          refine ⟨686672287217710392980572037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457781524811806928653714691 686672287217710392980572037)
          ·
            refine ⟨128751053853320698683857257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 686672287217710392980572037 128751053853320698683857257)
            ·
              refine ⟨96563290389990524012892943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128751053853320698683857257 96563290389990524012892943)
              ·
                refine ⟨144844935584985786019339415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96563290389990524012892943 144844935584985786019339415)
                ·
                  refine ⟨217267403377478679029009123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144844935584985786019339415 217267403377478679029009123)
                  ·
                    refine ⟨325901105066218018543513685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 217267403377478679029009123 325901105066218018543513685)
                    ·
                      refine ⟨3819153574994742404806801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 325901105066218018543513685 3819153574994742404806801)
                      ·
                        rfl

theorem cell23_7437775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_7437775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437775 prefixEnd_7437775 := by exact prefixLift 7437775
  have htrace : WordTrace (prefixWord ++ tailWord_7437775) baseStart_7437775 baseEnd_7437775 := by
    simpa [prefixWord, tailWord_7437775, baseEnd_7437775] using wordTrace_append hprefix tailTrace_7437775
  have hstable : (prefixWord ++ tailWord_7437775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437775).length < 2 ^ (prefixWord ++ tailWord_7437775).sum := by decide
  have hdescent : baseEnd_7437775 < baseStart_7437775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437789 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 6]
def baseStart_7437789 : Nat := 118140960795 + 7437789 * 2 ^ 59
def prefixEnd_7437789 : Nat := 4983230072969 + 3 ^ 40 * 7437789 * 2
def baseEnd_7437789 : Nat := 424351195969322816670193

theorem tailTrace_7437789 : CollatzResearch.WordTrace tailWord_7437789 prefixEnd_7437789 424351195969322816670193 := by
  unfold tailWord_7437789
  simp only [CollatzResearch.WordTrace]
  refine ⟨271278451251168201074692421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180852300834112134049794947 271278451251168201074692421)
  ·
    refine ⟨50864709609594037701504829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271278451251168201074692421 50864709609594037701504829)
    ·
      refine ⟨19074266103597764138064311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50864709609594037701504829 19074266103597764138064311)
      ·
        refine ⟨28611399155396646207096467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19074266103597764138064311 28611399155396646207096467)
        ·
          refine ⟨42917098733094969310644701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28611399155396646207096467 42917098733094969310644701)
          ·
            refine ⟨16093912024910613491491763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42917098733094969310644701 16093912024910613491491763)
            ·
              refine ⟨24140868037365920237237645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093912024910613491491763 24140868037365920237237645)
              ·
                refine ⟨9052825514012220088964117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24140868037365920237237645 9052825514012220088964117)
                ·
                  refine ⟨424351195969322816670193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9052825514012220088964117 424351195969322816670193)
                  ·
                    rfl

theorem cell23_7437789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_7437789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437789 prefixEnd_7437789 := by exact prefixLift 7437789
  have htrace : WordTrace (prefixWord ++ tailWord_7437789) baseStart_7437789 baseEnd_7437789 := by
    simpa [prefixWord, tailWord_7437789, baseEnd_7437789] using wordTrace_append hprefix tailTrace_7437789
  have hstable : (prefixWord ++ tailWord_7437789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437789).length < 2 ^ (prefixWord ++ tailWord_7437789).sum := by decide
  have hdescent : baseEnd_7437789 < baseStart_7437789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437854 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7437854 : Nat := 118140960795 + 7437854 * 2 ^ 59
def prefixEnd_7437854 : Nat := 4983230072969 + 3 ^ 40 * 7437854 * 2
def baseEnd_7437854 : Nat := 3819194139966447595718939

theorem tailTrace_7437854 : CollatzResearch.WordTrace tailWord_7437854 prefixEnd_7437854 3819194139966447595718939 := by
  unfold tailWord_7437854
  simp only [CollatzResearch.WordTrace]
  refine ⟨33910102749491589646976077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180853881330621811450539077 33910102749491589646976077)
  ·
    refine ⟨12716288531059346117616029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33910102749491589646976077 12716288531059346117616029)
    ·
      refine ⟨4768608199147254794106011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12716288531059346117616029 4768608199147254794106011)
      ·
        refine ⟨7152912298720882191159017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768608199147254794106011 7152912298720882191159017)
        ·
          refine ⟨5364684224040661643369263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7152912298720882191159017 5364684224040661643369263)
          ·
            refine ⟨8047026336060992465053895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5364684224040661643369263 8047026336060992465053895)
            ·
              refine ⟨12070539504091488697580843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8047026336060992465053895 12070539504091488697580843)
              ·
                refine ⟨18105809256137233046371265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12070539504091488697580843 18105809256137233046371265)
                ·
                  refine ⟨13579356942102924784778449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18105809256137233046371265 13579356942102924784778449)
                  ·
                    refine ⟨10184517706577193588583837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13579356942102924784778449 10184517706577193588583837)
                    ·
                      refine ⟨3819194139966447595718939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10184517706577193588583837 3819194139966447595718939)
                      ·
                        rfl

theorem cell23_7437854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7437854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437854 prefixEnd_7437854 := by exact prefixLift 7437854
  have htrace : WordTrace (prefixWord ++ tailWord_7437854) baseStart_7437854 baseEnd_7437854 := by
    simpa [prefixWord, tailWord_7437854, baseEnd_7437854] using wordTrace_append hprefix tailTrace_7437854
  have hstable : (prefixWord ++ tailWord_7437854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437854).length < 2 ^ (prefixWord ++ tailWord_7437854).sum := by decide
  have hdescent : baseEnd_7437854 < baseStart_7437854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437906 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_7437906 : Nat := 118140960795 + 7437906 * 2 ^ 59
def prefixEnd_7437906 : Nat := 4983230072969 + 3 ^ 40 * 7437906 * 2
def baseEnd_7437906 : Nat := 3819220840960481392268699

theorem tailTrace_7437906 : CollatzResearch.WordTrace tailWord_7437906 prefixEnd_7437906 3819220840960481392268699 := by
  unfold tailWord_7437906
  simp only [CollatzResearch.WordTrace]
  refine ⟨67820679647936082514175393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180855145727829553371134381 67820679647936082514175393)
  ·
    refine ⟨50865509735952061885631545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67820679647936082514175393 50865509735952061885631545)
    ·
      refine ⟨38149132301964046414223659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50865509735952061885631545 38149132301964046414223659)
      ·
        refine ⟨57223698452946069621335489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38149132301964046414223659 57223698452946069621335489)
        ·
          refine ⟨42917773839709552216001617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57223698452946069621335489 42917773839709552216001617)
          ·
            refine ⟨32188330379782164162001213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42917773839709552216001617 32188330379782164162001213)
            ·
              refine ⟨12070623892418311560750455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32188330379782164162001213 12070623892418311560750455)
              ·
                refine ⟨18105935838627467341125683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12070623892418311560750455 18105935838627467341125683)
                ·
                  refine ⟨27158903757941201011688525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18105935838627467341125683 27158903757941201011688525)
                  ·
                    refine ⟨10184588909227950379383197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27158903757941201011688525 10184588909227950379383197)
                    ·
                      refine ⟨3819220840960481392268699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10184588909227950379383197 3819220840960481392268699)
                      ·
                        rfl

theorem cell23_7437906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_7437906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437906 prefixEnd_7437906 := by exact prefixLift 7437906
  have htrace : WordTrace (prefixWord ++ tailWord_7437906) baseStart_7437906 baseEnd_7437906 := by
    simpa [prefixWord, tailWord_7437906, baseEnd_7437906] using wordTrace_append hprefix tailTrace_7437906
  have hstable : (prefixWord ++ tailWord_7437906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437906).length < 2 ^ (prefixWord ++ tailWord_7437906).sum := by decide
  have hdescent : baseEnd_7437906 < baseStart_7437906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437963 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 2, 2, 2]
def baseStart_7437963 : Nat := 118140960795 + 7437963 * 2 ^ 59
def prefixEnd_7437963 : Nat := 4983230072969 + 3 ^ 40 * 7437963 * 2
def baseEnd_7437963 : Nat := 3819250109357787669255937

theorem tailTrace_7437963 : CollatzResearch.WordTrace tailWord_7437963 prefixEnd_7437963 3819250109357787669255937 := by
  unfold tailWord_7437963
  simp only [CollatzResearch.WordTrace]
  refine ⟨271284797552537828791526543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180856531701691885861017695 271284797552537828791526543)
  ·
    refine ⟨406927196328806743187289815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271284797552537828791526543 406927196328806743187289815)
    ·
      refine ⟨610390794493210114780934723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406927196328806743187289815 610390794493210114780934723)
      ·
        refine ⟨915586191739815172171402085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610390794493210114780934723 915586191739815172171402085)
        ·
          refine ⟨171672410951215344782137891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 915586191739815172171402085 171672410951215344782137891)
          ·
            refine ⟨257508616426823017173206837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171672410951215344782137891 257508616426823017173206837)
            ·
              refine ⟨24141432790014657859988141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257508616426823017173206837 24141432790014657859988141)
              ·
                refine ⟨9053037296255496697495553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24141432790014657859988141 9053037296255496697495553)
                ·
                  refine ⟨6789777972191622523121665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053037296255496697495553 6789777972191622523121665)
                  ·
                    refine ⟨5092333479143716892341249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789777972191622523121665 5092333479143716892341249)
                    ·
                      refine ⟨3819250109357787669255937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092333479143716892341249 3819250109357787669255937)
                      ·
                        rfl

theorem cell23_7437963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 2, 2].length) (baseStart_7437963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437963 prefixEnd_7437963 := by exact prefixLift 7437963
  have htrace : WordTrace (prefixWord ++ tailWord_7437963) baseStart_7437963 baseEnd_7437963 := by
    simpa [prefixWord, tailWord_7437963, baseEnd_7437963] using wordTrace_append hprefix tailTrace_7437963
  have hstable : (prefixWord ++ tailWord_7437963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437963).length < 2 ^ (prefixWord ++ tailWord_7437963).sum := by decide
  have hdescent : baseEnd_7437963 < baseStart_7437963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7437999 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 2, 5]
def baseStart_7437999 : Nat := 118140960795 + 7437999 * 2 ^ 59
def prefixEnd_7437999 : Nat := 4983230072969 + 3 ^ 40 * 7437999 * 2
def baseEnd_7437999 : Nat := 1273089531553783176135257

theorem tailTrace_7437999 : CollatzResearch.WordTrace tailWord_7437999 prefixEnd_7437999 1273089531553783176135257 := by
  unfold tailWord_7437999
  simp only [CollatzResearch.WordTrace]
  refine ⟨271286110580407406939837051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180857407053604937959891367 271286110580407406939837051)
  ·
    refine ⟨406929165870611110409755577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271286110580407406939837051 406929165870611110409755577)
    ·
      refine ⟨305196874402958332807316683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406929165870611110409755577 305196874402958332807316683)
      ·
        refine ⟨457795311604437499210975025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305196874402958332807316683 457795311604437499210975025)
        ·
          refine ⟨343346483703328124408231269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457795311604437499210975025 343346483703328124408231269)
          ·
            refine ⟨64377465694374023326543363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343346483703328124408231269 64377465694374023326543363)
            ·
              refine ⟨96566198541561034989815045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64377465694374023326543363 96566198541561034989815045)
              ·
                refine ⟨18106162226542694060590321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96566198541561034989815045 18106162226542694060590321)
                ·
                  refine ⟨13579621669907020545442741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18106162226542694060590321 13579621669907020545442741)
                  ·
                    refine ⟨1273089531553783176135257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13579621669907020545442741 1273089531553783176135257)
                    ·
                      rfl

theorem cell23_7437999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_7437999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7437999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7437999 prefixEnd_7437999 := by exact prefixLift 7437999
  have htrace : WordTrace (prefixWord ++ tailWord_7437999) baseStart_7437999 baseEnd_7437999 := by
    simpa [prefixWord, tailWord_7437999, baseEnd_7437999] using wordTrace_append hprefix tailTrace_7437999
  have hstable : (prefixWord ++ tailWord_7437999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7437999).length < 2 ^ (prefixWord ++ tailWord_7437999).sum := by decide
  have hdescent : baseEnd_7437999 < baseStart_7437999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7437999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438009 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7438009 : Nat := 118140960795 + 7438009 * 2 ^ 59
def prefixEnd_7438009 : Nat := 4983230072969 + 3 ^ 40 * 7438009 * 2
def baseEnd_7438009 : Nat := 3819273729467894489280725

theorem tailTrace_7438009 : CollatzResearch.WordTrace tailWord_7438009 prefixEnd_7438009 3819273729467894489280725 := by
  unfold tailWord_7438009
  simp only [CollatzResearch.WordTrace]
  refine ⟨271286475310371178647701081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180857650206914119098467387 271286475310371178647701081)
  ·
    refine ⟨203464856482778383985775811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271286475310371178647701081 203464856482778383985775811)
    ·
      refine ⟨305197284724167575978663717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203464856482778383985775811 305197284724167575978663717)
      ·
        refine ⟨57224490885781420495999447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305197284724167575978663717 57224490885781420495999447)
        ·
          refine ⟨85836736328672130743999171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57224490885781420495999447 85836736328672130743999171)
          ·
            refine ⟨128755104493008196115998757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85836736328672130743999171 128755104493008196115998757)
            ·
              refine ⟨24141582092439036771749767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128755104493008196115998757 24141582092439036771749767)
              ·
                refine ⟨36212373138658555157624651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24141582092439036771749767 36212373138658555157624651)
                ·
                  refine ⟨54318559707987832736436977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36212373138658555157624651 54318559707987832736436977)
                  ·
                    refine ⟨40738919780990874552327733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54318559707987832736436977 40738919780990874552327733)
                    ·
                      refine ⟨3819273729467894489280725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40738919780990874552327733 3819273729467894489280725)
                      ·
                        rfl

theorem cell23_7438009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7438009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438009 prefixEnd_7438009 := by exact prefixLift 7438009
  have htrace : WordTrace (prefixWord ++ tailWord_7438009) baseStart_7438009 baseEnd_7438009 := by
    simpa [prefixWord, tailWord_7438009, baseEnd_7438009] using wordTrace_append hprefix tailTrace_7438009
  have hstable : (prefixWord ++ tailWord_7438009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438009).length < 2 ^ (prefixWord ++ tailWord_7438009).sum := by decide
  have hdescent : baseEnd_7438009 < baseStart_7438009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438063 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 1, 4]
def baseStart_7438063 : Nat := 118140960795 + 7438063 * 2 ^ 59
def prefixEnd_7438063 : Nat := 4983230072969 + 3 ^ 40 * 7438063 * 2
def baseEnd_7438063 : Nat := 1273100485807745759335159

theorem tailTrace_7438063 : CollatzResearch.WordTrace tailWord_7438063 prefixEnd_7438063 1273100485807745759335159 := by
  unfold tailWord_7438063
  simp only [CollatzResearch.WordTrace]
  refine ⟨271288444852175545870166843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180858963234783697246777895 271288444852175545870166843)
  ·
    refine ⟨406932667278263318805250265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271288444852175545870166843 406932667278263318805250265)
    ·
      refine ⟨305199500458697489103937699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406932667278263318805250265 305199500458697489103937699)
      ·
        refine ⟨457799250688046233655906549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305199500458697489103937699 457799250688046233655906549)
        ·
          refine ⟨42918679752004334405241239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457799250688046233655906549 42918679752004334405241239)
          ·
            refine ⟨64378019628006501607861859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42918679752004334405241239 64378019628006501607861859)
            ·
              refine ⟨96567029442009752411792789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64378019628006501607861859 96567029442009752411792789)
              ·
                refine ⟨4526579505094207144302787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96567029442009752411792789 4526579505094207144302787)
                ·
                  refine ⟨6789869257641310716454181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526579505094207144302787 6789869257641310716454181)
                  ·
                    refine ⟨1273100485807745759335159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6789869257641310716454181 1273100485807745759335159)
                    ·
                      rfl

theorem cell23_7438063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 4].length) (baseStart_7438063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438063 prefixEnd_7438063 := by exact prefixLift 7438063
  have htrace : WordTrace (prefixWord ++ tailWord_7438063) baseStart_7438063 baseEnd_7438063 := by
    simpa [prefixWord, tailWord_7438063, baseEnd_7438063] using wordTrace_append hprefix tailTrace_7438063
  have hstable : (prefixWord ++ tailWord_7438063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438063).length < 2 ^ (prefixWord ++ tailWord_7438063).sum := by decide
  have hdescent : baseEnd_7438063 < baseStart_7438063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438113 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 4, 3, 2]
def baseStart_7438113 : Nat := 118140960795 + 7438113 * 2 ^ 59
def prefixEnd_7438113 : Nat := 4983230072969 + 3 ^ 40 * 7438113 * 2
def baseEnd_7438113 : Nat := 3819327131455962082380247

theorem tailTrace_7438113 : CollatzResearch.WordTrace tailWord_7438113 prefixEnd_7438113 3819327131455962082380247 := by
  unfold tailWord_7438113
  simp only [CollatzResearch.WordTrace]
  refine ⟨271290268501994404409486993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180860179001329602939657995 271290268501994404409486993)
  ·
    refine ⟨203467701376495803307115245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271290268501994404409486993 203467701376495803307115245)
    ·
      refine ⟨76300388016185926240168217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203467701376495803307115245 76300388016185926240168217)
      ·
        refine ⟨57225291012139444680126163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76300388016185926240168217 57225291012139444680126163)
        ·
          refine ⟨85837936518209167020189245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57225291012139444680126163 85837936518209167020189245)
          ·
            refine ⟨32189226194328437632570967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85837936518209167020189245 32189226194328437632570967)
            ·
              refine ⟨48283839291492656448856451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32189226194328437632570967 48283839291492656448856451)
              ·
                refine ⟨72425758937238984673284677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48283839291492656448856451 72425758937238984673284677)
                ·
                  refine ⟨13579829800732309626240877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72425758937238984673284677 13579829800732309626240877)
                  ·
                    refine ⟨5092436175274616109840329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13579829800732309626240877 5092436175274616109840329)
                    ·
                      refine ⟨3819327131455962082380247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092436175274616109840329 3819327131455962082380247)
                      ·
                        rfl

theorem cell23_7438113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_7438113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438113 prefixEnd_7438113 := by exact prefixLift 7438113
  have htrace : WordTrace (prefixWord ++ tailWord_7438113) baseStart_7438113 baseEnd_7438113 := by
    simpa [prefixWord, tailWord_7438113, baseEnd_7438113] using wordTrace_append hprefix tailTrace_7438113
  have hstable : (prefixWord ++ tailWord_7438113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438113).length < 2 ^ (prefixWord ++ tailWord_7438113).sum := by decide
  have hdescent : baseEnd_7438113 < baseStart_7438113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438120 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_7438120 : Nat := 118140960795 + 7438120 * 2 ^ 59
def prefixEnd_7438120 : Nat := 4983230072969 + 3 ^ 40 * 7438120 * 2
def baseEnd_7438120 : Nat := 3819330725820543554992715

theorem tailTrace_7438120 : CollatzResearch.WordTrace tailWord_7438120 prefixEnd_7438120 3819330725820543554992715 := by
  unfold tailWord_7438120
  simp only [CollatzResearch.WordTrace]
  refine ⟨135645261906484522302495907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180860349208646029736661209 135645261906484522302495907)
  ·
    refine ⟨203467892859726783453743861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135645261906484522302495907 203467892859726783453743861)
    ·
      refine ⟨19075114955599385948788487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203467892859726783453743861 19075114955599385948788487)
      ·
        refine ⟨28612672433399078923182731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19075114955599385948788487 28612672433399078923182731)
        ·
          refine ⟨42919008650098618384774097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28612672433399078923182731 42919008650098618384774097)
          ·
            refine ⟨32189256487573963788580573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42919008650098618384774097 32189256487573963788580573)
            ·
              refine ⟨12070971182840236420717715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32189256487573963788580573 12070971182840236420717715)
              ·
                refine ⟨18106456774260354631076573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12070971182840236420717715 18106456774260354631076573)
                ·
                  refine ⟨6789921290347632986653715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18106456774260354631076573 6789921290347632986653715)
                  ·
                    refine ⟨10184881935521449479980573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6789921290347632986653715 10184881935521449479980573)
                    ·
                      refine ⟨3819330725820543554992715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10184881935521449479980573 3819330725820543554992715)
                      ·
                        rfl

theorem cell23_7438120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_7438120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438120 prefixEnd_7438120 := by exact prefixLift 7438120
  have htrace : WordTrace (prefixWord ++ tailWord_7438120) baseStart_7438120 baseEnd_7438120 := by
    simpa [prefixWord, tailWord_7438120, baseEnd_7438120] using wordTrace_append hprefix tailTrace_7438120
  have hstable : (prefixWord ++ tailWord_7438120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438120).length < 2 ^ (prefixWord ++ tailWord_7438120).sum := by decide
  have hdescent : baseEnd_7438120 < baseStart_7438120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438143 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_7438143 : Nat := 118140960795 + 7438143 * 2 ^ 59
def prefixEnd_7438143 : Nat := 4983230072969 + 3 ^ 40 * 7438143 * 2
def baseEnd_7438143 : Nat := 3819342535875596965005109

theorem tailTrace_7438143 : CollatzResearch.WordTrace tailWord_7438143 prefixEnd_7438143 3819342535875596965005109 := by
  unfold tailWord_7438143
  simp only [CollatzResearch.WordTrace]
  refine ⟨271291362691885719533079083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180860908461257146355386055 271291362691885719533079083)
  ·
    refine ⟨406937044037828579299618625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271291362691885719533079083 406937044037828579299618625)
    ·
      refine ⟨305202783028371434474713969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406937044037828579299618625 305202783028371434474713969)
      ·
        refine ⟨228902087271278575856035477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305202783028371434474713969 228902087271278575856035477)
        ·
          refine ⟨10729785340841183243251663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228902087271278575856035477 10729785340841183243251663)
          ·
            refine ⟨16094678011261774864877495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729785340841183243251663 16094678011261774864877495)
            ·
              refine ⟨24142017016892662297316243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16094678011261774864877495 24142017016892662297316243)
              ·
                refine ⟨36213025525338993445974365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24142017016892662297316243 36213025525338993445974365)
                ·
                  refine ⟨13579884572002122542240387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36213025525338993445974365 13579884572002122542240387)
                  ·
                    refine ⟨20369826858003183813360581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13579884572002122542240387 20369826858003183813360581)
                    ·
                      refine ⟨3819342535875596965005109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20369826858003183813360581 3819342535875596965005109)
                      ·
                        rfl

theorem cell23_7438143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_7438143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438143 prefixEnd_7438143 := by exact prefixLift 7438143
  have htrace : WordTrace (prefixWord ++ tailWord_7438143) baseStart_7438143 baseEnd_7438143 := by
    simpa [prefixWord, tailWord_7438143, baseEnd_7438143] using wordTrace_append hprefix tailTrace_7438143
  have hstable : (prefixWord ++ tailWord_7438143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438143).length < 2 ^ (prefixWord ++ tailWord_7438143).sum := by decide
  have hdescent : baseEnd_7438143 < baseStart_7438143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438149 : List Nat := [1, 3, 1, 1, 1, 2, 3, 11]
def baseStart_7438149 : Nat := 118140960795 + 7438149 * 2 ^ 59
def prefixEnd_7438149 : Nat := 4983230072969 + 3 ^ 40 * 7438149 * 2
def baseEnd_7438149 : Nat := 141457245065167553390003

theorem tailTrace_7438149 : CollatzResearch.WordTrace tailWord_7438149 prefixEnd_7438149 141457245065167553390003 := by
  unfold tailWord_7438149
  simp only [CollatzResearch.WordTrace]
  refine ⟨271291581529863982557797501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180861054353242655038531667 271291581529863982557797501)
  ·
    refine ⟨101734343073698993459174063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271291581529863982557797501 101734343073698993459174063)
    ·
      refine ⟨152601514610548490188761095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101734343073698993459174063 152601514610548490188761095)
      ·
        refine ⟨228902271915822735283141643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152601514610548490188761095 228902271915822735283141643)
        ·
          refine ⟨343353407873734102924712465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228902271915822735283141643 343353407873734102924712465)
          ·
            refine ⟨257515055905300577193534349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343353407873734102924712465 257515055905300577193534349)
            ·
              refine ⟨96568145964487716447575381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257515055905300577193534349 96568145964487716447575381)
              ·
                refine ⟨141457245065167553390003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 96568145964487716447575381 141457245065167553390003)
                ·
                  rfl

theorem cell23_7438149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 11].length) (baseStart_7438149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438149 prefixEnd_7438149 := by exact prefixLift 7438149
  have htrace : WordTrace (prefixWord ++ tailWord_7438149) baseStart_7438149 baseEnd_7438149 := by
    simpa [prefixWord, tailWord_7438149, baseEnd_7438149] using wordTrace_append hprefix tailTrace_7438149
  have hstable : (prefixWord ++ tailWord_7438149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438149).length < 2 ^ (prefixWord ++ tailWord_7438149).sum := by decide
  have hdescent : baseEnd_7438149 < baseStart_7438149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438157 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_7438157 : Nat := 118140960795 + 7438157 * 2 ^ 59
def prefixEnd_7438157 : Nat := 4983230072969 + 3 ^ 40 * 7438157 * 2
def baseEnd_7438157 : Nat := 1273116574868253303410015

theorem tailTrace_7438157 : CollatzResearch.WordTrace tailWord_7438157 prefixEnd_7438157 1273116574868253303410015 := by
  unfold tailWord_7438157
  simp only [CollatzResearch.WordTrace]
  refine ⟨271291873313834999924088725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180861248875889999949392483 271291873313834999924088725)
  ·
    refine ⟨12716806561586015621441659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271291873313834999924088725 12716806561586015621441659)
    ·
      refine ⟨19075209842379023432162489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12716806561586015621441659 19075209842379023432162489)
      ·
        refine ⟨14306407381784267574121867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19075209842379023432162489 14306407381784267574121867)
        ·
          refine ⟨21459611072676401361182801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14306407381784267574121867 21459611072676401361182801)
          ·
            refine ⟨16094708304507301020887101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21459611072676401361182801 16094708304507301020887101)
            ·
              refine ⟨6035515614190237882832663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16094708304507301020887101 6035515614190237882832663)
              ·
                refine ⟨9053273421285356824248995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035515614190237882832663 9053273421285356824248995)
                ·
                  refine ⟨13579910131928035236373493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9053273421285356824248995 13579910131928035236373493)
                  ·
                    refine ⟨1273116574868253303410015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13579910131928035236373493 1273116574868253303410015)
                    ·
                      rfl

theorem cell23_7438157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_7438157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438157 prefixEnd_7438157 := by exact prefixLift 7438157
  have htrace : WordTrace (prefixWord ++ tailWord_7438157) baseStart_7438157 baseEnd_7438157 := by
    simpa [prefixWord, tailWord_7438157, baseEnd_7438157] using wordTrace_append hprefix tailTrace_7438157
  have hstable : (prefixWord ++ tailWord_7438157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438157).length < 2 ^ (prefixWord ++ tailWord_7438157).sum := by decide
  have hdescent : baseEnd_7438157 < baseStart_7438157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438177 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 1, 2, 2]
def baseStart_7438177 : Nat := 118140960795 + 7438177 * 2 ^ 59
def prefixEnd_7438177 : Nat := 4983230072969 + 3 ^ 40 * 7438177 * 2
def baseEnd_7438177 : Nat := 3819359994217849831979953

theorem tailTrace_7438177 : CollatzResearch.WordTrace tailWord_7438177 prefixEnd_7438177 3819359994217849831979953 := by
  unfold tailWord_7438177
  simp only [CollatzResearch.WordTrace]
  refine ⟨271292602773762543339816785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180861735182508362226544523 271292602773762543339816785)
  ·
    refine ⟨203469452080321907504862589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271292602773762543339816785 203469452080321907504862589)
    ·
      refine ⟨76301044530120715314323471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203469452080321907504862589 76301044530120715314323471)
      ·
        refine ⟨114451566795181072971485207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76301044530120715314323471 114451566795181072971485207)
        ·
          refine ⟨171677350192771609457227811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114451566795181072971485207 171677350192771609457227811)
          ·
            refine ⟨257516025289157414185841717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171677350192771609457227811 257516025289157414185841717)
            ·
              refine ⟨24142127370858507579922661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257516025289157414185841717 24142127370858507579922661)
              ·
                refine ⟨4526648882035970171235499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24142127370858507579922661 4526648882035970171235499)
                ·
                  refine ⟨6789973323053955256853249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526648882035970171235499 6789973323053955256853249)
                  ·
                    refine ⟨5092479992290466442639937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789973323053955256853249 5092479992290466442639937)
                    ·
                      refine ⟨3819359994217849831979953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092479992290466442639937 3819359994217849831979953)
                      ·
                        rfl

theorem cell23_7438177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_7438177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438177 prefixEnd_7438177 := by exact prefixLift 7438177
  have htrace : WordTrace (prefixWord ++ tailWord_7438177) baseStart_7438177 baseEnd_7438177 := by
    simpa [prefixWord, tailWord_7438177, baseEnd_7438177] using wordTrace_append hprefix tailTrace_7438177
  have hstable : (prefixWord ++ tailWord_7438177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438177).length < 2 ^ (prefixWord ++ tailWord_7438177).sum := by decide
  have hdescent : baseEnd_7438177 < baseStart_7438177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438190 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_7438190 : Nat := 118140960795 + 7438190 * 2 ^ 59
def prefixEnd_7438190 : Nat := 4983230072969 + 3 ^ 40 * 7438190 * 2
def baseEnd_7438190 : Nat := 3819366669466358281117393

theorem tailTrace_7438190 : CollatzResearch.WordTrace tailWord_7438190 prefixEnd_7438190 3819366669466358281117393 := by
  unfold tailWord_7438190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33911634615339430820005003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180862051281810297706693349 33911634615339430820005003)
  ·
    refine ⟨50867451923009146230007505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33911634615339430820005003 50867451923009146230007505)
    ·
      refine ⟨38150588942256859672505629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50867451923009146230007505 38150588942256859672505629)
      ·
        refine ⟨14306470853346322377189611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38150588942256859672505629 14306470853346322377189611)
        ·
          refine ⟨21459706280019483565784417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14306470853346322377189611 21459706280019483565784417)
          ·
            refine ⟨16094779710014612674338313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21459706280019483565784417 16094779710014612674338313)
            ·
              refine ⟨12071084782510959505753735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16094779710014612674338313 12071084782510959505753735)
              ·
                refine ⟨18106627173766439258630603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12071084782510959505753735 18106627173766439258630603)
                ·
                  refine ⟨27159940760649658887945905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18106627173766439258630603 27159940760649658887945905)
                  ·
                    refine ⟨20369955570487244165959429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27159940760649658887945905 20369955570487244165959429)
                    ·
                      refine ⟨3819366669466358281117393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20369955570487244165959429 3819366669466358281117393)
                      ·
                        rfl

theorem cell23_7438190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_7438190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438190 prefixEnd_7438190 := by exact prefixLift 7438190
  have htrace : WordTrace (prefixWord ++ tailWord_7438190) baseStart_7438190 baseEnd_7438190 := by
    simpa [prefixWord, tailWord_7438190, baseEnd_7438190] using wordTrace_append hprefix tailTrace_7438190
  have hstable : (prefixWord ++ tailWord_7438190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438190).length < 2 ^ (prefixWord ++ tailWord_7438190).sum := by decide
  have hdescent : baseEnd_7438190 < baseStart_7438190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438193 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_7438193 : Nat := 118140960795 + 7438193 * 2 ^ 59
def prefixEnd_7438193 : Nat := 4983230072969 + 3 ^ 40 * 7438193 * 2
def baseEnd_7438193 : Nat := 3819368209908321769379879

theorem tailTrace_7438193 : CollatzResearch.WordTrace tailWord_7438193 prefixEnd_7438193 3819368209908321769379879 := by
  unfold tailWord_7438193
  simp only [CollatzResearch.WordTrace]
  refine ⟨271293186341704578072399233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180862124227803052048266155 271293186341704578072399233)
  ·
    refine ⟨203469889756278433554299425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271293186341704578072399233 203469889756278433554299425)
    ·
      refine ⟨152602417317208825165724569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203469889756278433554299425 152602417317208825165724569)
      ·
        refine ⟨114451812987906618874293427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152602417317208825165724569 114451812987906618874293427)
        ·
          refine ⟨171677719481859928311440141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114451812987906618874293427 171677719481859928311440141)
          ·
            refine ⟨64379144805697473116790053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171677719481859928311440141 64379144805697473116790053)
            ·
              refine ⟨12071089651068276209398135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64379144805697473116790053 12071089651068276209398135)
              ·
                refine ⟨18106634476602414314097203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12071089651068276209398135 18106634476602414314097203)
                ·
                  refine ⟨27159951714903621471145805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18106634476602414314097203 27159951714903621471145805)
                  ·
                    refine ⟨10184981893088858051679677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27159951714903621471145805 10184981893088858051679677)
                    ·
                      refine ⟨3819368209908321769379879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10184981893088858051679677 3819368209908321769379879)
                      ·
                        rfl

theorem cell23_7438193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_7438193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438193 prefixEnd_7438193 := by exact prefixLift 7438193
  have htrace : WordTrace (prefixWord ++ tailWord_7438193) baseStart_7438193 baseEnd_7438193 := by
    simpa [prefixWord, tailWord_7438193, baseEnd_7438193] using wordTrace_append hprefix tailTrace_7438193
  have hstable : (prefixWord ++ tailWord_7438193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438193).length < 2 ^ (prefixWord ++ tailWord_7438193).sum := by decide
  have hdescent : baseEnd_7438193 < baseStart_7438193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438233 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 3, 4, 2]
def baseStart_7438233 : Nat := 118140960795 + 7438233 * 2 ^ 59
def prefixEnd_7438233 : Nat := 4983230072969 + 3 ^ 40 * 7438233 * 2
def baseEnd_7438233 : Nat := 3819388749134501612879695

theorem tailTrace_7438233 : CollatzResearch.WordTrace tailWord_7438233 prefixEnd_7438233 3819388749134501612879695 := by
  unfold tailWord_7438233
  simp only [CollatzResearch.WordTrace]
  refine ⟨271294645261559664903855353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180863096841039776602570235 271294645261559664903855353)
  ·
    refine ⟨203470983946169748677891515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271294645261559664903855353 203470983946169748677891515)
    ·
      refine ⟨305206475919254623016837273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203470983946169748677891515 305206475919254623016837273)
      ·
        refine ⟨228904856939440967262627955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305206475919254623016837273 228904856939440967262627955)
        ·
          refine ⟨343357285409161450893941933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228904856939440967262627955 343357285409161450893941933)
          ·
            refine ⟨128758982028435544085228225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343357285409161450893941933 128758982028435544085228225)
            ·
              refine ⟨96569236521326658063921169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128758982028435544085228225 96569236521326658063921169)
              ·
                refine ⟨72426927390994993547940877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96569236521326658063921169 72426927390994993547940877)
                ·
                  refine ⟨27160097771623122580477829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72426927390994993547940877 27160097771623122580477829)
                  ·
                    refine ⟨5092518332179335483839593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27160097771623122580477829 5092518332179335483839593)
                    ·
                      refine ⟨3819388749134501612879695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092518332179335483839593 3819388749134501612879695)
                      ·
                        rfl

theorem cell23_7438233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_7438233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438233 prefixEnd_7438233 := by exact prefixLift 7438233
  have htrace : WordTrace (prefixWord ++ tailWord_7438233) baseStart_7438233 baseEnd_7438233 := by
    simpa [prefixWord, tailWord_7438233, baseEnd_7438233] using wordTrace_append hprefix tailTrace_7438233
  have hstable : (prefixWord ++ tailWord_7438233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438233).length < 2 ^ (prefixWord ++ tailWord_7438233).sum := by decide
  have hdescent : baseEnd_7438233 < baseStart_7438233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438316 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_7438316 : Nat := 118140960795 + 7438316 * 2 ^ 59
def prefixEnd_7438316 : Nat := 4983230072969 + 3 ^ 40 * 7438316 * 2
def baseEnd_7438316 : Nat := 1273143789342941596047271

theorem tailTrace_7438316 : CollatzResearch.WordTrace tailWord_7438316 prefixEnd_7438316 1273143789342941596047271 := by
  unfold tailWord_7438316
  simp only [CollatzResearch.WordTrace]
  refine ⟨135648836260129485039563401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180865115013505980052751201 135648836260129485039563401)
  ·
    refine ⟨101736627195097113779672551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135648836260129485039563401 101736627195097113779672551)
    ·
      refine ⟨152604940792645670669508827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101736627195097113779672551 152604940792645670669508827)
      ·
        refine ⟨228907411188968506004263241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152604940792645670669508827 228907411188968506004263241)
        ·
          refine ⟨171680558391726379503197431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228907411188968506004263241 171680558391726379503197431)
          ·
            refine ⟨257520837587589569254796147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171680558391726379503197431 257520837587589569254796147)
            ·
              refine ⟨386281256381384353882194221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257520837587589569254796147 386281256381384353882194221)
              ·
                refine ⟨144855471143019132705822833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386281256381384353882194221 144855471143019132705822833)
                ·
                  refine ⟨108641603357264349529367125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144855471143019132705822833 108641603357264349529367125)
                  ·
                    refine ⟨1273143789342941596047271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108641603357264349529367125 1273143789342941596047271)
                    ·
                      rfl

theorem cell23_7438316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_7438316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438316 prefixEnd_7438316 := by exact prefixLift 7438316
  have htrace : WordTrace (prefixWord ++ tailWord_7438316) baseStart_7438316 baseEnd_7438316 := by
    simpa [prefixWord, tailWord_7438316, baseEnd_7438316] using wordTrace_append hprefix tailTrace_7438316
  have hstable : (prefixWord ++ tailWord_7438316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438316).length < 2 ^ (prefixWord ++ tailWord_7438316).sum := by decide
  have hdescent : baseEnd_7438316 < baseStart_7438316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438350 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_7438350 : Nat := 118140960795 + 7438350 * 2 ^ 59
def prefixEnd_7438350 : Nat := 4983230072969 + 3 ^ 40 * 7438350 * 2
def baseEnd_7438350 : Nat := 1273149608790359218372219

theorem tailTrace_7438350 : CollatzResearch.WordTrace tailWord_7438350 prefixEnd_7438350 1273149608790359218372219 := by
  unfold tailWord_7438350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33912364075266974235733063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180865941734757195923909669 33912364075266974235733063)
  ·
    refine ⟨50868546112900461353599595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33912364075266974235733063 50868546112900461353599595)
    ·
      refine ⟨76302819169350692030399393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50868546112900461353599595 76302819169350692030399393)
      ·
        refine ⟨57227114377013019022799545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76302819169350692030399393 57227114377013019022799545)
        ·
          refine ⟨42920335782759764267099659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57227114377013019022799545 42920335782759764267099659)
          ·
            refine ⟨64380503674139646400649489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42920335782759764267099659 64380503674139646400649489)
            ·
              refine ⟨48285377755604734800487117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64380503674139646400649489 48285377755604734800487117)
              ·
                refine ⟨18107016658351775550182669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48285377755604734800487117 18107016658351775550182669)
                ·
                  refine ⟨6790131246881915831318501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18107016658351775550182669 6790131246881915831318501)
                  ·
                    refine ⟨1273149608790359218372219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6790131246881915831318501 1273149608790359218372219)
                    ·
                      rfl

theorem cell23_7438350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_7438350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438350 prefixEnd_7438350 := by exact prefixLift 7438350
  have htrace : WordTrace (prefixWord ++ tailWord_7438350) baseStart_7438350 baseEnd_7438350 := by
    simpa [prefixWord, tailWord_7438350, baseEnd_7438350] using wordTrace_append hprefix tailTrace_7438350
  have hstable : (prefixWord ++ tailWord_7438350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438350).length < 2 ^ (prefixWord ++ tailWord_7438350).sum := by decide
  have hdescent : baseEnd_7438350 < baseStart_7438350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438357 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_7438357 : Nat := 118140960795 + 7438357 * 2 ^ 59
def prefixEnd_7438357 : Nat := 4983230072969 + 3 ^ 40 * 7438357 * 2
def baseEnd_7438357 : Nat := 3819452420735659127729125

theorem tailTrace_7438357 : CollatzResearch.WordTrace tailWord_7438357 prefixEnd_7438357 3819452420735659127729125 := by
  unfold tailWord_7438357
  simp only [CollatzResearch.WordTrace]
  refine ⟨271299167913110434081369325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180866111942073622720912883 271299167913110434081369325)
  ·
    refine ⟨101737187967416412780513497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271299167913110434081369325 101737187967416412780513497)
    ·
      refine ⟨76302890975562309585385123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101737187967416412780513497 76302890975562309585385123)
      ·
        refine ⟨114454336463343464378077685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76302890975562309585385123 114454336463343464378077685)
        ·
          refine ⟨10730094043438449785444783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114454336463343464378077685 10730094043438449785444783)
          ·
            refine ⟨16095141065157674678167175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730094043438449785444783 16095141065157674678167175)
            ·
              refine ⟨24142711597736512017250763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095141065157674678167175 24142711597736512017250763)
              ·
                refine ⟨36214067396604768025876145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24142711597736512017250763 36214067396604768025876145)
                ·
                  refine ⟨27160550547453576019407109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36214067396604768025876145 27160550547453576019407109)
                  ·
                    refine ⟨5092603227647545503638833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27160550547453576019407109 5092603227647545503638833)
                    ·
                      refine ⟨3819452420735659127729125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092603227647545503638833 3819452420735659127729125)
                      ·
                        rfl

theorem cell23_7438357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_7438357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438357 prefixEnd_7438357 := by exact prefixLift 7438357
  have htrace : WordTrace (prefixWord ++ tailWord_7438357) baseStart_7438357 baseEnd_7438357 := by
    simpa [prefixWord, tailWord_7438357, baseEnd_7438357] using wordTrace_append hprefix tailTrace_7438357
  have hstable : (prefixWord ++ tailWord_7438357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438357).length < 2 ^ (prefixWord ++ tailWord_7438357).sum := by decide
  have hdescent : baseEnd_7438357 < baseStart_7438357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438407 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_7438407 : Nat := 118140960795 + 7438407 * 2 ^ 59
def prefixEnd_7438407 : Nat := 4983230072969 + 3 ^ 40 * 7438407 * 2
def baseEnd_7438407 : Nat := 3819478094768383932103895

theorem tailTrace_7438407 : CollatzResearch.WordTrace tailWord_7438407 prefixEnd_7438407 3819478094768383932103895 := by
  unfold tailWord_7438407
  simp only [CollatzResearch.WordTrace]
  refine ⟨271300991562929292620689475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180867327708619528413792983 271300991562929292620689475)
  ·
    refine ⟨406951487344393938931034213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271300991562929292620689475 406951487344393938931034213)
    ·
      refine ⟨76303403877073863549568915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406951487344393938931034213 76303403877073863549568915)
      ·
        refine ⟨114455105815610795324353373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76303403877073863549568915 114455105815610795324353373)
        ·
          refine ⟨42920664680854048246632515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114455105815610795324353373 42920664680854048246632515)
          ·
            refine ⟨64380997021281072369948773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42920664680854048246632515 64380997021281072369948773)
            ·
              refine ⟨12071436941490201069365395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64380997021281072369948773 12071436941490201069365395)
              ·
                refine ⟨18107155412235301604048093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12071436941490201069365395 18107155412235301604048093)
                ·
                  refine ⟨6790183279588238101518035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18107155412235301604048093 6790183279588238101518035)
                  ·
                    refine ⟨10185274919382357152277053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6790183279588238101518035 10185274919382357152277053)
                    ·
                      refine ⟨3819478094768383932103895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10185274919382357152277053 3819478094768383932103895)
                      ·
                        rfl

theorem cell23_7438407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_7438407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438407 prefixEnd_7438407 := by exact prefixLift 7438407
  have htrace : WordTrace (prefixWord ++ tailWord_7438407) baseStart_7438407 baseEnd_7438407 := by
    simpa [prefixWord, tailWord_7438407, baseEnd_7438407] using wordTrace_append hprefix tailTrace_7438407
  have hstable : (prefixWord ++ tailWord_7438407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438407).length < 2 ^ (prefixWord ++ tailWord_7438407).sum := by decide
  have hdescent : baseEnd_7438407 < baseStart_7438407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438433 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_7438433 : Nat := 118140960795 + 7438433 * 2 ^ 59
def prefixEnd_7438433 : Nat := 4983230072969 + 3 ^ 40 * 7438433 * 2
def baseEnd_7438433 : Nat := 3819491445265400830378775

theorem tailTrace_7438433 : CollatzResearch.WordTrace tailWord_7438433 prefixEnd_7438433 3819491445265400830378775 := by
  unfold tailWord_7438433
  simp only [CollatzResearch.WordTrace]
  refine ⟨271301939860835099061135953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180867959907223399374090635 271301939860835099061135953)
  ·
    refine ⟨203476454895626324295851965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271301939860835099061135953 203476454895626324295851965)
    ·
      refine ⟨76303670585859871610944487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203476454895626324295851965 76303670585859871610944487)
      ·
        refine ⟨114455505878789807416416731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76303670585859871610944487 114455505878789807416416731)
        ·
          refine ⟨171683258818184711124625097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114455505878789807416416731 171683258818184711124625097)
          ·
            refine ⟨128762444113638533343468823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171683258818184711124625097 128762444113638533343468823)
            ·
              refine ⟨193143666170457800015203235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128762444113638533343468823 193143666170457800015203235)
              ·
                refine ⟨289715499255686700022804853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193143666170457800015203235 289715499255686700022804853)
                ·
                  refine ⟨27160828055220628127137955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289715499255686700022804853 27160828055220628127137955)
                  ·
                    refine ⟨40741242082830942190706933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27160828055220628127137955 40741242082830942190706933)
                    ·
                      refine ⟨3819491445265400830378775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40741242082830942190706933 3819491445265400830378775)
                      ·
                        rfl

theorem cell23_7438433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_7438433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438433 prefixEnd_7438433 := by exact prefixLift 7438433
  have htrace : WordTrace (prefixWord ++ tailWord_7438433) baseStart_7438433 baseEnd_7438433 := by
    simpa [prefixWord, tailWord_7438433, baseEnd_7438433] using wordTrace_append hprefix tailTrace_7438433
  have hstable : (prefixWord ++ tailWord_7438433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438433).length < 2 ^ (prefixWord ++ tailWord_7438433).sum := by decide
  have hdescent : baseEnd_7438433 < baseStart_7438433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438450 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7438450 : Nat := 118140960795 + 7438450 * 2 ^ 59
def prefixEnd_7438450 : Nat := 4983230072969 + 3 ^ 40 * 7438450 * 2
def baseEnd_7438450 : Nat := 3819500174436527263866197

theorem tailTrace_7438450 : CollatzResearch.WordTrace tailWord_7438450 prefixEnd_7438450 3819500174436527263866197 := by
  unfold tailWord_7438450
  simp only [CollatzResearch.WordTrace]
  refine ⟨67825639975443377741126201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180868373267849007309669869 67825639975443377741126201)
  ·
    refine ⟨50869229981582533305844651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67825639975443377741126201 50869229981582533305844651)
    ·
      refine ⟨76303844972373799958766977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50869229981582533305844651 76303844972373799958766977)
      ·
        refine ⟨57227883729280349969075233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76303844972373799958766977 57227883729280349969075233)
        ·
          refine ⟨42920912796960262476806425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57227883729280349969075233 42920912796960262476806425)
          ·
            refine ⟨32190684597720196857604819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42920912796960262476806425 32190684597720196857604819)
            ·
              refine ⟨48286026896580295286407229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32190684597720196857604819 48286026896580295286407229)
              ·
                refine ⟨18107260086217610732402711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48286026896580295286407229 18107260086217610732402711)
                ·
                  refine ⟨27160890129326416098604067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18107260086217610732402711 27160890129326416098604067)
                  ·
                    refine ⟨40741335193989624147906101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27160890129326416098604067 40741335193989624147906101)
                    ·
                      refine ⟨3819500174436527263866197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40741335193989624147906101 3819500174436527263866197)
                      ·
                        rfl

theorem cell23_7438450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7438450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438450 prefixEnd_7438450 := by exact prefixLift 7438450
  have htrace : WordTrace (prefixWord ++ tailWord_7438450) baseStart_7438450 baseEnd_7438450 := by
    simpa [prefixWord, tailWord_7438450, baseEnd_7438450] using wordTrace_append hprefix tailTrace_7438450
  have hstable : (prefixWord ++ tailWord_7438450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438450).length < 2 ^ (prefixWord ++ tailWord_7438450).sum := by decide
  have hdescent : baseEnd_7438450 < baseStart_7438450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438473 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_7438473 : Nat := 118140960795 + 7438473 * 2 ^ 59
def prefixEnd_7438473 : Nat := 4983230072969 + 3 ^ 40 * 7438473 * 2
def baseEnd_7438473 : Nat := 3819511984491580673878591

theorem tailTrace_7438473 : CollatzResearch.WordTrace tailWord_7438473 prefixEnd_7438473 3819511984491580673878591 := by
  unfold tailWord_7438473
  simp only [CollatzResearch.WordTrace]
  refine ⟨271303398780690185892592073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180868932520460123928394715 271303398780690185892592073)
  ·
    refine ⟨203477549085517639419444055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271303398780690185892592073 203477549085517639419444055)
    ·
      refine ⟨305216323628276459129166083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203477549085517639419444055 305216323628276459129166083)
      ·
        refine ⟨457824485442414688693749125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305216323628276459129166083 457824485442414688693749125)
        ·
          refine ⟨85842091020452754130077961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457824485442414688693749125 85842091020452754130077961)
          ·
            refine ⟨64381568265339565597558471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85842091020452754130077961 64381568265339565597558471)
            ·
              refine ⟨96572352398009348396337707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64381568265339565597558471 96572352398009348396337707)
              ·
                refine ⟨144858528597014022594506561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96572352398009348396337707 144858528597014022594506561)
                ·
                  refine ⟨108643896447760516945879921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144858528597014022594506561 108643896447760516945879921)
                  ·
                    refine ⟨81482922335820387709409941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108643896447760516945879921 81482922335820387709409941)
                    ·
                      refine ⟨3819511984491580673878591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81482922335820387709409941 3819511984491580673878591)
                      ·
                        rfl

theorem cell23_7438473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_7438473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438473 prefixEnd_7438473 := by exact prefixLift 7438473
  have htrace : WordTrace (prefixWord ++ tailWord_7438473) baseStart_7438473 baseEnd_7438473 := by
    simpa [prefixWord, tailWord_7438473, baseEnd_7438473] using wordTrace_append hprefix tailTrace_7438473
  have hstable : (prefixWord ++ tailWord_7438473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438473).length < 2 ^ (prefixWord ++ tailWord_7438473).sum := by decide
  have hdescent : baseEnd_7438473 < baseStart_7438473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438474 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_7438474 : Nat := 118140960795 + 7438474 * 2 ^ 59
def prefixEnd_7438474 : Nat := 4983230072969 + 3 ^ 40 * 7438474 * 2
def baseEnd_7438474 : Nat := 1273170832657411723322029

theorem tailTrace_7438474 : CollatzResearch.WordTrace tailWord_7438474 prefixEnd_7438474 1273170832657411723322029 := by
  unfold tailWord_7438474
  simp only [CollatzResearch.WordTrace]
  refine ⟨67825858813421640765844619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180868956835791042042252317 67825858813421640765844619)
  ·
    refine ⟨101738788220132461148766929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67825858813421640765844619 101738788220132461148766929)
    ·
      refine ⟨76304091165099345861575197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101738788220132461148766929 76304091165099345861575197)
      ·
        refine ⟨28614034186912254698090699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76304091165099345861575197 28614034186912254698090699)
        ·
          refine ⟨42921051280368382047136049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28614034186912254698090699 42921051280368382047136049)
          ·
            refine ⟨32190788460276286535352037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42921051280368382047136049 32190788460276286535352037)
            ·
              refine ⟨6035772836301803725378507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32190788460276286535352037 6035772836301803725378507)
              ·
                refine ⟨9053659254452705588067761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035772836301803725378507 9053659254452705588067761)
                ·
                  refine ⟨6790244440839529191050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053659254452705588067761 6790244440839529191050821)
                  ·
                    refine ⟨1273170832657411723322029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6790244440839529191050821 1273170832657411723322029)
                    ·
                      rfl

theorem cell23_7438474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_7438474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438474 prefixEnd_7438474 := by exact prefixLift 7438474
  have htrace : WordTrace (prefixWord ++ tailWord_7438474) baseStart_7438474 baseEnd_7438474 := by
    simpa [prefixWord, tailWord_7438474, baseEnd_7438474] using wordTrace_append hprefix tailTrace_7438474
  have hstable : (prefixWord ++ tailWord_7438474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438474).length < 2 ^ (prefixWord ++ tailWord_7438474).sum := by decide
  have hdescent : baseEnd_7438474 < baseStart_7438474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438480 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_7438480 : Nat := 118140960795 + 7438480 * 2 ^ 59
def prefixEnd_7438480 : Nat := 4983230072969 + 3 ^ 40 * 7438480 * 2
def baseEnd_7438480 : Nat := 3819515578856162146491059

theorem tailTrace_7438480 : CollatzResearch.WordTrace tailWord_7438480 prefixEnd_7438480 3819515578856162146491059 := by
  unfold tailWord_7438480
  simp only [CollatzResearch.WordTrace]
  refine ⟨135651827045832413044048447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180869102727776550725397929 135651827045832413044048447)
  ·
    refine ⟨203477740568748619566072671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135651827045832413044048447 203477740568748619566072671)
    ·
      refine ⟨305216610853122929349109007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203477740568748619566072671 305216610853122929349109007)
      ·
        refine ⟨457824916279684394023663511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305216610853122929349109007 457824916279684394023663511)
        ·
          refine ⟨686737374419526591035495267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457824916279684394023663511 686737374419526591035495267)
          ·
            refine ⟨1030106061629289886553242901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686737374419526591035495267 1030106061629289886553242901)
            ·
              refine ⟨48286221638872963432183261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1030106061629289886553242901 48286221638872963432183261)
              ·
                refine ⟨18107333114577361287068723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48286221638872963432183261 18107333114577361287068723)
                ·
                  refine ⟨27160999671866041930603085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18107333114577361287068723 27160999671866041930603085)
                  ·
                    refine ⟨10185374876949765723976157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27160999671866041930603085 10185374876949765723976157)
                    ·
                      refine ⟨3819515578856162146491059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10185374876949765723976157 3819515578856162146491059)
                      ·
                        rfl

theorem cell23_7438480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_7438480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438480 prefixEnd_7438480 := by exact prefixLift 7438480
  have htrace : WordTrace (prefixWord ++ tailWord_7438480) baseStart_7438480 baseEnd_7438480 := by
    simpa [prefixWord, tailWord_7438480, baseEnd_7438480] using wordTrace_append hprefix tailTrace_7438480
  have hstable : (prefixWord ++ tailWord_7438480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438480).length < 2 ^ (prefixWord ++ tailWord_7438480).sum := by decide
  have hdescent : baseEnd_7438480 < baseStart_7438480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438494 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_7438494 : Nat := 118140960795 + 7438494 * 2 ^ 59
def prefixEnd_7438494 : Nat := 4983230072969 + 3 ^ 40 * 7438494 * 2
def baseEnd_7438494 : Nat := 3819522767585325091715995

theorem tailTrace_7438494 : CollatzResearch.WordTrace tailWord_7438494 prefixEnd_7438494 3819522767585325091715995 := by
  unfold tailWord_7438494
  simp only [CollatzResearch.WordTrace]
  refine ⟨33913020589201763309888317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180869443142409404319404357 33913020589201763309888317)
  ·
    refine ⟨12717382720950661241208119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33913020589201763309888317 12717382720950661241208119)
    ·
      refine ⟨19076074081425991861812179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12717382720950661241208119 19076074081425991861812179)
      ·
        refine ⟨28614111122138987792718269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19076074081425991861812179 28614111122138987792718269)
        ·
          refine ⟨10730291670802120422269351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28614111122138987792718269 10730291670802120422269351)
          ·
            refine ⟨16095437506203180633404027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730291670802120422269351 16095437506203180633404027)
            ·
              refine ⟨24143156259304770950106041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095437506203180633404027 24143156259304770950106041)
              ·
                refine ⟨18107367194478578212579531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24143156259304770950106041 18107367194478578212579531)
                ·
                  refine ⟨27161050791717867318869297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18107367194478578212579531 27161050791717867318869297)
                  ·
                    refine ⟨20370788093788400489151973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27161050791717867318869297 20370788093788400489151973)
                    ·
                      refine ⟨3819522767585325091715995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20370788093788400489151973 3819522767585325091715995)
                      ·
                        rfl

theorem cell23_7438494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_7438494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438494 prefixEnd_7438494 := by exact prefixLift 7438494
  have htrace : WordTrace (prefixWord ++ tailWord_7438494) baseStart_7438494 baseEnd_7438494 := by
    simpa [prefixWord, tailWord_7438494, baseEnd_7438494] using wordTrace_append hprefix tailTrace_7438494
  have hstable : (prefixWord ++ tailWord_7438494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438494).length < 2 ^ (prefixWord ++ tailWord_7438494).sum := by decide
  have hdescent : baseEnd_7438494 < baseStart_7438494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438497 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7438497 : Nat := 118140960795 + 7438497 * 2 ^ 59
def prefixEnd_7438497 : Nat := 4983230072969 + 3 ^ 40 * 7438497 * 2
def baseEnd_7438497 : Nat := 3819524308027288579978481

theorem tailTrace_7438497 : CollatzResearch.WordTrace tailWord_7438497 prefixEnd_7438497 3819524308027288579978481 := by
  unfold tailWord_7438497
  simp only [CollatzResearch.WordTrace]
  refine ⟨271304274132603237991465745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180869516088402158660977163 271304274132603237991465745)
  ·
    refine ⟨203478205599452428493599309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271304274132603237991465745 203478205599452428493599309)
    ·
      refine ⟨76304327099794660685099741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203478205599452428493599309 76304327099794660685099741)
      ·
        refine ⟨28614122662422997756912403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76304327099794660685099741 28614122662422997756912403)
        ·
          refine ⟨42921183993634496635368605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28614122662422997756912403 42921183993634496635368605)
          ·
            refine ⟨16095443997612936238263227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42921183993634496635368605 16095443997612936238263227)
            ·
              refine ⟨24143165996419404357394841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095443997612936238263227 24143165996419404357394841)
              ·
                refine ⟨18107374497314553268046131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24143165996419404357394841 18107374497314553268046131)
                ·
                  refine ⟨27161061745971829902069197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18107374497314553268046131 27161061745971829902069197)
                  ·
                    refine ⟨10185398154739436213275949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27161061745971829902069197 10185398154739436213275949)
                    ·
                      refine ⟨3819524308027288579978481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10185398154739436213275949 3819524308027288579978481)
                      ·
                        rfl

theorem cell23_7438497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7438497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438497 prefixEnd_7438497 := by exact prefixLift 7438497
  have htrace : WordTrace (prefixWord ++ tailWord_7438497) baseStart_7438497 baseEnd_7438497 := by
    simpa [prefixWord, tailWord_7438497, baseEnd_7438497] using wordTrace_append hprefix tailTrace_7438497
  have hstable : (prefixWord ++ tailWord_7438497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438497).length < 2 ^ (prefixWord ++ tailWord_7438497).sum := by decide
  have hdescent : baseEnd_7438497 < baseStart_7438497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438514 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_7438514 : Nat := 118140960795 + 7438514 * 2 ^ 59
def prefixEnd_7438514 : Nat := 4983230072969 + 3 ^ 40 * 7438514 * 2
def baseEnd_7438514 : Nat := 3819533037198415013465903

theorem tailTrace_7438514 : CollatzResearch.WordTrace tailWord_7438514 prefixEnd_7438514 3819533037198415013465903 := by
  unfold tailWord_7438514
  simp only [CollatzResearch.WordTrace]
  refine ⟨67826223543385412473708649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180869929449027766596556397 67826223543385412473708649)
  ·
    refine ⟨50869667657539059355281487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67826223543385412473708649 50869667657539059355281487)
    ·
      refine ⟨76304501486308589032922231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50869667657539059355281487 76304501486308589032922231)
      ·
        refine ⟨114456752229462883549383347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76304501486308589032922231 114456752229462883549383347)
        ·
          refine ⟨171685128344194325324075021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114456752229462883549383347 171685128344194325324075021)
          ·
            refine ⟨64381923129072871996528133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171685128344194325324075021 64381923129072871996528133)
            ·
              refine ⟨12071610586701163499349025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64381923129072871996528133 12071610586701163499349025)
              ·
                refine ⟨9053707940025872624511769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12071610586701163499349025 9053707940025872624511769)
                ·
                  refine ⟨6790280955019404468383827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053707940025872624511769 6790280955019404468383827)
                  ·
                    refine ⟨10185421432529106702575741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6790280955019404468383827 10185421432529106702575741)
                    ·
                      refine ⟨3819533037198415013465903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10185421432529106702575741 3819533037198415013465903)
                      ·
                        rfl

theorem cell23_7438514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_7438514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438514 prefixEnd_7438514 := by exact prefixLift 7438514
  have htrace : WordTrace (prefixWord ++ tailWord_7438514) baseStart_7438514 baseEnd_7438514 := by
    simpa [prefixWord, tailWord_7438514, baseEnd_7438514] using wordTrace_append hprefix tailTrace_7438514
  have hstable : (prefixWord ++ tailWord_7438514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438514).length < 2 ^ (prefixWord ++ tailWord_7438514).sum := by decide
  have hdescent : baseEnd_7438514 < baseStart_7438514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438567 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_7438567 : Nat := 118140960795 + 7438567 * 2 ^ 59
def prefixEnd_7438567 : Nat := 4983230072969 + 3 ^ 40 * 7438567 * 2
def baseEnd_7438567 : Nat := 3819560251673103306103159

theorem tailTrace_7438567 : CollatzResearch.WordTrace tailWord_7438567 prefixEnd_7438567 3819560251673103306103159 := by
  unfold tailWord_7438567
  simp only [CollatzResearch.WordTrace]
  refine ⟨271306827242349639946513955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180871218161566426631009303 271306827242349639946513955)
  ·
    refine ⟨406960240863524459919770933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271306827242349639946513955 406960240863524459919770933)
    ·
      refine ⟨38152522580955418117478525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406960240863524459919770933 38152522580955418117478525)
      ·
        refine ⟨14307195967858281794054447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38152522580955418117478525 14307195967858281794054447)
        ·
          refine ⟨21460793951787422691081671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307195967858281794054447 21460793951787422691081671)
          ·
            refine ⟨32191190927681134036622507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21460793951787422691081671 32191190927681134036622507)
            ·
              refine ⟨48286786391521701054933761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32191190927681134036622507 48286786391521701054933761)
              ·
                refine ⟨36215089793641275791200321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48286786391521701054933761 36215089793641275791200321)
                ·
                  refine ⟨27161317345230956843400241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36215089793641275791200321 27161317345230956843400241)
                  ·
                    refine ⟨20370988008923217632550181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27161317345230956843400241 20370988008923217632550181)
                    ·
                      refine ⟨3819560251673103306103159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20370988008923217632550181 3819560251673103306103159)
                      ·
                        rfl

theorem cell23_7438567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_7438567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438567 prefixEnd_7438567 := by exact prefixLift 7438567
  have htrace : WordTrace (prefixWord ++ tailWord_7438567) baseStart_7438567 baseEnd_7438567 := by
    simpa [prefixWord, tailWord_7438567, baseEnd_7438567] using wordTrace_append hprefix tailTrace_7438567
  have hstable : (prefixWord ++ tailWord_7438567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438567).length < 2 ^ (prefixWord ++ tailWord_7438567).sum := by decide
  have hdescent : baseEnd_7438567 < baseStart_7438567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438577 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 5]
def baseStart_7438577 : Nat := 118140960795 + 7438577 * 2 ^ 59
def prefixEnd_7438577 : Nat := 4983230072969 + 3 ^ 40 * 7438577 * 2
def baseEnd_7438577 : Nat := 424396154053294251886457

theorem tailTrace_7438577 : CollatzResearch.WordTrace tailWord_7438577 prefixEnd_7438577 424396154053294251886457 := by
  unfold tailWord_7438577
  simp only [CollatzResearch.WordTrace]
  refine ⟨271307191972313411654377985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180871461314875607769585323 271307191972313411654377985)
  ·
    refine ⟨203480393979235058740783489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271307191972313411654377985 203480393979235058740783489)
    ·
      refine ⟨152610295484426294055587617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203480393979235058740783489 152610295484426294055587617)
      ·
        refine ⟨114457721613319720541690713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152610295484426294055587617 114457721613319720541690713)
        ·
          refine ⟨85843291209989790406268035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114457721613319720541690713 85843291209989790406268035)
          ·
            refine ⟨128764936814984685609402053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85843291209989790406268035 128764936814984685609402053)
            ·
              refine ⟨24143425652809628551762885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128764936814984685609402053 24143425652809628551762885)
              ·
                refine ⟨4526892309901805353455541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24143425652809628551762885 4526892309901805353455541)
                ·
                  refine ⟨424396154053294251886457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4526892309901805353455541 424396154053294251886457)
                  ·
                    rfl

theorem cell23_7438577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 5].length) (baseStart_7438577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438577 prefixEnd_7438577 := by exact prefixLift 7438577
  have htrace : WordTrace (prefixWord ++ tailWord_7438577) baseStart_7438577 baseEnd_7438577 := by
    simpa [prefixWord, tailWord_7438577, baseEnd_7438577] using wordTrace_append hprefix tailTrace_7438577
  have hstable : (prefixWord ++ tailWord_7438577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438577).length < 2 ^ (prefixWord ++ tailWord_7438577).sum := by decide
  have hdescent : baseEnd_7438577 < baseStart_7438577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438588 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_7438588 : Nat := 118140960795 + 7438588 * 2 ^ 59
def prefixEnd_7438588 : Nat := 4983230072969 + 3 ^ 40 * 7438588 * 2
def baseEnd_7438588 : Nat := 3819571034766847723940563

theorem tailTrace_7438588 : CollatzResearch.WordTrace tailWord_7438588 prefixEnd_7438588 3819571034766847723940563 := by
  unfold tailWord_7438588
  simp only [CollatzResearch.WordTrace]
  refine ⟨135653796587636780266514209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180871728783515707022018945 135653796587636780266514209)
  ·
    refine ⟨101740347440727585199885657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135653796587636780266514209 101740347440727585199885657)
    ·
      refine ⟨76305260580545688899914243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101740347440727585199885657 76305260580545688899914243)
      ·
        refine ⟨114457890870818533349871365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76305260580545688899914243 114457890870818533349871365)
        ·
          refine ⟨21460854538278475003100881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114457890870818533349871365 21460854538278475003100881)
          ·
            refine ⟨16095640903708856252325661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21460854538278475003100881 16095640903708856252325661)
            ·
              refine ⟨6035865338890821094622123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16095640903708856252325661 6035865338890821094622123)
              ·
                refine ⟨9053798008336231641933185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035865338890821094622123 9053798008336231641933185)
                ·
                  refine ⟨6790348506252173731449889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053798008336231641933185 6790348506252173731449889)
                  ·
                    refine ⟨5092761379689130298587417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6790348506252173731449889 5092761379689130298587417)
                    ·
                      refine ⟨3819571034766847723940563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092761379689130298587417 3819571034766847723940563)
                      ·
                        rfl

theorem cell23_7438588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_7438588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438588 prefixEnd_7438588 := by exact prefixLift 7438588
  have htrace : WordTrace (prefixWord ++ tailWord_7438588) baseStart_7438588 baseEnd_7438588 := by
    simpa [prefixWord, tailWord_7438588, baseEnd_7438588] using wordTrace_append hprefix tailTrace_7438588
  have hstable : (prefixWord ++ tailWord_7438588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438588).length < 2 ^ (prefixWord ++ tailWord_7438588).sum := by decide
  have hdescent : baseEnd_7438588 < baseStart_7438588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438627 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 4]
def baseStart_7438627 : Nat := 118140960795 + 7438627 * 2 ^ 59
def prefixEnd_7438627 : Nat := 4983230072969 + 3 ^ 40 * 7438627 * 2
def baseEnd_7438627 : Nat := 3819591060512373071352883

theorem tailTrace_7438627 : CollatzResearch.WordTrace tailWord_7438627 prefixEnd_7438627 3819591060512373071352883 := by
  unfold tailWord_7438627
  simp only [CollatzResearch.WordTrace]
  refine ⟨271309015622132270193698135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180872677081421513462465423 271309015622132270193698135)
  ·
    refine ⟨406963523433198405290547203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271309015622132270193698135 406963523433198405290547203)
    ·
      refine ⟨610445285149797607935820805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406963523433198405290547203 610445285149797607935820805)
      ·
        refine ⟨114458490965587051487966401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 610445285149797607935820805 114458490965587051487966401)
        ·
          refine ⟨85843868224190288615974801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114458490965587051487966401 85843868224190288615974801)
          ·
            refine ⟨64382901168142716461981101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85843868224190288615974801 64382901168142716461981101)
            ·
              refine ⟨24143587938053518673242913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64382901168142716461981101 24143587938053518673242913)
              ·
                refine ⟨18107690953540139004932185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24143587938053518673242913 18107690953540139004932185)
                ·
                  refine ⟨13580768215155104253699139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18107690953540139004932185 13580768215155104253699139)
                  ·
                    refine ⟨20371152322732656380548709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13580768215155104253699139 20371152322732656380548709)
                    ·
                      refine ⟨3819591060512373071352883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20371152322732656380548709 3819591060512373071352883)
                      ·
                        rfl

theorem cell23_7438627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_7438627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438627 prefixEnd_7438627 := by exact prefixLift 7438627
  have htrace : WordTrace (prefixWord ++ tailWord_7438627) baseStart_7438627 baseEnd_7438627 := by
    simpa [prefixWord, tailWord_7438627, baseEnd_7438627] using wordTrace_append hprefix tailTrace_7438627
  have hstable : (prefixWord ++ tailWord_7438627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438627).length < 2 ^ (prefixWord ++ tailWord_7438627).sum := by decide
  have hdescent : baseEnd_7438627 < baseStart_7438627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438634 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7438634 : Nat := 118140960795 + 7438634 * 2 ^ 59
def prefixEnd_7438634 : Nat := 4983230072969 + 3 ^ 40 * 7438634 * 2
def baseEnd_7438634 : Nat := 3819594654876954543965351

theorem tailTrace_7438634 : CollatzResearch.WordTrace tailWord_7438634 prefixEnd_7438634 3819594654876954543965351 := by
  unfold tailWord_7438634
  simp only [CollatzResearch.WordTrace]
  refine ⟨67827317733276727597300739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180872847288737940259468637 67827317733276727597300739)
  ·
    refine ⟨101740976599915091395951109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67827317733276727597300739 101740976599915091395951109)
    ·
      refine ⟨19076433112484079636740833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101740976599915091395951109 19076433112484079636740833)
      ·
        refine ⟨14307324834363059727555625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19076433112484079636740833 14307324834363059727555625)
        ·
          refine ⟨10730493625772294795666719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14307324834363059727555625 10730493625772294795666719)
          ·
            refine ⟨16095740438658442193500079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730493625772294795666719 16095740438658442193500079)
            ·
              refine ⟨24143610657987663290250119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095740438658442193500079 24143610657987663290250119)
              ·
                refine ⟨36215415986981494935375179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24143610657987663290250119 36215415986981494935375179)
                ·
                  refine ⟨54323123980472242403062769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36215415986981494935375179 54323123980472242403062769)
                  ·
                    refine ⟨40742342985354181802297077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54323123980472242403062769 40742342985354181802297077)
                    ·
                      refine ⟨3819594654876954543965351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40742342985354181802297077 3819594654876954543965351)
                      ·
                        rfl

theorem cell23_7438634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7438634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438634 prefixEnd_7438634 := by exact prefixLift 7438634
  have htrace : WordTrace (prefixWord ++ tailWord_7438634) baseStart_7438634 baseEnd_7438634 := by
    simpa [prefixWord, tailWord_7438634, baseEnd_7438634] using wordTrace_append hprefix tailTrace_7438634
  have hstable : (prefixWord ++ tailWord_7438634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438634).length < 2 ^ (prefixWord ++ tailWord_7438634).sum := by decide
  have hdescent : baseEnd_7438634 < baseStart_7438634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438640 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_7438640 : Nat := 118140960795 + 7438640 * 2 ^ 59
def prefixEnd_7438640 : Nat := 4983230072969 + 3 ^ 40 * 7438640 * 2
def baseEnd_7438640 : Nat := 3819597735760881520490323

theorem tailTrace_7438640 : CollatzResearch.WordTrace tailWord_7438640 prefixEnd_7438640 3819597735760881520490323 := by
  unfold tailWord_7438640
  simp only [CollatzResearch.WordTrace]
  refine ⟨135654744885542586706960687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180872993180723448942614249 135654744885542586706960687)
  ·
    refine ⟨203482117328313880060441031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135654744885542586706960687 203482117328313880060441031)
    ·
      refine ⟨305223175992470820090661547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203482117328313880060441031 305223175992470820090661547)
      ·
        refine ⟨457834763988706230135992321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305223175992470820090661547 457834763988706230135992321)
        ·
          refine ⟨343376072991529672601994241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457834763988706230135992321 343376072991529672601994241)
          ·
            refine ⟨257532054743647254451495681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343376072991529672601994241 257532054743647254451495681)
            ·
              refine ⟨193149041057735440838621761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257532054743647254451495681 193149041057735440838621761)
              ·
                refine ⟨144861780793301580628966321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193149041057735440838621761 144861780793301580628966321)
                ·
                  refine ⟨108646335594976185471724741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144861780793301580628966321 108646335594976185471724741)
                  ·
                    refine ⟨20371187924058034775948389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108646335594976185471724741 20371187924058034775948389)
                    ·
                      refine ⟨3819597735760881520490323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20371187924058034775948389 3819597735760881520490323)
                      ·
                        rfl

theorem cell23_7438640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_7438640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438640 prefixEnd_7438640 := by exact prefixLift 7438640
  have htrace : WordTrace (prefixWord ++ tailWord_7438640) baseStart_7438640 baseEnd_7438640 := by
    simpa [prefixWord, tailWord_7438640, baseEnd_7438640] using wordTrace_append hprefix tailTrace_7438640
  have hstable : (prefixWord ++ tailWord_7438640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438640).length < 2 ^ (prefixWord ++ tailWord_7438640).sum := by decide
  have hdescent : baseEnd_7438640 < baseStart_7438640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438721 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_7438721 : Nat := 118140960795 + 7438721 * 2 ^ 59
def prefixEnd_7438721 : Nat := 4983230072969 + 3 ^ 40 * 7438721 * 2
def baseEnd_7438721 : Nat := 3819639327693895703577451

theorem tailTrace_7438721 : CollatzResearch.WordTrace tailWord_7438721 prefixEnd_7438721 3819639327693895703577451 := by
  unfold tailWord_7438721
  simp only [CollatzResearch.WordTrace]
  refine ⟨271312444083791724247620017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180874962722527816165080011 271312444083791724247620017)
  ·
    refine ⟨203484333062843793185715013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271312444083791724247620017 203484333062843793185715013)
    ·
      refine ⟨38153312449283211222321565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203484333062843793185715013 38153312449283211222321565)
      ·
        refine ⟨14307492168481204208370587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38153312449283211222321565 14307492168481204208370587)
        ·
          refine ⟨21461238252721806312555881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307492168481204208370587 21461238252721806312555881)
          ·
            refine ⟨16095928689541354734416911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21461238252721806312555881 16095928689541354734416911)
            ·
              refine ⟨24143893034312032101625367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095928689541354734416911 24143893034312032101625367)
              ·
                refine ⟨36215839551468048152438051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24143893034312032101625367 36215839551468048152438051)
                ·
                  refine ⟨54323759327202072228657077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36215839551468048152438051 54323759327202072228657077)
                  ·
                    refine ⟨5092852436925194271436601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54323759327202072228657077 5092852436925194271436601)
                    ·
                      refine ⟨3819639327693895703577451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092852436925194271436601 3819639327693895703577451)
                      ·
                        rfl

theorem cell23_7438721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_7438721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438721 prefixEnd_7438721 := by exact prefixLift 7438721
  have htrace : WordTrace (prefixWord ++ tailWord_7438721) baseStart_7438721 baseEnd_7438721 := by
    simpa [prefixWord, tailWord_7438721, baseEnd_7438721] using wordTrace_append hprefix tailTrace_7438721
  have hstable : (prefixWord ++ tailWord_7438721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438721).length < 2 ^ (prefixWord ++ tailWord_7438721).sum := by decide
  have hdescent : baseEnd_7438721 < baseStart_7438721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438727 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 1, 6]
def baseStart_7438727 : Nat := 118140960795 + 7438727 * 2 ^ 59
def prefixEnd_7438727 : Nat := 4983230072969 + 3 ^ 40 * 7438727 * 2
def baseEnd_7438727 : Nat := 1273214136192607560034141

theorem tailTrace_7438727 : CollatzResearch.WordTrace tailWord_7438727 prefixEnd_7438727 1273214136192607560034141 := by
  unfold tailWord_7438727
  simp only [CollatzResearch.WordTrace]
  refine ⟨271312662921769987272338435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180875108614513324848225623 271312662921769987272338435)
  ·
    refine ⟨406968994382654980908507653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271312662921769987272338435 406968994382654980908507653)
    ·
      refine ⟨76306686446747808920345185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406968994382654980908507653 76306686446747808920345185)
      ·
        refine ⟨57230014835060856690258889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76306686446747808920345185 57230014835060856690258889)
        ·
          refine ⟨42922511126295642517694167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57230014835060856690258889 42922511126295642517694167)
          ·
            refine ⟨64383766689443463776541251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42922511126295642517694167 64383766689443463776541251)
            ·
              refine ⟨96575650034165195664811877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64383766689443463776541251 96575650034165195664811877)
              ·
                refine ⟨18107934381405974187152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96575650034165195664811877 18107934381405974187152227)
                ·
                  refine ⟨27161901572108961280728341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18107934381405974187152227 27161901572108961280728341)
                  ·
                    refine ⟨1273214136192607560034141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27161901572108961280728341 1273214136192607560034141)
                    ·
                      rfl

theorem cell23_7438727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_7438727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438727 prefixEnd_7438727 := by exact prefixLift 7438727
  have htrace : WordTrace (prefixWord ++ tailWord_7438727) baseStart_7438727 baseEnd_7438727 := by
    simpa [prefixWord, tailWord_7438727, baseEnd_7438727] using wordTrace_append hprefix tailTrace_7438727
  have hstable : (prefixWord ++ tailWord_7438727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438727).length < 2 ^ (prefixWord ++ tailWord_7438727).sum := by decide
  have hdescent : baseEnd_7438727 < baseStart_7438727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438728 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_7438728 : Nat := 118140960795 + 7438728 * 2 ^ 59
def prefixEnd_7438728 : Nat := 4983230072969 + 3 ^ 40 * 7438728 * 2
def baseEnd_7438728 : Nat := 3819642922058477176189919

theorem tailTrace_7438728 : CollatzResearch.WordTrace tailWord_7438728 prefixEnd_7438728 3819642922058477176189919 := by
  unfold tailWord_7438728
  simp only [CollatzResearch.WordTrace]
  refine ⟨135656349697383182221562419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180875132929844242962083225 135656349697383182221562419)
  ·
    refine ⟨203484524546074773332343629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135656349697383182221562419 203484524546074773332343629)
    ·
      refine ⟨76306696704778039999628861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203484524546074773332343629 76306696704778039999628861)
      ·
        refine ⟨28615011264291764999860823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76306696704778039999628861 28615011264291764999860823)
        ·
          refine ⟨42922516896437647499791235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28615011264291764999860823 42922516896437647499791235)
          ·
            refine ⟨64383775344656471249686853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42922516896437647499791235 64383775344656471249686853)
            ·
              refine ⟨12071957877123088359316285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64383775344656471249686853 12071957877123088359316285)
              ·
                refine ⟨4526984203921158134743607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12071957877123088359316285 4526984203921158134743607)
                ·
                  refine ⟨6790476305881737202115411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526984203921158134743607 6790476305881737202115411)
                  ·
                    refine ⟨10185714458822605803173117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6790476305881737202115411 10185714458822605803173117)
                    ·
                      refine ⟨3819642922058477176189919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10185714458822605803173117 3819642922058477176189919)
                      ·
                        rfl

theorem cell23_7438728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_7438728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438728 prefixEnd_7438728 := by exact prefixLift 7438728
  have htrace : WordTrace (prefixWord ++ tailWord_7438728) baseStart_7438728 baseEnd_7438728 := by
    simpa [prefixWord, tailWord_7438728, baseEnd_7438728] using wordTrace_append hprefix tailTrace_7438728
  have hstable : (prefixWord ++ tailWord_7438728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438728).length < 2 ^ (prefixWord ++ tailWord_7438728).sum := by decide
  have hdescent : baseEnd_7438728 < baseStart_7438728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438731 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 1, 5]
def baseStart_7438731 : Nat := 118140960795 + 7438731 * 2 ^ 59
def prefixEnd_7438731 : Nat := 4983230072969 + 3 ^ 40 * 7438731 * 2
def baseEnd_7438731 : Nat := 1273214820833480221484135

theorem tailTrace_7438731 : CollatzResearch.WordTrace tailWord_7438731 prefixEnd_7438731 1273214820833480221484135 := by
  unfold tailWord_7438731
  simp only [CollatzResearch.WordTrace]
  refine ⟨271312808813755495955484047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180875205875836997303656031 271312808813755495955484047)
  ·
    refine ⟨406969213220633243933226071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271312808813755495955484047 406969213220633243933226071)
    ·
      refine ⟨610453819830949865899839107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406969213220633243933226071 610453819830949865899839107)
      ·
        refine ⟨915680729746424798849758661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610453819830949865899839107 915680729746424798849758661)
        ·
          refine ⟨171690136827454649784329749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 915680729746424798849758661 171690136827454649784329749)
          ·
            refine ⟨8047975163786936708640457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171690136827454649784329749 8047975163786936708640457)
            ·
              refine ⟨6035981372840202531480343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8047975163786936708640457 6035981372840202531480343)
              ·
                refine ⟨9053972059260303797220515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035981372840202531480343 9053972059260303797220515)
                ·
                  refine ⟨13580958088890455695830773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9053972059260303797220515 13580958088890455695830773)
                  ·
                    refine ⟨1273214820833480221484135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13580958088890455695830773 1273214820833480221484135)
                    ·
                      rfl

theorem cell23_7438731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 5].length) (baseStart_7438731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438731 prefixEnd_7438731 := by exact prefixLift 7438731
  have htrace : WordTrace (prefixWord ++ tailWord_7438731) baseStart_7438731 baseEnd_7438731 := by
    simpa [prefixWord, tailWord_7438731, baseEnd_7438731] using wordTrace_append hprefix tailTrace_7438731
  have hstable : (prefixWord ++ tailWord_7438731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438731).length < 2 ^ (prefixWord ++ tailWord_7438731).sum := by decide
  have hdescent : baseEnd_7438731 < baseStart_7438731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438754 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7438754 : Nat := 118140960795 + 7438754 * 2 ^ 59
def prefixEnd_7438754 : Nat := 4983230072969 + 3 ^ 40 * 7438754 * 2
def baseEnd_7438754 : Nat := 3819656272555494074464799

theorem tailTrace_7438754 : CollatzResearch.WordTrace tailWord_7438754 prefixEnd_7438754 3819656272555494074464799 := by
  unfold tailWord_7438754
  simp only [CollatzResearch.WordTrace]
  refine ⟨67828411923168042720892829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180875765128448113922380877 67828411923168042720892829)
  ·
    refine ⟨25435654471188016020334811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67828411923168042720892829 25435654471188016020334811)
    ·
      refine ⟨38153481706782024030502217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25435654471188016020334811 38153481706782024030502217)
      ·
        refine ⟨28615111280086518022876663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38153481706782024030502217 28615111280086518022876663)
        ·
          refine ⟨42922666920129777034314995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28615111280086518022876663 42922666920129777034314995)
          ·
            refine ⟨64384000380194665551472493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42922666920129777034314995 64384000380194665551472493)
            ·
              refine ⟨24144000142572999581802185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64384000380194665551472493 24144000142572999581802185)
              ·
                refine ⟨18108000106929749686351639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24144000142572999581802185 18108000106929749686351639)
                ·
                  refine ⟨27162000160394624529527459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18108000106929749686351639 27162000160394624529527459)
                  ·
                    refine ⟨40743000240591936794291189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27162000160394624529527459 40743000240591936794291189)
                    ·
                      refine ⟨3819656272555494074464799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40743000240591936794291189 3819656272555494074464799)
                      ·
                        rfl

theorem cell23_7438754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7438754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438754 prefixEnd_7438754 := by exact prefixLift 7438754
  have htrace : WordTrace (prefixWord ++ tailWord_7438754) baseStart_7438754 baseEnd_7438754 := by
    simpa [prefixWord, tailWord_7438754, baseEnd_7438754] using wordTrace_append hprefix tailTrace_7438754
  have hstable : (prefixWord ++ tailWord_7438754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438754).length < 2 ^ (prefixWord ++ tailWord_7438754).sum := by decide
  have hdescent : baseEnd_7438754 < baseStart_7438754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438802 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_7438802 : Nat := 118140960795 + 7438802 * 2 ^ 59
def prefixEnd_7438802 : Nat := 4983230072969 + 3 ^ 40 * 7438802 * 2
def baseEnd_7438802 : Nat := 3819680919626909886664579

theorem tailTrace_7438802 : CollatzResearch.WordTrace tailWord_7438802 prefixEnd_7438802 3819680919626909886664579 := by
  unfold tailWord_7438802
  simp only [CollatzResearch.WordTrace]
  refine ⟨67828849599124568770329665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180876932264332183387545773 67828849599124568770329665)
  ·
    refine ⟨50871637199343426577747249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67828849599124568770329665 50871637199343426577747249)
    ·
      refine ⟨38153727899507569933310437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50871637199343426577747249 38153727899507569933310437)
      ·
        refine ⟨7153823981157669362495707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38153727899507569933310437 7153823981157669362495707)
        ·
          refine ⟨10730735971736504043743561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7153823981157669362495707 10730735971736504043743561)
          ·
            refine ⟨8048051978802378032807671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10730735971736504043743561 8048051978802378032807671)
            ·
              refine ⟨12072077968203567049211507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048051978802378032807671 12072077968203567049211507)
              ·
                refine ⟨18108116952305350573817261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12072077968203567049211507 18108116952305350573817261)
                ·
                  refine ⟨6790543857114506465181473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18108116952305350573817261 6790543857114506465181473)
                  ·
                    refine ⟨5092907892835879848886105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6790543857114506465181473 5092907892835879848886105)
                    ·
                      refine ⟨3819680919626909886664579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092907892835879848886105 3819680919626909886664579)
                      ·
                        rfl

theorem cell23_7438802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_7438802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438802 prefixEnd_7438802 := by exact prefixLift 7438802
  have htrace : WordTrace (prefixWord ++ tailWord_7438802) baseStart_7438802 baseEnd_7438802 := by
    simpa [prefixWord, tailWord_7438802, baseEnd_7438802] using wordTrace_append hprefix tailTrace_7438802
  have hstable : (prefixWord ++ tailWord_7438802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438802).length < 2 ^ (prefixWord ++ tailWord_7438802).sum := by decide
  have hdescent : baseEnd_7438802 < baseStart_7438802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438817 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_7438817 : Nat := 118140960795 + 7438817 * 2 ^ 59
def prefixEnd_7438817 : Nat := 4983230072969 + 3 ^ 40 * 7438817 * 2
def baseEnd_7438817 : Nat := 1273229540612242442659003

theorem tailTrace_7438817 : CollatzResearch.WordTrace tailWord_7438817 prefixEnd_7438817 1273229540612242442659003 := by
  unfold tailWord_7438817
  simp only [CollatzResearch.WordTrace]
  refine ⟨271315945491443932643114705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180877296994295955095409803 271315945491443932643114705)
  ·
    refine ⟨203486959118582949482336029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271315945491443932643114705 203486959118582949482336029)
    ·
      refine ⟨76307609669468606055876011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203486959118582949482336029 76307609669468606055876011)
      ·
        refine ⟨114461414504202909083814017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76307609669468606055876011 114461414504202909083814017)
        ·
          refine ⟨85846060878152181812860513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114461414504202909083814017 85846060878152181812860513)
          ·
            refine ⟨64384545658614136359645385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85846060878152181812860513 64384545658614136359645385)
            ·
              refine ⟨48288409243960602269734039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64384545658614136359645385 48288409243960602269734039)
              ·
                refine ⟨72432613865940903404601059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48288409243960602269734039 72432613865940903404601059)
                ·
                  refine ⟨108648920798911355106901589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72432613865940903404601059 108648920798911355106901589)
                  ·
                    refine ⟨1273229540612242442659003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108648920798911355106901589 1273229540612242442659003)
                    ·
                      rfl

theorem cell23_7438817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_7438817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438817 prefixEnd_7438817 := by exact prefixLift 7438817
  have htrace : WordTrace (prefixWord ++ tailWord_7438817) baseStart_7438817 baseEnd_7438817 := by
    simpa [prefixWord, tailWord_7438817, baseEnd_7438817] using wordTrace_append hprefix tailTrace_7438817
  have hstable : (prefixWord ++ tailWord_7438817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438817).length < 2 ^ (prefixWord ++ tailWord_7438817).sum := by decide
  have hdescent : baseEnd_7438817 < baseStart_7438817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438827 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5]
def baseStart_7438827 : Nat := 118140960795 + 7438827 * 2 ^ 59
def prefixEnd_7438827 : Nat := 4983230072969 + 3 ^ 40 * 7438827 * 2
def baseEnd_7438827 : Nat := 3819693756643272288851963

theorem tailTrace_7438827 : CollatzResearch.WordTrace tailWord_7438827 prefixEnd_7438827 3819693756643272288851963 := by
  unfold tailWord_7438827
  simp only [CollatzResearch.WordTrace]
  refine ⟨271316310221407704350978735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180877540147605136233985823 271316310221407704350978735)
  ·
    refine ⟨406974465332111556526468103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271316310221407704350978735 406974465332111556526468103)
    ·
      refine ⟨610461697998167334789702155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406974465332111556526468103 610461697998167334789702155)
      ·
        refine ⟨915692546997251002184553233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610461697998167334789702155 915692546997251002184553233)
        ·
          refine ⟨686769410247938251638414925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915692546997251002184553233 686769410247938251638414925)
          ·
            refine ⟨257538528842976844364405597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686769410247938251638414925 257538528842976844364405597)
            ·
              refine ⟨96576948316116316636652099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257538528842976844364405597 96576948316116316636652099)
              ·
                refine ⟨144865422474174474954978149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96576948316116316636652099 144865422474174474954978149)
                ·
                  refine ⟨27162266713907714054058403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144865422474174474954978149 27162266713907714054058403)
                  ·
                    refine ⟨40743400070861571081087605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27162266713907714054058403 40743400070861571081087605)
                    ·
                      refine ⟨3819693756643272288851963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40743400070861571081087605 3819693756643272288851963)
                      ·
                        rfl

theorem cell23_7438827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_7438827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438827 prefixEnd_7438827 := by exact prefixLift 7438827
  have htrace : WordTrace (prefixWord ++ tailWord_7438827) baseStart_7438827 baseEnd_7438827 := by
    simpa [prefixWord, tailWord_7438827, baseEnd_7438827] using wordTrace_append hprefix tailTrace_7438827
  have hstable : (prefixWord ++ tailWord_7438827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438827).length < 2 ^ (prefixWord ++ tailWord_7438827).sum := by decide
  have hdescent : baseEnd_7438827 < baseStart_7438827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438841 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 6, 2, 2]
def baseStart_7438841 : Nat := 118140960795 + 7438841 * 2 ^ 59
def prefixEnd_7438841 : Nat := 4983230072969 + 3 ^ 40 * 7438841 * 2
def baseEnd_7438841 : Nat := 3819700945372435234076899

theorem tailTrace_7438841 : CollatzResearch.WordTrace tailWord_7438841 prefixEnd_7438841 3819700945372435234076899 := by
  unfold tailWord_7438841
  simp only [CollatzResearch.WordTrace]
  refine ⟨271316820843356984741988377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180877880562237989827992251 271316820843356984741988377)
  ·
    refine ⟨203487615632517738556491283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271316820843356984741988377 203487615632517738556491283)
    ·
      refine ⟨305231423448776607834736925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203487615632517738556491283 305231423448776607834736925)
      ·
        refine ⟨114461783793291227938026347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305231423448776607834736925 114461783793291227938026347)
        ·
          refine ⟨171692675689936841907039521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114461783793291227938026347 171692675689936841907039521)
          ·
            refine ⟨128769506767452631430279641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171692675689936841907039521 128769506767452631430279641)
            ·
              refine ⟨96577130075589473572709731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128769506767452631430279641 96577130075589473572709731)
              ·
                refine ⟨144865695113384210359064597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96577130075589473572709731 144865695113384210359064597)
                ·
                  refine ⟨6790579458439884860581153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144865695113384210359064597 6790579458439884860581153)
                  ·
                    refine ⟨5092934593829913645435865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6790579458439884860581153 5092934593829913645435865)
                    ·
                      refine ⟨3819700945372435234076899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5092934593829913645435865 3819700945372435234076899)
                      ·
                        rfl

theorem cell23_7438841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_7438841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438841 prefixEnd_7438841 := by exact prefixLift 7438841
  have htrace : WordTrace (prefixWord ++ tailWord_7438841) baseStart_7438841 baseEnd_7438841 := by
    simpa [prefixWord, tailWord_7438841, baseEnd_7438841] using wordTrace_append hprefix tailTrace_7438841
  have hstable : (prefixWord ++ tailWord_7438841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438841).length < 2 ^ (prefixWord ++ tailWord_7438841).sum := by decide
  have hdescent : baseEnd_7438841 < baseStart_7438841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438874 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_7438874 : Nat := 118140960795 + 7438874 * 2 ^ 59
def prefixEnd_7438874 : Nat := 4983230072969 + 3 ^ 40 * 7438874 * 2
def baseEnd_7438874 : Nat := 3819717890234033604964247

theorem tailTrace_7438874 : CollatzResearch.WordTrace tailWord_7438874 prefixEnd_7438874 3819717890234033604964247 := by
  unfold tailWord_7438874
  simp only [CollatzResearch.WordTrace]
  refine ⟨67829506113059357844484919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180878682968158287585293117 67829506113059357844484919)
  ·
    refine ⟨101744259169589036766727379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67829506113059357844484919 101744259169589036766727379)
    ·
      refine ⟨152616388754383555150091069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101744259169589036766727379 152616388754383555150091069)
      ·
        refine ⟨57231145782893833181284151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152616388754383555150091069 57231145782893833181284151)
        ·
          refine ⟨85846718674340749771926227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57231145782893833181284151 85846718674340749771926227)
          ·
            refine ⟨128770078011511124657889341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85846718674340749771926227 128770078011511124657889341)
            ·
              refine ⟨48288779254316671746708503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128770078011511124657889341 48288779254316671746708503)
              ·
                refine ⟨72433168881475007620062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48288779254316671746708503 72433168881475007620062755)
                ·
                  refine ⟨108649753322212511430094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72433168881475007620062755 108649753322212511430094133)
                  ·
                    refine ⟨10185914373957422946571325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108649753322212511430094133 10185914373957422946571325)
                    ·
                      refine ⟨3819717890234033604964247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10185914373957422946571325 3819717890234033604964247)
                      ·
                        rfl

theorem cell23_7438874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_7438874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438874 prefixEnd_7438874 := by exact prefixLift 7438874
  have htrace : WordTrace (prefixWord ++ tailWord_7438874) baseStart_7438874 baseEnd_7438874 := by
    simpa [prefixWord, tailWord_7438874, baseEnd_7438874] using wordTrace_append hprefix tailTrace_7438874
  have hstable : (prefixWord ++ tailWord_7438874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438874).length < 2 ^ (prefixWord ++ tailWord_7438874).sum := by decide
  have hdescent : baseEnd_7438874 < baseStart_7438874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438951 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_7438951 : Nat := 118140960795 + 7438951 * 2 ^ 59
def prefixEnd_7438951 : Nat := 4983230072969 + 3 ^ 40 * 7438951 * 2
def baseEnd_7438951 : Nat := 3819757428244429803701393

theorem tailTrace_7438951 : CollatzResearch.WordTrace tailWord_7438951 prefixEnd_7438951 3819757428244429803701393 := by
  unfold tailWord_7438951
  simp only [CollatzResearch.WordTrace]
  refine ⟨271320832872958473528492707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180880555248638982352328471 271320832872958473528492707)
  ·
    refine ⟨406981249309437710292739061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271320832872958473528492707 406981249309437710292739061)
    ·
      refine ⟨38154492122759785339944287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406981249309437710292739061 38154492122759785339944287)
      ·
        refine ⟨57231738184139678009916431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38154492122759785339944287 57231738184139678009916431)
        ·
          refine ⟨85847607276209517014874647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57231738184139678009916431 85847607276209517014874647)
          ·
            refine ⟨128771410914314275522311971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85847607276209517014874647 128771410914314275522311971)
            ·
              refine ⟨193157116371471413283467957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128771410914314275522311971 193157116371471413283467957)
              ·
                refine ⟨18108479659825444995325121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193157116371471413283467957 18108479659825444995325121)
                ·
                  refine ⟨13581359744869083746493841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18108479659825444995325121 13581359744869083746493841)
                  ·
                    refine ⟨10186019808651812809870381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13581359744869083746493841 10186019808651812809870381)
                    ·
                      refine ⟨3819757428244429803701393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10186019808651812809870381 3819757428244429803701393)
                      ·
                        rfl

theorem cell23_7438951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_7438951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438951 prefixEnd_7438951 := by exact prefixLift 7438951
  have htrace : WordTrace (prefixWord ++ tailWord_7438951) baseStart_7438951 baseEnd_7438951 := by
    simpa [prefixWord, tailWord_7438951, baseEnd_7438951] using wordTrace_append hprefix tailTrace_7438951
  have hstable : (prefixWord ++ tailWord_7438951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438951).length < 2 ^ (prefixWord ++ tailWord_7438951).sum := by decide
  have hdescent : baseEnd_7438951 < baseStart_7438951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7438954 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_7438954 : Nat := 118140960795 + 7438954 * 2 ^ 59
def prefixEnd_7438954 : Nat := 4983230072969 + 3 ^ 40 * 7438954 * 2
def baseEnd_7438954 : Nat := 424417663187377032440431

theorem tailTrace_7438954 : CollatzResearch.WordTrace tailWord_7438954 prefixEnd_7438954 424417663187377032440431 := by
  unfold tailWord_7438954
  simp only [CollatzResearch.WordTrace]
  refine ⟨67830235572986901260212979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180880628194631736693901277 67830235572986901260212979)
  ·
    refine ⟨101745353359480351890319469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67830235572986901260212979 101745353359480351890319469)
    ·
      refine ⟨38154507509805131958869801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101745353359480351890319469 38154507509805131958869801)
      ·
        refine ⟨28615880632353848969152351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38154507509805131958869801 28615880632353848969152351)
        ·
          refine ⟨42923820948530773453728527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28615880632353848969152351 42923820948530773453728527)
          ·
            refine ⟨64385731422796160180592791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42923820948530773453728527 64385731422796160180592791)
            ·
              refine ⟨96578597134194240270889187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64385731422796160180592791 96578597134194240270889187)
              ·
                refine ⟨144867895701291360406333781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96578597134194240270889187 144867895701291360406333781)
                ·
                  refine ⟨424417663187377032440431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144867895701291360406333781 424417663187377032440431)
                  ·
                    rfl

theorem cell23_7438954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_7438954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7438954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7438954 prefixEnd_7438954 := by exact prefixLift 7438954
  have htrace : WordTrace (prefixWord ++ tailWord_7438954) baseStart_7438954 baseEnd_7438954 := by
    simpa [prefixWord, tailWord_7438954, baseEnd_7438954] using wordTrace_append hprefix tailTrace_7438954
  have hstable : (prefixWord ++ tailWord_7438954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7438954).length < 2 ^ (prefixWord ++ tailWord_7438954).sum := by decide
  have hdescent : baseEnd_7438954 < baseStart_7438954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7438954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439048 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 2, 4]
def baseStart_7439048 : Nat := 118140960795 + 7439048 * 2 ^ 59
def prefixEnd_7439048 : Nat := 4983230072969 + 3 ^ 40 * 7439048 * 2
def baseEnd_7439048 : Nat := 1273269078622638641396149

theorem tailTrace_7439048 : CollatzResearch.WordTrace tailWord_7439048 prefixEnd_7439048 1273269078622638641396149 := by
  unfold tailWord_7439048
  simp only [CollatzResearch.WordTrace]
  refine ⟨135662185376803529547386899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180882913835738039396515865 135662185376803529547386899)
  ·
    refine ⟨203493278065205294321080349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135662185376803529547386899 203493278065205294321080349)
    ·
      refine ⟨76309979274451985370405131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203493278065205294321080349 76309979274451985370405131)
      ·
        refine ⟨114464968911677978055607697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76309979274451985370405131 114464968911677978055607697)
        ·
          refine ⟨85848726683758483541705773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114464968911677978055607697 85848726683758483541705773)
          ·
            refine ⟨32193272506409431328139665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85848726683758483541705773 32193272506409431328139665)
            ·
              refine ⟨24144954379807073496104749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32193272506409431328139665 24144954379807073496104749)
              ·
                refine ⟨9054357892427652561039281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24144954379807073496104749 9054357892427652561039281)
                ·
                  refine ⟨6790768419320739420779461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9054357892427652561039281 6790768419320739420779461)
                  ·
                    refine ⟨1273269078622638641396149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6790768419320739420779461 1273269078622638641396149)
                    ·
                      rfl

theorem cell23_7439048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_7439048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439048 prefixEnd_7439048 := by exact prefixLift 7439048
  have htrace : WordTrace (prefixWord ++ tailWord_7439048) baseStart_7439048 baseEnd_7439048 := by
    simpa [prefixWord, tailWord_7439048, baseEnd_7439048] using wordTrace_append hprefix tailTrace_7439048
  have hstable : (prefixWord ++ tailWord_7439048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439048).length < 2 ^ (prefixWord ++ tailWord_7439048).sum := by decide
  have hdescent : baseEnd_7439048 < baseStart_7439048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439075 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7439075 : Nat := 118140960795 + 7439075 * 2 ^ 59
def prefixEnd_7439075 : Nat := 4983230072969 + 3 ^ 40 * 7439075 * 2
def baseEnd_7439075 : Nat := 3819821099845587318550823

theorem tailTrace_7439075 : CollatzResearch.WordTrace tailWord_7439075 prefixEnd_7439075 3819821099845587318550823 := by
  unfold tailWord_7439075
  simp only [CollatzResearch.WordTrace]
  refine ⟨271325355524509242706006679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180883570349672828470671119 271325355524509242706006679)
  ·
    refine ⟨406988033286763864059010019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271325355524509242706006679 406988033286763864059010019)
    ·
      refine ⟨610482049930145796088515029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406988033286763864059010019 610482049930145796088515029)
      ·
        refine ⟨14308173045237792095824571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 610482049930145796088515029 14308173045237792095824571)
        ·
          refine ⟨21462259567856688143736857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14308173045237792095824571 21462259567856688143736857)
          ·
            refine ⟨16096694675892516107802643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21462259567856688143736857 16096694675892516107802643)
            ·
              refine ⟨24145042013838774161703965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16096694675892516107802643 24145042013838774161703965)
              ·
                refine ⟨9054390755189540310638987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24145042013838774161703965 9054390755189540310638987)
                ·
                  refine ⟨13581586132784310465958481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9054390755189540310638987 13581586132784310465958481)
                  ·
                    refine ⟨10186189599588232849468861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13581586132784310465958481 10186189599588232849468861)
                    ·
                      refine ⟨3819821099845587318550823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10186189599588232849468861 3819821099845587318550823)
                      ·
                        rfl

theorem cell23_7439075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7439075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439075 prefixEnd_7439075 := by exact prefixLift 7439075
  have htrace : WordTrace (prefixWord ++ tailWord_7439075) baseStart_7439075 baseEnd_7439075 := by
    simpa [prefixWord, tailWord_7439075, baseEnd_7439075] using wordTrace_append hprefix tailTrace_7439075
  have hstable : (prefixWord ++ tailWord_7439075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439075).length < 2 ^ (prefixWord ++ tailWord_7439075).sum := by decide
  have hdescent : baseEnd_7439075 < baseStart_7439075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439088 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 4, 1, 3]
def baseStart_7439088 : Nat := 118140960795 + 7439088 * 2 ^ 59
def prefixEnd_7439088 : Nat := 4983230072969 + 3 ^ 40 * 7439088 * 2
def baseEnd_7439088 : Nat := 3819827775094095767688263

theorem tailTrace_7439088 : CollatzResearch.WordTrace tailWord_7439088 prefixEnd_7439088 3819827775094095767688263 := by
  unfold tailWord_7439088
  simp only [CollatzResearch.WordTrace]
  refine ⟨135662914836731072963114959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180883886448974763950819945 135662914836731072963114959)
  ·
    refine ⟨203494372255096609444672439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135662914836731072963114959 203494372255096609444672439)
    ·
      refine ⟨305241558382644914167008659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203494372255096609444672439 305241558382644914167008659)
      ·
        refine ⟨457862337573967371250512989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305241558382644914167008659 457862337573967371250512989)
        ·
          refine ⟨171698376590237764218942371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457862337573967371250512989 171698376590237764218942371)
          ·
            refine ⟨257547564885356646328413557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171698376590237764218942371 257547564885356646328413557)
            ·
              refine ⟨24145084208002185593288771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257547564885356646328413557 24145084208002185593288771)
              ·
                refine ⟨36217626312003278389933157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24145084208002185593288771 36217626312003278389933157)
                ·
                  refine ⟨6790804933500614698112467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36217626312003278389933157 6790804933500614698112467)
                  ·
                    refine ⟨10186207400250922047168701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6790804933500614698112467 10186207400250922047168701)
                    ·
                      refine ⟨3819827775094095767688263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10186207400250922047168701 3819827775094095767688263)
                      ·
                        rfl

theorem cell23_7439088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_7439088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439088 prefixEnd_7439088 := by exact prefixLift 7439088
  have htrace : WordTrace (prefixWord ++ tailWord_7439088) baseStart_7439088 baseEnd_7439088 := by
    simpa [prefixWord, tailWord_7439088, baseEnd_7439088] using wordTrace_append hprefix tailTrace_7439088
  have hstable : (prefixWord ++ tailWord_7439088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439088).length < 2 ^ (prefixWord ++ tailWord_7439088).sum := by decide
  have hdescent : baseEnd_7439088 < baseStart_7439088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439092 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_7439092 : Nat := 118140960795 + 7439092 * 2 ^ 59
def prefixEnd_7439092 : Nat := 4983230072969 + 3 ^ 40 * 7439092 * 2
def baseEnd_7439092 : Nat := 3819829829016713752038245

theorem tailTrace_7439092 : CollatzResearch.WordTrace tailWord_7439092 prefixEnd_7439092 3819829829016713752038245 := by
  unfold tailWord_7439092
  simp only [CollatzResearch.WordTrace]
  refine ⟨135662987782723827304687765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180883983710298436406250353 135662987782723827304687765)
  ·
    refine ⟨6359202552315179404907239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135662987782723827304687765 6359202552315179404907239)
    ·
      refine ⟨9538803828472769107360859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6359202552315179404907239 9538803828472769107360859)
      ·
        refine ⟨14308205742709153661041289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9538803828472769107360859 14308205742709153661041289)
        ·
          refine ⟨10731154307031865245780967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14308205742709153661041289 10731154307031865245780967)
          ·
            refine ⟨16096731460547797868671451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731154307031865245780967 16096731460547797868671451)
            ·
              refine ⟨24145097190821696803007177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16096731460547797868671451 24145097190821696803007177)
              ·
                refine ⟨18108822893116272602255383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24145097190821696803007177 18108822893116272602255383)
                ·
                  refine ⟨27163234339674408903383075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18108822893116272602255383 27163234339674408903383075)
                  ·
                    refine ⟨40744851509511613355074613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27163234339674408903383075 40744851509511613355074613)
                    ·
                      refine ⟨3819829829016713752038245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40744851509511613355074613 3819829829016713752038245)
                      ·
                        rfl

theorem cell23_7439092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_7439092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439092 prefixEnd_7439092 := by exact prefixLift 7439092
  have htrace : WordTrace (prefixWord ++ tailWord_7439092) baseStart_7439092 baseEnd_7439092 := by
    simpa [prefixWord, tailWord_7439092, baseEnd_7439092] using wordTrace_append hprefix tailTrace_7439092
  have hstable : (prefixWord ++ tailWord_7439092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439092).length < 2 ^ (prefixWord ++ tailWord_7439092).sum := by decide
  have hdescent : baseEnd_7439092 < baseStart_7439092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439098 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2]
def baseStart_7439098 : Nat := 118140960795 + 7439098 * 2 ^ 59
def prefixEnd_7439098 : Nat := 4983230072969 + 3 ^ 40 * 7439098 * 2
def baseEnd_7439098 : Nat := 3819832909900640728563217

theorem tailTrace_7439098 : CollatzResearch.WordTrace tailWord_7439098 prefixEnd_7439098 3819832909900640728563217 := by
  unfold tailWord_7439098
  simp only [CollatzResearch.WordTrace]
  refine ⟨67831548600856479408523487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180884129602283945089395965 67831548600856479408523487)
  ·
    refine ⟨101747322901284719112785231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67831548600856479408523487 101747322901284719112785231)
    ·
      refine ⟨152620984351927078669177847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101747322901284719112785231 152620984351927078669177847)
      ·
        refine ⟨228931476527890618003766771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152620984351927078669177847 228931476527890618003766771)
        ·
          refine ⟨343397214791835927005650157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228931476527890618003766771 343397214791835927005650157)
          ·
            refine ⟨128773955546938472627118809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343397214791835927005650157 128773955546938472627118809)
            ·
              refine ⟨96580466660203854470339107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128773955546938472627118809 96580466660203854470339107)
              ·
                refine ⟨144870699990305781705508661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96580466660203854470339107 144870699990305781705508661)
                ·
                  refine ⟨13581628124091167034891437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144870699990305781705508661 13581628124091167034891437)
                  ·
                    refine ⟨5093110546534187638084289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13581628124091167034891437 5093110546534187638084289)
                    ·
                      refine ⟨3819832909900640728563217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093110546534187638084289 3819832909900640728563217)
                      ·
                        rfl

theorem cell23_7439098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_7439098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439098 prefixEnd_7439098 := by exact prefixLift 7439098
  have htrace : WordTrace (prefixWord ++ tailWord_7439098) baseStart_7439098 baseEnd_7439098 := by
    simpa [prefixWord, tailWord_7439098, baseEnd_7439098] using wordTrace_append hprefix tailTrace_7439098
  have hstable : (prefixWord ++ tailWord_7439098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439098).length < 2 ^ (prefixWord ++ tailWord_7439098).sum := by decide
  have hdescent : baseEnd_7439098 < baseStart_7439098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439128 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 3, 4, 2]
def baseStart_7439128 : Nat := 118140960795 + 7439128 * 2 ^ 59
def prefixEnd_7439128 : Nat := 4983230072969 + 3 ^ 40 * 7439128 * 2
def baseEnd_7439128 : Nat := 3819848314320275611188079

theorem tailTrace_7439128 : CollatzResearch.WordTrace tailWord_7439128 prefixEnd_7439128 3819848314320275611188079 := by
  unfold tailWord_7439128
  simp only [CollatzResearch.WordTrace]
  refine ⟨135663644296658616378843019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180884859062211488505124025 135663644296658616378843019)
  ·
    refine ⟨203495466444987924568264529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135663644296658616378843019 203495466444987924568264529)
    ·
      refine ⟨152621599833740943426198397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203495466444987924568264529 152621599833740943426198397)
      ·
        refine ⟨57233099937652853784824399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152621599833740943426198397 57233099937652853784824399)
        ·
          refine ⟨85849649906479280677236599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57233099937652853784824399 85849649906479280677236599)
          ·
            refine ⟨128774474859718921015854899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85849649906479280677236599 128774474859718921015854899)
            ·
              refine ⟨193161712289578381523782349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128774474859718921015854899 193161712289578381523782349)
              ·
                refine ⟨72435642108591893071418381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193161712289578381523782349 72435642108591893071418381)
                ·
                  refine ⟨27163365790721959901781893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72435642108591893071418381 27163365790721959901781893)
                  ·
                    refine ⟨5093131085760367481584105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27163365790721959901781893 5093131085760367481584105)
                    ·
                      refine ⟨3819848314320275611188079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093131085760367481584105 3819848314320275611188079)
                      ·
                        rfl

theorem cell23_7439128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_7439128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439128 prefixEnd_7439128 := by exact prefixLift 7439128
  have htrace : WordTrace (prefixWord ++ tailWord_7439128) baseStart_7439128 baseEnd_7439128 := by
    simpa [prefixWord, tailWord_7439128, baseEnd_7439128] using wordTrace_append hprefix tailTrace_7439128
  have hstable : (prefixWord ++ tailWord_7439128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439128).length < 2 ^ (prefixWord ++ tailWord_7439128).sum := by decide
  have hdescent : baseEnd_7439128 < baseStart_7439128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439156 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_7439156 : Nat := 118140960795 + 7439156 * 2 ^ 59
def prefixEnd_7439156 : Nat := 4983230072969 + 3 ^ 40 * 7439156 * 2
def baseEnd_7439156 : Nat := 3819862691778601501637951

theorem tailTrace_7439156 : CollatzResearch.WordTrace tailWord_7439156 prefixEnd_7439156 3819862691778601501637951 := by
  unfold tailWord_7439156
  simp only [CollatzResearch.WordTrace]
  refine ⟨135664154918607896769852661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180885539891477195693136881 135664154918607896769852661)
  ·
    refine ⟨12718514523619490322173687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135664154918607896769852661 12718514523619490322173687)
    ·
      refine ⟨19077771785429235483260531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12718514523619490322173687 19077771785429235483260531)
      ·
        refine ⟨28616657678143853224890797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19077771785429235483260531 28616657678143853224890797)
        ·
          refine ⟨10731246629303944959334049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28616657678143853224890797 10731246629303944959334049)
          ·
            refine ⟨8048434971977958719500537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10731246629303944959334049 8048434971977958719500537)
            ·
              refine ⟨6036326228983469039625403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8048434971977958719500537 6036326228983469039625403)
              ·
                refine ⟨9054489343475203559438105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036326228983469039625403 9054489343475203559438105)
                ·
                  refine ⟨6790867007606402669578579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9054489343475203559438105 6790867007606402669578579)
                  ·
                    refine ⟨10186300511409604004367869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6790867007606402669578579 10186300511409604004367869)
                    ·
                      refine ⟨3819862691778601501637951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10186300511409604004367869 3819862691778601501637951)
                      ·
                        rfl

theorem cell23_7439156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_7439156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439156 prefixEnd_7439156 := by exact prefixLift 7439156
  have htrace : WordTrace (prefixWord ++ tailWord_7439156) baseStart_7439156 baseEnd_7439156 := by
    simpa [prefixWord, tailWord_7439156, baseEnd_7439156] using wordTrace_append hprefix tailTrace_7439156
  have hstable : (prefixWord ++ tailWord_7439156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439156).length < 2 ^ (prefixWord ++ tailWord_7439156).sum := by decide
  have hdescent : baseEnd_7439156 < baseStart_7439156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439166 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_7439166 : Nat := 118140960795 + 7439166 * 2 ^ 59
def prefixEnd_7439166 : Nat := 4983230072969 + 3 ^ 40 * 7439166 * 2
def baseEnd_7439166 : Nat := 3819867826585146462512905

theorem tailTrace_7439166 : CollatzResearch.WordTrace tailWord_7439166 prefixEnd_7439166 3819867826585146462512905 := by
  unfold tailWord_7439166
  simp only [CollatzResearch.WordTrace]
  refine ⟨33916084320897445655946169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180885783044786376831712901 33916084320897445655946169)
  ·
    refine ⟨25437063240673084241959627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33916084320897445655946169 25437063240673084241959627)
    ·
      refine ⟨38155594861009626362939441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25437063240673084241959627 38155594861009626362939441)
      ·
        refine ⟨28616696145757219772204581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38155594861009626362939441 28616696145757219772204581)
        ·
          refine ⟨5365630527329478707288359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28616696145757219772204581 5365630527329478707288359)
          ·
            refine ⟨8048445790994218060932539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5365630527329478707288359 8048445790994218060932539)
            ·
              refine ⟨12072668686491327091398809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048445790994218060932539 12072668686491327091398809)
              ·
                refine ⟨9054501514868495318549107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12072668686491327091398809 9054501514868495318549107)
                ·
                  refine ⟨13581752272302742977823661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9054501514868495318549107 13581752272302742977823661)
                  ·
                    refine ⟨5093157102113528616683873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13581752272302742977823661 5093157102113528616683873)
                    ·
                      refine ⟨3819867826585146462512905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093157102113528616683873 3819867826585146462512905)
                      ·
                        rfl

theorem cell23_7439166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_7439166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439166 prefixEnd_7439166 := by exact prefixLift 7439166
  have htrace : WordTrace (prefixWord ++ tailWord_7439166) baseStart_7439166 baseEnd_7439166 := by
    simpa [prefixWord, tailWord_7439166, baseEnd_7439166] using wordTrace_append hprefix tailTrace_7439166
  have hstable : (prefixWord ++ tailWord_7439166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439166).length < 2 ^ (prefixWord ++ tailWord_7439166).sum := by decide
  have hdescent : baseEnd_7439166 < baseStart_7439166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439202 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_7439202 : Nat := 118140960795 + 7439202 * 2 ^ 59
def prefixEnd_7439202 : Nat := 4983230072969 + 3 ^ 40 * 7439202 * 2
def baseEnd_7439202 : Nat := 424431812432078702406971

theorem tailTrace_7439202 : CollatzResearch.WordTrace tailWord_7439202 prefixEnd_7439202 424431812432078702406971 := by
  unfold tailWord_7439202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67832496898762285848969965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180886658396699428930586573 67832496898762285848969965)
  ·
    refine ⟨25437186337035857193363737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67832496898762285848969965 25437186337035857193363737)
    ·
      refine ⟨19077889752776892895022803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25437186337035857193363737 19077889752776892895022803)
      ·
        refine ⟨28616834629165339342534205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19077889752776892895022803 28616834629165339342534205)
        ·
          refine ⟨10731312985937002253450327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28616834629165339342534205 10731312985937002253450327)
          ·
            refine ⟨16096969478905503380175491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731312985937002253450327 16096969478905503380175491)
            ·
              refine ⟨24145454218358255070263237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16096969478905503380175491 24145454218358255070263237)
              ·
                refine ⟨4527272665942172825674357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24145454218358255070263237 4527272665942172825674357)
                ·
                  refine ⟨424431812432078702406971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4527272665942172825674357 424431812432078702406971)
                  ·
                    rfl

theorem cell23_7439202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_7439202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439202 prefixEnd_7439202 := by exact prefixLift 7439202
  have htrace : WordTrace (prefixWord ++ tailWord_7439202) baseStart_7439202 baseEnd_7439202 := by
    simpa [prefixWord, tailWord_7439202, baseEnd_7439202] using wordTrace_append hprefix tailTrace_7439202
  have hstable : (prefixWord ++ tailWord_7439202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439202).length < 2 ^ (prefixWord ++ tailWord_7439202).sum := by decide
  have hdescent : baseEnd_7439202 < baseStart_7439202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439208 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_7439208 : Nat := 118140960795 + 7439208 * 2 ^ 59
def prefixEnd_7439208 : Nat := 4983230072969 + 3 ^ 40 * 7439208 * 2
def baseEnd_7439208 : Nat := 3819889392772635298187711

theorem tailTrace_7439208 : CollatzResearch.WordTrace tailWord_7439208 prefixEnd_7439208 3819889392772635298187711 := by
  unfold tailWord_7439208
  simp only [CollatzResearch.WordTrace]
  refine ⟨135665103216513703210299139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180886804288684937613732185 135665103216513703210299139)
  ·
    refine ⟨203497654824770554815448709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135665103216513703210299139 203497654824770554815448709)
    ·
      refine ⟨38155810279644479027896633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203497654824770554815448709 38155810279644479027896633)
      ·
        refine ⟨28616857709733359270922475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38155810279644479027896633 28616857709733359270922475)
        ·
          refine ⟨42925286564600038906383713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28616857709733359270922475 42925286564600038906383713)
          ·
            refine ⟨32193964923450029179787785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42925286564600038906383713 32193964923450029179787785)
            ·
              refine ⟨24145473692587521884840839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32193964923450029179787785 24145473692587521884840839)
              ·
                refine ⟨36218210538881282827261259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24145473692587521884840839 36218210538881282827261259)
                ·
                  refine ⟨54327315808321924240891889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36218210538881282827261259 54327315808321924240891889)
                  ·
                    refine ⟨40745486856241443180668917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54327315808321924240891889 40745486856241443180668917)
                    ·
                      refine ⟨3819889392772635298187711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40745486856241443180668917 3819889392772635298187711)
                      ·
                        rfl

theorem cell23_7439208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_7439208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439208 prefixEnd_7439208 := by exact prefixLift 7439208
  have htrace : WordTrace (prefixWord ++ tailWord_7439208) baseStart_7439208 baseEnd_7439208 := by
    simpa [prefixWord, tailWord_7439208, baseEnd_7439208] using wordTrace_append hprefix tailTrace_7439208
  have hstable : (prefixWord ++ tailWord_7439208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439208).length < 2 ^ (prefixWord ++ tailWord_7439208).sum := by decide
  have hdescent : baseEnd_7439208 < baseStart_7439208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439218 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7439218 : Nat := 118140960795 + 7439218 * 2 ^ 59
def prefixEnd_7439218 : Nat := 4983230072969 + 3 ^ 40 * 7439218 * 2
def baseEnd_7439218 : Nat := 3819894527579180259062665

theorem tailTrace_7439218 : CollatzResearch.WordTrace tailWord_7439218 prefixEnd_7439218 3819894527579180259062665 := by
  unfold tailWord_7439218
  simp only [CollatzResearch.WordTrace]
  refine ⟨67832642790747794532115577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180887047441994118752308205 67832642790747794532115577)
  ·
    refine ⟨50874482093060845899086683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67832642790747794532115577 50874482093060845899086683)
    ·
      refine ⟨76311723139591268848630025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50874482093060845899086683 76311723139591268848630025)
      ·
        refine ⟨57233792354693451636472519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76311723139591268848630025 57233792354693451636472519)
        ·
          refine ⟨85850688532040177454708779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57233792354693451636472519 85850688532040177454708779)
          ·
            refine ⟨128776032798060266182063169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85850688532040177454708779 128776032798060266182063169)
            ·
              refine ⟨96582024598545199636547377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128776032798060266182063169 96582024598545199636547377)
              ·
                refine ⟨72436518448908899727410533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96582024598545199636547377 72436518448908899727410533)
                ·
                  refine ⟨13581847209170418698889475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72436518448908899727410533 13581847209170418698889475)
                  ·
                    refine ⟨20372770813755628048334213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13581847209170418698889475 20372770813755628048334213)
                    ·
                      refine ⟨3819894527579180259062665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20372770813755628048334213 3819894527579180259062665)
                      ·
                        rfl

theorem cell23_7439218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7439218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439218 prefixEnd_7439218 := by exact prefixLift 7439218
  have htrace : WordTrace (prefixWord ++ tailWord_7439218) baseStart_7439218 baseEnd_7439218 := by
    simpa [prefixWord, tailWord_7439218, baseEnd_7439218] using wordTrace_append hprefix tailTrace_7439218
  have hstable : (prefixWord ++ tailWord_7439218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439218).length < 2 ^ (prefixWord ++ tailWord_7439218).sum := by decide
  have hdescent : baseEnd_7439218 < baseStart_7439218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439328 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_7439328 : Nat := 118140960795 + 7439328 * 2 ^ 59
def prefixEnd_7439328 : Nat := 4983230072969 + 3 ^ 40 * 7439328 * 2
def baseEnd_7439328 : Nat := 3819951010451174828687159

theorem tailTrace_7439328 : CollatzResearch.WordTrace tailWord_7439328 prefixEnd_7439328 3819951010451174828687159 := by
  unfold tailWord_7439328
  simp only [CollatzResearch.WordTrace]
  refine ⟨135667291596296333457483319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180889722128395111276644425 135667291596296333457483319)
  ·
    refine ⟨203500937394444500186224979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135667291596296333457483319 203500937394444500186224979)
    ·
      refine ⟨305251406091666750279337469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203500937394444500186224979 305251406091666750279337469)
      ·
        refine ⟨114469277284375031354751551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305251406091666750279337469 114469277284375031354751551)
        ·
          refine ⟨171703915926562547032127327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114469277284375031354751551 171703915926562547032127327)
          ·
            refine ⟨257555873889843820548190991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171703915926562547032127327 257555873889843820548190991)
            ·
              refine ⟨386333810834765730822286487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257555873889843820548190991 386333810834765730822286487)
              ·
                refine ⟨579500716252148596233429731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386333810834765730822286487 579500716252148596233429731)
                ·
                  refine ⟨869251074378222894350144597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579500716252148596233429731 869251074378222894350144597)
                  ·
                    refine ⟨10186536027869799543165757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 869251074378222894350144597 10186536027869799543165757)
                    ·
                      refine ⟨3819951010451174828687159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10186536027869799543165757 3819951010451174828687159)
                      ·
                        rfl

theorem cell23_7439328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_7439328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439328 prefixEnd_7439328 := by exact prefixLift 7439328
  have htrace : WordTrace (prefixWord ++ tailWord_7439328) baseStart_7439328 baseEnd_7439328 := by
    simpa [prefixWord, tailWord_7439328, baseEnd_7439328] using wordTrace_append hprefix tailTrace_7439328
  have hstable : (prefixWord ++ tailWord_7439328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439328).length < 2 ^ (prefixWord ++ tailWord_7439328).sum := by decide
  have hdescent : baseEnd_7439328 < baseStart_7439328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439342 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_7439342 : Nat := 118140960795 + 7439342 * 2 ^ 59
def prefixEnd_7439342 : Nat := 4983230072969 + 3 ^ 40 * 7439342 * 2
def baseEnd_7439342 : Nat := 3819958199180337773912095

theorem tailTrace_7439342 : CollatzResearch.WordTrace tailWord_7439342 prefixEnd_7439342 3819958199180337773912095 := by
  unfold tailWord_7439342
  simp only [CollatzResearch.WordTrace]
  refine ⟨33916886726817743413247035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180890062543027964870650853 33916886726817743413247035)
  ·
    refine ⟨50875330090226615119870553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33916886726817743413247035 50875330090226615119870553)
    ·
      refine ⟨38156497567669961339902915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50875330090226615119870553 38156497567669961339902915)
      ·
        refine ⟨57234746351504942009854373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38156497567669961339902915 57234746351504942009854373)
        ·
          refine ⟨10731514940907176626847695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57234746351504942009854373 10731514940907176626847695)
          ·
            refine ⟨16097272411360764940271543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731514940907176626847695 16097272411360764940271543)
            ·
              refine ⟨24145908617041147410407315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16097272411360764940271543 24145908617041147410407315)
              ·
                refine ⟨36218862925561721115610973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24145908617041147410407315 36218862925561721115610973)
                ·
                  refine ⟨13582073597085645418354115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36218862925561721115610973 13582073597085645418354115)
                  ·
                    refine ⟨20373110395628468127531173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13582073597085645418354115 20373110395628468127531173)
                    ·
                      refine ⟨3819958199180337773912095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20373110395628468127531173 3819958199180337773912095)
                      ·
                        rfl

theorem cell23_7439342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_7439342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439342 prefixEnd_7439342 := by exact prefixLift 7439342
  have htrace : WordTrace (prefixWord ++ tailWord_7439342) baseStart_7439342 baseEnd_7439342 := by
    simpa [prefixWord, tailWord_7439342, baseEnd_7439342] using wordTrace_append hprefix tailTrace_7439342
  have hstable : (prefixWord ++ tailWord_7439342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439342).length < 2 ^ (prefixWord ++ tailWord_7439342).sum := by decide
  have hdescent : baseEnd_7439342 < baseStart_7439342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439346 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7439346 : Nat := 118140960795 + 7439346 * 2 ^ 59
def prefixEnd_7439346 : Nat := 4983230072969 + 3 ^ 40 * 7439346 * 2
def baseEnd_7439346 : Nat := 3819960253102955758262077

theorem tailTrace_7439346 : CollatzResearch.WordTrace tailWord_7439346 prefixEnd_7439346 3819960253102955758262077 := by
  unfold tailWord_7439346
  simp only [CollatzResearch.WordTrace]
  refine ⟨67833809926631863997280473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180890159804351637326081261 67833809926631863997280473)
  ·
    refine ⟨50875357444973897997960355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67833809926631863997280473 50875357444973897997960355)
    ·
      refine ⟨76313036167460846996940533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50875357444973897997960355 76313036167460846996940533)
      ·
        refine ⟨7154347140699454405963175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76313036167460846996940533 7154347140699454405963175)
        ·
          refine ⟨10731520711049181608944763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154347140699454405963175 10731520711049181608944763)
          ·
            refine ⟨16097281066573772413417145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731520711049181608944763 16097281066573772413417145)
            ·
              refine ⟨12072960799930329310062859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16097281066573772413417145 12072960799930329310062859)
              ·
                refine ⟨18109441199895493965094289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12072960799930329310062859 18109441199895493965094289)
                ·
                  refine ⟨13582080899921620473820717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18109441199895493965094289 13582080899921620473820717)
                  ·
                    refine ⟨5093280337470607677682769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13582080899921620473820717 5093280337470607677682769)
                    ·
                      refine ⟨3819960253102955758262077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093280337470607677682769 3819960253102955758262077)
                      ·
                        rfl

theorem cell23_7439346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7439346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439346 prefixEnd_7439346 := by exact prefixLift 7439346
  have htrace : WordTrace (prefixWord ++ tailWord_7439346) baseStart_7439346 baseEnd_7439346 := by
    simpa [prefixWord, tailWord_7439346, baseEnd_7439346] using wordTrace_append hprefix tailTrace_7439346
  have hstable : (prefixWord ++ tailWord_7439346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439346).length < 2 ^ (prefixWord ++ tailWord_7439346).sum := by decide
  have hdescent : baseEnd_7439346 < baseStart_7439346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439408 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_7439408 : Nat := 118140960795 + 7439408 * 2 ^ 59
def prefixEnd_7439408 : Nat := 4983230072969 + 3 ^ 40 * 7439408 * 2
def baseEnd_7439408 : Nat := 1273330696301178171895597

theorem tailTrace_7439408 : CollatzResearch.WordTrace tailWord_7439408 prefixEnd_7439408 1273330696301178171895597 := by
  unfold tailWord_7439408
  simp only [CollatzResearch.WordTrace]
  refine ⟨135668750516151420288939439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180891667354868560385252585 135668750516151420288939439)
  ·
    refine ⟨203503125774227130433409159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135668750516151420288939439 203503125774227130433409159)
    ·
      refine ⟨305254688661340695650113739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203503125774227130433409159 305254688661340695650113739)
      ·
        refine ⟨457882032992011043475170609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305254688661340695650113739 457882032992011043475170609)
        ·
          refine ⟨343411524744008282606377957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457882032992011043475170609 343411524744008282606377957)
          ·
            refine ⟨64389660889501552988695867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343411524744008282606377957 64389660889501552988695867)
            ·
              refine ⟨96584491334252329483043801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64389660889501552988695867 96584491334252329483043801)
              ·
                refine ⟨72438368500689247112282851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96584491334252329483043801 72438368500689247112282851)
                ·
                  refine ⟨108657552751033870668424277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72438368500689247112282851 108657552751033870668424277)
                  ·
                    refine ⟨1273330696301178171895597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108657552751033870668424277 1273330696301178171895597)
                    ·
                      rfl

theorem cell23_7439408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_7439408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439408 prefixEnd_7439408 := by exact prefixLift 7439408
  have htrace : WordTrace (prefixWord ++ tailWord_7439408) baseStart_7439408 baseEnd_7439408 := by
    simpa [prefixWord, tailWord_7439408, baseEnd_7439408] using wordTrace_append hprefix tailTrace_7439408
  have hstable : (prefixWord ++ tailWord_7439408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439408).length < 2 ^ (prefixWord ++ tailWord_7439408).sum := by decide
  have hdescent : baseEnd_7439408 < baseStart_7439408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439445 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7439445 : Nat := 118140960795 + 7439445 * 2 ^ 59
def prefixEnd_7439445 : Nat := 4983230072969 + 3 ^ 40 * 7439445 * 2
def baseEnd_7439445 : Nat := 3820011087687750870924121

theorem tailTrace_7439445 : CollatzResearch.WordTrace tailWord_7439445 prefixEnd_7439445 3820011087687750870924121 := by
  unfold tailWord_7439445
  simp only [CollatzResearch.WordTrace]
  refine ⟨271338850533168795896975789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180892567022112530597983859 271338850533168795896975789)
  ·
    refine ⟨101752068949938298461365921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271338850533168795896975789 101752068949938298461365921)
    ·
      refine ⟨76314051712453723846024441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101752068949938298461365921 76314051712453723846024441)
      ·
        refine ⟨57235538784340292884518331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76314051712453723846024441 57235538784340292884518331)
        ·
          refine ⟨85853308176510439326777497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57235538784340292884518331 85853308176510439326777497)
          ·
            refine ⟨64389981132382829495083123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85853308176510439326777497 64389981132382829495083123)
            ·
              refine ⟨96584971698574244242624685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64389981132382829495083123 96584971698574244242624685)
              ·
                refine ⟨36219364386965341590984257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96584971698574244242624685 36219364386965341590984257)
                ·
                  refine ⟨27164523290224006193238193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36219364386965341590984257 27164523290224006193238193)
                  ·
                    refine ⟨20373392467668004644928645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27164523290224006193238193 20373392467668004644928645)
                    ·
                      refine ⟨3820011087687750870924121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20373392467668004644928645 3820011087687750870924121)
                      ·
                        rfl

theorem cell23_7439445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7439445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439445 prefixEnd_7439445 := by exact prefixLift 7439445
  have htrace : WordTrace (prefixWord ++ tailWord_7439445) baseStart_7439445 baseEnd_7439445 := by
    simpa [prefixWord, tailWord_7439445, baseEnd_7439445] using wordTrace_append hprefix tailTrace_7439445
  have hstable : (prefixWord ++ tailWord_7439445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439445).length < 2 ^ (prefixWord ++ tailWord_7439445).sum := by decide
  have hdescent : baseEnd_7439445 < baseStart_7439445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439453 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7439453 : Nat := 118140960795 + 7439453 * 2 ^ 59
def prefixEnd_7439453 : Nat := 4983230072969 + 3 ^ 40 * 7439453 * 2
def baseEnd_7439453 : Nat := 3820015195532986839624085

theorem tailTrace_7439453 : CollatzResearch.WordTrace tailWord_7439453 prefixEnd_7439453 3820015195532986839624085 := by
  unfold tailWord_7439453
  simp only [CollatzResearch.WordTrace]
  refine ⟨271339142317139813263267013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180892761544759875508844675 271339142317139813263267013)
  ·
    refine ⟨50876089184463714986862565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271339142317139813263267013 50876089184463714986862565)
    ·
      refine ⟨9539266722086946560036731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50876089184463714986862565 9539266722086946560036731)
      ·
        refine ⟨14308900083130419840055097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9539266722086946560036731 14308900083130419840055097)
        ·
          refine ⟨10731675062347814880041323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14308900083130419840055097 10731675062347814880041323)
          ·
            refine ⟨16097512593521722320061985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731675062347814880041323 16097512593521722320061985)
            ·
              refine ⟨12073134445141291740046489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16097512593521722320061985 12073134445141291740046489)
              ·
                refine ⟨9054850833855968805034867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12073134445141291740046489 9054850833855968805034867)
                ·
                  refine ⟨13582276250783953207552301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9054850833855968805034867 13582276250783953207552301)
                  ·
                    refine ⟨5093353594043982452832113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13582276250783953207552301 5093353594043982452832113)
                    ·
                      refine ⟨3820015195532986839624085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093353594043982452832113 3820015195532986839624085)
                      ·
                        rfl

theorem cell23_7439453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7439453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439453 prefixEnd_7439453 := by exact prefixLift 7439453
  have htrace : WordTrace (prefixWord ++ tailWord_7439453) baseStart_7439453 baseEnd_7439453 := by
    simpa [prefixWord, tailWord_7439453, baseEnd_7439453] using wordTrace_append hprefix tailTrace_7439453
  have hstable : (prefixWord ++ tailWord_7439453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439453).length < 2 ^ (prefixWord ++ tailWord_7439453).sum := by decide
  have hdescent : baseEnd_7439453 < baseStart_7439453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439519 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 2, 5]
def baseStart_7439519 : Nat := 118140960795 + 7439519 * 2 ^ 59
def prefixEnd_7439519 : Nat := 4983230072969 + 3 ^ 40 * 7439519 * 2
def baseEnd_7439519 : Nat := 1273349695085394527132927

theorem tailTrace_7439519 : CollatzResearch.WordTrace tailWord_7439519 prefixEnd_7439519 1273349695085394527132927 := by
  unfold tailWord_7439519
  simp only [CollatzResearch.WordTrace]
  refine ⟨271341549534900706535169611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180894366356600471023446407 271341549534900706535169611)
  ·
    refine ⟨407012324302351059802754417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271341549534900706535169611 407012324302351059802754417)
    ·
      refine ⟨305259243226763294852065813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407012324302351059802754417 305259243226763294852065813)
      ·
        refine ⟨14309027026254529446190585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 305259243226763294852065813 14309027026254529446190585)
        ·
          refine ⟨10731770269690897084642939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14309027026254529446190585 10731770269690897084642939)
          ·
            refine ⟨16097655404536345626964409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731770269690897084642939 16097655404536345626964409)
            ·
              refine ⟨12073241553402259220223307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16097655404536345626964409 12073241553402259220223307)
              ·
                refine ⟨18109862330103388830334961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12073241553402259220223307 18109862330103388830334961)
                ·
                  refine ⟨13582396747577541622751221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18109862330103388830334961 13582396747577541622751221)
                  ·
                    refine ⟨1273349695085394527132927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13582396747577541622751221 1273349695085394527132927)
                    ·
                      rfl

theorem cell23_7439519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_7439519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439519 prefixEnd_7439519 := by exact prefixLift 7439519
  have htrace : WordTrace (prefixWord ++ tailWord_7439519) baseStart_7439519 baseEnd_7439519 := by
    simpa [prefixWord, tailWord_7439519, baseEnd_7439519] using wordTrace_append hprefix tailTrace_7439519
  have hstable : (prefixWord ++ tailWord_7439519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439519).length < 2 ^ (prefixWord ++ tailWord_7439519).sum := by decide
  have hdescent : baseEnd_7439519 < baseStart_7439519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439556 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_7439556 : Nat := 118140960795 + 7439556 * 2 ^ 59
def prefixEnd_7439556 : Nat := 4983230072969 + 3 ^ 40 * 7439556 * 2
def baseEnd_7439556 : Nat := 3820068084040399936636111

theorem tailTrace_7439556 : CollatzResearch.WordTrace tailWord_7439556 prefixEnd_7439556 3820068084040399936636111 := by
  unfold tailWord_7439556
  simp only [CollatzResearch.WordTrace]
  refine ⟨135671449517883330927133261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180895266023844441236177681 135671449517883330927133261)
  ·
    refine ⟨50876793569206249097674973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135671449517883330927133261 50876793569206249097674973)
    ·
      refine ⟨19078797588452343411628115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50876793569206249097674973 19078797588452343411628115)
      ·
        refine ⟨28618196382678515117442173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19078797588452343411628115 28618196382678515117442173)
        ·
          refine ⟨10731823643504443169040815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28618196382678515117442173 10731823643504443169040815)
          ·
            refine ⟨16097735465256664753561223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10731823643504443169040815 16097735465256664753561223)
            ·
              refine ⟨24146603197884997130341835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16097735465256664753561223 24146603197884997130341835)
              ·
                refine ⟨36219904796827495695512753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24146603197884997130341835 36219904796827495695512753)
                ·
                  refine ⟨27164928597620621771634565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36219904796827495695512753 27164928597620621771634565)
                  ·
                    refine ⟨5093424112053866582181481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27164928597620621771634565 5093424112053866582181481)
                    ·
                      refine ⟨3820068084040399936636111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093424112053866582181481 3820068084040399936636111)
                      ·
                        rfl

theorem cell23_7439556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_7439556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439556 prefixEnd_7439556 := by exact prefixLift 7439556
  have htrace : WordTrace (prefixWord ++ tailWord_7439556) baseStart_7439556 baseEnd_7439556 := by
    simpa [prefixWord, tailWord_7439556, baseEnd_7439556] using wordTrace_append hprefix tailTrace_7439556
  have hstable : (prefixWord ++ tailWord_7439556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439556).length < 2 ^ (prefixWord ++ tailWord_7439556).sum := by decide
  have hdescent : baseEnd_7439556 < baseStart_7439556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439562 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_7439562 : Nat := 118140960795 + 7439562 * 2 ^ 59
def prefixEnd_7439562 : Nat := 4983230072969 + 3 ^ 40 * 7439562 * 2
def baseEnd_7439562 : Nat := 424452351658258545906787

theorem tailTrace_7439562 : CollatzResearch.WordTrace tailWord_7439562 prefixEnd_7439562 424452351658258545906787 := by
  unfold tailWord_7439562
  simp only [CollatzResearch.WordTrace]
  refine ⟨67835779468436231219746235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180895411915829949919323293 67835779468436231219746235)
  ·
    refine ⟨101753669202654346829619353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67835779468436231219746235 101753669202654346829619353)
    ·
      refine ⟨76315251901990760122214515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101753669202654346829619353 76315251901990760122214515)
      ·
        refine ⟨114472877852986140183321773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76315251901990760122214515 114472877852986140183321773)
        ·
          refine ⟨42927329194869802568745665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114472877852986140183321773 42927329194869802568745665)
          ·
            refine ⟨32195496896152351926559249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42927329194869802568745665 32195496896152351926559249)
            ·
              refine ⟨24146622672114263944919437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32195496896152351926559249 24146622672114263944919437)
              ·
                refine ⟨9054983502042848979344789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24146622672114263944919437 9054983502042848979344789)
                ·
                  refine ⟨424452351658258545906787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9054983502042848979344789 424452351658258545906787)
                  ·
                    rfl

theorem cell23_7439562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_7439562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439562 prefixEnd_7439562 := by exact prefixLift 7439562
  have htrace : WordTrace (prefixWord ++ tailWord_7439562) baseStart_7439562 baseEnd_7439562 := by
    simpa [prefixWord, tailWord_7439562, baseEnd_7439562] using wordTrace_append hprefix tailTrace_7439562
  have hstable : (prefixWord ++ tailWord_7439562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439562).length < 2 ^ (prefixWord ++ tailWord_7439562).sum := by decide
  have hdescent : baseEnd_7439562 < baseStart_7439562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439576 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_7439576 : Nat := 118140960795 + 7439576 * 2 ^ 59
def prefixEnd_7439576 : Nat := 4983230072969 + 3 ^ 40 * 7439576 * 2
def baseEnd_7439576 : Nat := 3820078353653489858386019

theorem tailTrace_7439576 : CollatzResearch.WordTrace tailWord_7439576 prefixEnd_7439576 3820078353653489858386019 := by
  unfold tailWord_7439576
  simp only [CollatzResearch.WordTrace]
  refine ⟨135671814247847102634997291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180895752330462803513329721 135671814247847102634997291)
  ·
    refine ⟨203507721371770653952495937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135671814247847102634997291 203507721371770653952495937)
    ·
      refine ⟨152630791028827990464371953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203507721371770653952495937 152630791028827990464371953)
      ·
        refine ⟨114473093271620992848278965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152630791028827990464371953 114473093271620992848278965)
        ·
          refine ⟨10731852494214468079526153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114473093271620992848278965 10731852494214468079526153)
          ·
            refine ⟨8048889370660851059644615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10731852494214468079526153 8048889370660851059644615)
            ·
              refine ⟨12073334055991276589466923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048889370660851059644615 12073334055991276589466923)
              ·
                refine ⟨18110001083986914884200385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12073334055991276589466923 18110001083986914884200385)
                ·
                  refine ⟨13582500812990186163150289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18110001083986914884200385 13582500812990186163150289)
                  ·
                    refine ⟨10186875609742639622362717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13582500812990186163150289 10186875609742639622362717)
                    ·
                      refine ⟨3820078353653489858386019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10186875609742639622362717 3820078353653489858386019)
                      ·
                        rfl

theorem cell23_7439576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_7439576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439576 prefixEnd_7439576 := by exact prefixLift 7439576
  have htrace : WordTrace (prefixWord ++ tailWord_7439576) baseStart_7439576 baseEnd_7439576 := by
    simpa [prefixWord, tailWord_7439576, baseEnd_7439576] using wordTrace_append hprefix tailTrace_7439576
  have hstable : (prefixWord ++ tailWord_7439576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439576).length < 2 ^ (prefixWord ++ tailWord_7439576).sum := by decide
  have hdescent : baseEnd_7439576 < baseStart_7439576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439632 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_7439632 : Nat := 118140960795 + 7439632 * 2 ^ 59
def prefixEnd_7439632 : Nat := 4983230072969 + 3 ^ 40 * 7439632 * 2
def baseEnd_7439632 : Nat := 3820107108570141639285761

theorem tailTrace_7439632 : CollatzResearch.WordTrace tailWord_7439632 prefixEnd_7439632 3820107108570141639285761 := by
  unfold tailWord_7439632
  simp only [CollatzResearch.WordTrace]
  refine ⟨135672835491745663417016575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180897113988994217889355433 135672835491745663417016575)
  ·
    refine ⟨203509253237618495125524863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135672835491745663417016575 203509253237618495125524863)
    ·
      refine ⟨305263879856427742688287295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203509253237618495125524863 305263879856427742688287295)
      ·
        refine ⟨457895819784641614032430943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305263879856427742688287295 457895819784641614032430943)
        ·
          refine ⟨686843729676962421048646415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457895819784641614032430943 686843729676962421048646415)
          ·
            refine ⟨1030265594515443631572969623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686843729676962421048646415 1030265594515443631572969623)
            ·
              refine ⟨1545398391773165447359454435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030265594515443631572969623 1545398391773165447359454435)
              ·
                refine ⟨2318097587659748171039181653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545398391773165447359454435 2318097587659748171039181653)
                ·
                  refine ⟨13582603052693836939682705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2318097587659748171039181653 13582603052693836939682705)
                  ·
                    refine ⟨10186952289520377704762029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13582603052693836939682705 10186952289520377704762029)
                    ·
                      refine ⟨3820107108570141639285761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10186952289520377704762029 3820107108570141639285761)
                      ·
                        rfl

theorem cell23_7439632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_7439632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439632 prefixEnd_7439632 := by exact prefixLift 7439632
  have htrace : WordTrace (prefixWord ++ tailWord_7439632) baseStart_7439632 baseEnd_7439632 := by
    simpa [prefixWord, tailWord_7439632, baseEnd_7439632] using wordTrace_append hprefix tailTrace_7439632
  have hstable : (prefixWord ++ tailWord_7439632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439632).length < 2 ^ (prefixWord ++ tailWord_7439632).sum := by decide
  have hdescent : baseEnd_7439632 < baseStart_7439632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439693 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7439693 : Nat := 118140960795 + 7439693 * 2 ^ 59
def prefixEnd_7439693 : Nat := 4983230072969 + 3 ^ 40 * 7439693 * 2
def baseEnd_7439693 : Nat := 3820138430890065900622981

theorem tailTrace_7439693 : CollatzResearch.WordTrace tailWord_7439693 prefixEnd_7439693 3820138430890065900622981 := by
  unfold tailWord_7439693
  simp only [CollatzResearch.WordTrace]
  refine ⟨271347895836270334252003733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180898597224180222834669155 271347895836270334252003733)
  ·
    refine ⟨12719432617325171918062675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271347895836270334252003733 12719432617325171918062675)
    ·
      refine ⟨19079148925987757877094013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719432617325171918062675 19079148925987757877094013)
      ·
        refine ⟨7154680847245409203910255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19079148925987757877094013 7154680847245409203910255)
        ·
          refine ⟨10732021270868113805865383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154680847245409203910255 10732021270868113805865383)
          ·
            refine ⟨16098031906302170708798075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732021270868113805865383 16098031906302170708798075)
            ·
              refine ⟨24147047859453256063197113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16098031906302170708798075 24147047859453256063197113)
              ·
                refine ⟨18110285894589942047397835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24147047859453256063197113 18110285894589942047397835)
                ·
                  refine ⟨27165428841884913071096753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18110285894589942047397835 27165428841884913071096753)
                  ·
                    refine ⟨20374071631413684803322565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27165428841884913071096753 20374071631413684803322565)
                    ·
                      refine ⟨3820138430890065900622981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20374071631413684803322565 3820138430890065900622981)
                      ·
                        rfl

theorem cell23_7439693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7439693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439693 prefixEnd_7439693 := by exact prefixLift 7439693
  have htrace : WordTrace (prefixWord ++ tailWord_7439693) baseStart_7439693 baseEnd_7439693 := by
    simpa [prefixWord, tailWord_7439693, baseEnd_7439693] using wordTrace_append hprefix tailTrace_7439693
  have hstable : (prefixWord ++ tailWord_7439693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439693).length < 2 ^ (prefixWord ++ tailWord_7439693).sum := by decide
  have hdescent : baseEnd_7439693 < baseStart_7439693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439706 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2]
def baseStart_7439706 : Nat := 118140960795 + 7439706 * 2 ^ 59
def prefixEnd_7439706 : Nat := 4983230072969 + 3 ^ 40 * 7439706 * 2
def baseEnd_7439706 : Nat := 3820145106138574349760421

theorem tailTrace_7439706 : CollatzResearch.WordTrace tailWord_7439706 prefixEnd_7439706 3820145106138574349760421 := by
  unfold tailWord_7439706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67837092496305809368056743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180898913323482158314817981 67837092496305809368056743)
  ·
    refine ⟨101755638744458714052085115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67837092496305809368056743 101755638744458714052085115)
    ·
      refine ⟨152633458116688071078127673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101755638744458714052085115 152633458116688071078127673)
      ·
        refine ⟨114475093587516053308595755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152633458116688071078127673 114475093587516053308595755)
        ·
          refine ⟨171712640381274079962893633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114475093587516053308595755 171712640381274079962893633)
          ·
            refine ⟨128784480285955559972170225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171712640381274079962893633 128784480285955559972170225)
            ·
              refine ⟨96588360214466669979127669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128784480285955559972170225 96588360214466669979127669)
              ·
                refine ⟨9055158770106250310543219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96588360214466669979127669 9055158770106250310543219)
                ·
                  refine ⟨13582738155159375465814829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9055158770106250310543219 13582738155159375465814829)
                  ·
                    refine ⟨5093526808184765799680561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13582738155159375465814829 5093526808184765799680561)
                    ·
                      refine ⟨3820145106138574349760421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093526808184765799680561 3820145106138574349760421)
                      ·
                        rfl

theorem cell23_7439706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_7439706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439706 prefixEnd_7439706 := by exact prefixLift 7439706
  have htrace : WordTrace (prefixWord ++ tailWord_7439706) baseStart_7439706 baseEnd_7439706 := by
    simpa [prefixWord, tailWord_7439706, baseEnd_7439706] using wordTrace_append hprefix tailTrace_7439706
  have hstable : (prefixWord ++ tailWord_7439706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439706).length < 2 ^ (prefixWord ++ tailWord_7439706).sum := by decide
  have hdescent : baseEnd_7439706 < baseStart_7439706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439769 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_7439769 : Nat := 118140960795 + 7439769 * 2 ^ 59
def prefixEnd_7439769 : Nat := 4983230072969 + 3 ^ 40 * 7439769 * 2
def baseEnd_7439769 : Nat := 3820177455419807603272631

theorem tailTrace_7439769 : CollatzResearch.WordTrace tailWord_7439769 prefixEnd_7439769 3820177455419807603272631 := by
  unfold tailWord_7439769
  simp only [CollatzResearch.WordTrace]
  refine ⟨271350667783994999231770361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180900445189329999487846907 271350667783994999231770361)
  ·
    refine ⟨203513000837996249423827771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271350667783994999231770361 203513000837996249423827771)
    ·
      refine ⟨305269501256994374135741657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203513000837996249423827771 305269501256994374135741657)
      ·
        refine ⟨228952125942745780601806243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305269501256994374135741657 228952125942745780601806243)
        ·
          refine ⟨343428188914118670902709365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228952125942745780601806243 343428188914118670902709365)
          ·
            refine ⟨32196392710698625397129003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343428188914118670902709365 32196392710698625397129003)
            ·
              refine ⟨48294589066047938095693505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32196392710698625397129003 48294589066047938095693505)
              ·
                refine ⟨36220941799535953571770129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48294589066047938095693505 36220941799535953571770129)
                ·
                  refine ⟨27165706349651965178827597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36220941799535953571770129 27165706349651965178827597)
                  ·
                    refine ⟨10187139881119486942060349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27165706349651965178827597 10187139881119486942060349)
                    ·
                      refine ⟨3820177455419807603272631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10187139881119486942060349 3820177455419807603272631)
                      ·
                        rfl

theorem cell23_7439769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_7439769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439769 prefixEnd_7439769 := by exact prefixLift 7439769
  have htrace : WordTrace (prefixWord ++ tailWord_7439769) baseStart_7439769 baseEnd_7439769 := by
    simpa [prefixWord, tailWord_7439769, baseEnd_7439769] using wordTrace_append hprefix tailTrace_7439769
  have hstable : (prefixWord ++ tailWord_7439769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439769).length < 2 ^ (prefixWord ++ tailWord_7439769).sum := by decide
  have hdescent : baseEnd_7439769 < baseStart_7439769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439819 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 5, 4]
def baseStart_7439819 : Nat := 118140960795 + 7439819 * 2 ^ 59
def prefixEnd_7439819 : Nat := 4983230072969 + 3 ^ 40 * 7439819 * 2
def baseEnd_7439819 : Nat := 1273401043150844135882467

theorem tailTrace_7439819 : CollatzResearch.WordTrace tailWord_7439819 prefixEnd_7439819 1273401043150844135882467 := by
  unfold tailWord_7439819
  simp only [CollatzResearch.WordTrace]
  refine ⟨271352491433813857771090511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180901660955875905180727007 271352491433813857771090511)
  ·
    refine ⟨407028737150720786656635767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271352491433813857771090511 407028737150720786656635767)
    ·
      refine ⟨610543105726081179984953651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407028737150720786656635767 610543105726081179984953651)
      ·
        refine ⟨915814658589121769977430477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610543105726081179984953651 915814658589121769977430477)
        ·
          refine ⟨343430496970920663741536429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 915814658589121769977430477 343430496970920663741536429)
          ·
            refine ⟨128786436364095248903076161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343430496970920663741536429 128786436364095248903076161)
            ·
              refine ⟨96589827273071436677307121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128786436364095248903076161 96589827273071436677307121)
              ·
                refine ⟨72442370454803577507980341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96589827273071436677307121 72442370454803577507980341)
                ·
                  refine ⟨6791472230137835391373157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72442370454803577507980341 6791472230137835391373157)
                  ·
                    refine ⟨1273401043150844135882467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791472230137835391373157 1273401043150844135882467)
                    ·
                      rfl

theorem cell23_7439819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 4].length) (baseStart_7439819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439819 prefixEnd_7439819 := by exact prefixLift 7439819
  have htrace : WordTrace (prefixWord ++ tailWord_7439819) baseStart_7439819 baseEnd_7439819 := by
    simpa [prefixWord, tailWord_7439819, baseEnd_7439819] using wordTrace_append hprefix tailTrace_7439819
  have hstable : (prefixWord ++ tailWord_7439819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439819).length < 2 ^ (prefixWord ++ tailWord_7439819).sum := by decide
  have hdescent : baseEnd_7439819 < baseStart_7439819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439943 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 4, 4]
def baseStart_7439943 : Nat := 118140960795 + 7439943 * 2 ^ 59
def prefixEnd_7439943 : Nat := 4983230072969 + 3 ^ 40 * 7439943 * 2
def baseEnd_7439943 : Nat := 1273422267017896640832277

theorem tailTrace_7439943 : CollatzResearch.WordTrace tailWord_7439943 prefixEnd_7439943 1273422267017896640832277 := by
  unfold tailWord_7439943
  simp only [CollatzResearch.WordTrace]
  refine ⟨271357014085364626948604483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180904676056909751299069655 271357014085364626948604483)
  ·
    refine ⟨407035521128046940422906725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271357014085364626948604483 407035521128046940422906725)
    ·
      refine ⟨76319160211508801329295011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407035521128046940422906725 76319160211508801329295011)
      ·
        refine ⟨114478740317263201993942517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76319160211508801329295011 114478740317263201993942517)
        ·
          refine ⟨10732381904743425186932111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114478740317263201993942517 10732381904743425186932111)
          ·
            refine ⟨16098572857115137780398167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732381904743425186932111 16098572857115137780398167)
            ·
              refine ⟨24147859285672706670597251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16098572857115137780398167 24147859285672706670597251)
              ·
                refine ⟨36221788928509060005895877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24147859285672706670597251 36221788928509060005895877)
                ·
                  refine ⟨6791585424095448751105477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36221788928509060005895877 6791585424095448751105477)
                  ·
                    refine ⟨1273422267017896640832277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791585424095448751105477 1273422267017896640832277)
                    ·
                      rfl

theorem cell23_7439943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_7439943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439943 prefixEnd_7439943 := by exact prefixLift 7439943
  have htrace : WordTrace (prefixWord ++ tailWord_7439943) baseStart_7439943 baseEnd_7439943 := by
    simpa [prefixWord, tailWord_7439943, baseEnd_7439943] using wordTrace_append hprefix tailTrace_7439943
  have hstable : (prefixWord ++ tailWord_7439943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439943).length < 2 ^ (prefixWord ++ tailWord_7439943).sum := by decide
  have hdescent : baseEnd_7439943 < baseStart_7439943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439973 : List Nat := [1, 3, 1, 3, 3, 3, 2, 7]
def baseStart_7439973 : Nat := 118140960795 + 7439973 * 2 ^ 59
def prefixEnd_7439973 : Nat := 4983230072969 + 3 ^ 40 * 7439973 * 2
def baseEnd_7439973 : Nat := 141491933536049066856359

theorem tailTrace_7439973 : CollatzResearch.WordTrace tailWord_7439973 prefixEnd_7439973 141491933536049066856359 := by
  unfold tailWord_7439973
  simp only [CollatzResearch.WordTrace]
  refine ⟨271358108275255942072196573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180905405516837294714797715 271358108275255942072196573)
  ·
    refine ⟨101759290603220978277073715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271358108275255942072196573 101759290603220978277073715)
    ·
      refine ⟨152638935904831467415610573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101759290603220978277073715 152638935904831467415610573)
      ·
        refine ⟨57239600964311800280853965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152638935904831467415610573 57239600964311800280853965)
        ·
          refine ⟨21464850361616925105320237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57239600964311800280853965 21464850361616925105320237)
          ·
            refine ⟨8049318885606346914495089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21464850361616925105320237 8049318885606346914495089)
            ·
              refine ⟨6036989164204760185871317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8049318885606346914495089 6036989164204760185871317)
              ·
                refine ⟨141491933536049066856359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6036989164204760185871317 141491933536049066856359)
                ·
                  rfl

theorem cell23_7439973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 7].length) (baseStart_7439973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439973 prefixEnd_7439973 := by exact prefixLift 7439973
  have htrace : WordTrace (prefixWord ++ tailWord_7439973) baseStart_7439973 baseEnd_7439973 := by
    simpa [prefixWord, tailWord_7439973, baseEnd_7439973] using wordTrace_append hprefix tailTrace_7439973
  have hstable : (prefixWord ++ tailWord_7439973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439973).length < 2 ^ (prefixWord ++ tailWord_7439973).sum := by decide
  have hdescent : baseEnd_7439973 < baseStart_7439973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7439984 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 1, 2, 2]
def baseStart_7439984 : Nat := 118140960795 + 7439984 * 2 ^ 59
def prefixEnd_7439984 : Nat := 4983230072969 + 3 ^ 40 * 7439984 * 2
def baseEnd_7439984 : Nat := 3820287853760524262084143

theorem tailTrace_7439984 : CollatzResearch.WordTrace tailWord_7439984 prefixEnd_7439984 3820287853760524262084143 := by
  unfold tailWord_7439984
  simp only [CollatzResearch.WordTrace]
  refine ⟨135679254739108045475423503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180905672985477393967231337 135679254739108045475423503)
  ·
    refine ⟨203518882108662068213135255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135679254739108045475423503 203518882108662068213135255)
    ·
      refine ⟨305278323162993102319702883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203518882108662068213135255 305278323162993102319702883)
      ·
        refine ⟨457917484744489653479554325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305278323162993102319702883 457917484744489653479554325)
        ·
          refine ⟨21464882097397952506854109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 457917484744489653479554325 21464882097397952506854109)
          ·
            refine ⟨8049330786524232190070291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21464882097397952506854109 8049330786524232190070291)
            ·
              refine ⟨12073996179786348285105437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049330786524232190070291 12073996179786348285105437)
              ·
                refine ⟨4527748567419880606914539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12073996179786348285105437 4527748567419880606914539)
                ·
                  refine ⟨6791622851129820910371809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527748567419880606914539 6791622851129820910371809)
                  ·
                    refine ⟨5093717138347365682778857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6791622851129820910371809 5093717138347365682778857)
                    ·
                      refine ⟨3820287853760524262084143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093717138347365682778857 3820287853760524262084143)
                      ·
                        rfl

theorem cell23_7439984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 2, 2].length) (baseStart_7439984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7439984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7439984 prefixEnd_7439984 := by exact prefixLift 7439984
  have htrace : WordTrace (prefixWord ++ tailWord_7439984) baseStart_7439984 baseEnd_7439984 := by
    simpa [prefixWord, tailWord_7439984, baseEnd_7439984] using wordTrace_append hprefix tailTrace_7439984
  have hstable : (prefixWord ++ tailWord_7439984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7439984).length < 2 ^ (prefixWord ++ tailWord_7439984).sum := by decide
  have hdescent : baseEnd_7439984 < baseStart_7439984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7439984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440056 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_7440056 : Nat := 118140960795 + 7440056 * 2 ^ 59
def prefixEnd_7440056 : Nat := 4983230072969 + 3 ^ 40 * 7440056 * 2
def baseEnd_7440056 : Nat := 3820324824367647980383811

theorem tailTrace_7440056 : CollatzResearch.WordTrace tailWord_7440056 prefixEnd_7440056 3820324824367647980383811 := by
  unfold tailWord_7440056
  simp only [CollatzResearch.WordTrace]
  refine ⟨135680567766977623623734011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180907423689303498164978681 135680567766977623623734011)
  ·
    refine ⟨203520851650466435435601017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135680567766977623623734011 203520851650466435435601017)
    ·
      refine ⟨152640638737849826576700763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203520851650466435435601017 152640638737849826576700763)
      ·
        refine ⟨228960958106774739865051145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152640638737849826576700763 228960958106774739865051145)
        ·
          refine ⟨171720718580081054898788359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228960958106774739865051145 171720718580081054898788359)
          ·
            refine ⟨257581077870121582348182539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171720718580081054898788359 257581077870121582348182539)
            ·
              refine ⟨386371616805182373522273809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257581077870121582348182539 386371616805182373522273809)
              ·
                refine ⟨289778712603886780141705357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386371616805182373522273809 289778712603886780141705357)
                ·
                  refine ⟨108667017226457542553139509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289778712603886780141705357 108667017226457542553139509)
                  ·
                    refine ⟨10187532864980394614356829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108667017226457542553139509 10187532864980394614356829)
                    ·
                      refine ⟨3820324824367647980383811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10187532864980394614356829 3820324824367647980383811)
                      ·
                        rfl

theorem cell23_7440056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_7440056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440056 prefixEnd_7440056 := by exact prefixLift 7440056
  have htrace : WordTrace (prefixWord ++ tailWord_7440056) baseStart_7440056 baseEnd_7440056 := by
    simpa [prefixWord, tailWord_7440056, baseEnd_7440056] using wordTrace_append hprefix tailTrace_7440056
  have hstable : (prefixWord ++ tailWord_7440056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440056).length < 2 ^ (prefixWord ++ tailWord_7440056).sum := by decide
  have hdescent : baseEnd_7440056 < baseStart_7440056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440063 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 5]
def baseStart_7440063 : Nat := 118140960795 + 7440063 * 2 ^ 59
def prefixEnd_7440063 : Nat := 4983230072969 + 3 ^ 40 * 7440063 * 2
def baseEnd_7440063 : Nat := 424480935414692161444031

theorem tailTrace_7440063 : CollatzResearch.WordTrace tailWord_7440063 prefixEnd_7440063 424480935414692161444031 := by
  unfold tailWord_7440063
  simp only [CollatzResearch.WordTrace]
  refine ⟨271361390844929887442972843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180907593896619924961981895 271361390844929887442972843)
  ·
    refine ⟨407042086267394831164459265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271361390844929887442972843 407042086267394831164459265)
    ·
      refine ⟨305281564700546123373344449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407042086267394831164459265 305281564700546123373344449)
      ·
        refine ⟨228961173525409592530008337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305281564700546123373344449 228961173525409592530008337)
        ·
          refine ⟨171720880144057194397506253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228961173525409592530008337 171720880144057194397506253)
          ·
            refine ⟨64395330054021447899064845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171720880144057194397506253 64395330054021447899064845)
            ·
              refine ⟨24148248770258042962149317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64395330054021447899064845 24148248770258042962149317)
              ·
                refine ⟨4527796644423383055402997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24148248770258042962149317 4527796644423383055402997)
                ·
                  refine ⟨424480935414692161444031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4527796644423383055402997 424480935414692161444031)
                  ·
                    rfl

theorem cell23_7440063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5].length) (baseStart_7440063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440063 prefixEnd_7440063 := by exact prefixLift 7440063
  have htrace : WordTrace (prefixWord ++ tailWord_7440063) baseStart_7440063 baseEnd_7440063 := by
    simpa [prefixWord, tailWord_7440063, baseEnd_7440063] using wordTrace_append hprefix tailTrace_7440063
  have hstable : (prefixWord ++ tailWord_7440063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440063).length < 2 ^ (prefixWord ++ tailWord_7440063).sum := by decide
  have hdescent : baseEnd_7440063 < baseStart_7440063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440148 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 5]
def baseStart_7440148 : Nat := 118140960795 + 7440148 * 2 ^ 59
def prefixEnd_7440148 : Nat := 4983230072969 + 3 ^ 40 * 7440148 * 2
def baseEnd_7440148 : Nat := 424485784954206846714821

theorem tailTrace_7440148 : CollatzResearch.WordTrace tailWord_7440148 prefixEnd_7440148 424485784954206846714821 := by
  unfold tailWord_7440148
  simp only [CollatzResearch.WordTrace]
  refine ⟨135682245524810973479908549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180909660699747964639878065 135682245524810973479908549)
  ·
    refine ⟨25440421035902057527482853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135682245524810973479908549 25440421035902057527482853)
    ·
      refine ⟨4770078944231635786403035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25440421035902057527482853 4770078944231635786403035)
      ·
        refine ⟨7155118416347453679604553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770078944231635786403035 7155118416347453679604553)
        ·
          refine ⟨5366338812260590259703415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7155118416347453679604553 5366338812260590259703415)
          ·
            refine ⟨8049508218390885389555123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366338812260590259703415 8049508218390885389555123)
            ·
              refine ⟨12074262327586328084332685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049508218390885389555123 12074262327586328084332685)
              ·
                refine ⟨4527848372844873031624757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12074262327586328084332685 4527848372844873031624757)
                ·
                  refine ⟨424485784954206846714821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4527848372844873031624757 424485784954206846714821)
                  ·
                    rfl

theorem cell23_7440148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_7440148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440148 prefixEnd_7440148 := by exact prefixLift 7440148
  have htrace : WordTrace (prefixWord ++ tailWord_7440148) baseStart_7440148 baseEnd_7440148 := by
    simpa [prefixWord, tailWord_7440148, baseEnd_7440148] using wordTrace_append hprefix tailTrace_7440148
  have hstable : (prefixWord ++ tailWord_7440148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440148).length < 2 ^ (prefixWord ++ tailWord_7440148).sum := by decide
  have hdescent : baseEnd_7440148 < baseStart_7440148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440174 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7440174 : Nat := 118140960795 + 7440174 * 2 ^ 59
def prefixEnd_7440174 : Nat := 4983230072969 + 3 ^ 40 * 7440174 * 2
def baseEnd_7440174 : Nat := 1273461805028292839569423

theorem tailTrace_7440174 : CollatzResearch.WordTrace tailWord_7440174 prefixEnd_7440174 1273461805028292839569423 := by
  unfold tailWord_7440174
  simp only [CollatzResearch.WordTrace]
  refine ⟨33920679918440969175032947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180910292898351835600175717 33920679918440969175032947)
  ·
    refine ⟨50881019877661453762549421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33920679918440969175032947 50881019877661453762549421)
    ·
      refine ⟨19080382454123045160956033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50881019877661453762549421 19080382454123045160956033)
      ·
        refine ⟨14310286840592283870717025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19080382454123045160956033 14310286840592283870717025)
        ·
          refine ⟨10732715130444212903037769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14310286840592283870717025 10732715130444212903037769)
          ·
            refine ⟨8049536347833159677278327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10732715130444212903037769 8049536347833159677278327)
            ·
              refine ⟨12074304521749739515917491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049536347833159677278327 12074304521749739515917491)
              ·
                refine ⟨18111456782624609273876237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12074304521749739515917491 18111456782624609273876237)
                ·
                  refine ⟨6791796293484228477703589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18111456782624609273876237 6791796293484228477703589)
                  ·
                    refine ⟨1273461805028292839569423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6791796293484228477703589 1273461805028292839569423)
                    ·
                      rfl

theorem cell23_7440174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7440174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440174 prefixEnd_7440174 := by exact prefixLift 7440174
  have htrace : WordTrace (prefixWord ++ tailWord_7440174) baseStart_7440174 baseEnd_7440174 := by
    simpa [prefixWord, tailWord_7440174, baseEnd_7440174] using wordTrace_append hprefix tailTrace_7440174
  have hstable : (prefixWord ++ tailWord_7440174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440174).length < 2 ^ (prefixWord ++ tailWord_7440174).sum := by decide
  have hdescent : baseEnd_7440174 < baseStart_7440174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440176 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_7440176 : Nat := 118140960795 + 7440176 * 2 ^ 59
def prefixEnd_7440176 : Nat := 4983230072969 + 3 ^ 40 * 7440176 * 2
def baseEnd_7440176 : Nat := 3820386442046187510883259

theorem tailTrace_7440176 : CollatzResearch.WordTrace tailWord_7440176 prefixEnd_7440176 3820386442046187510883259 := by
  unfold tailWord_7440176
  simp only [CollatzResearch.WordTrace]
  refine ⟨135682756146760253870918191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180910341529013671827890921 135682756146760253870918191)
  ·
    refine ⟨203524134220140380806377287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135682756146760253870918191 203524134220140380806377287)
    ·
      refine ⟨305286201330210571209565931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203524134220140380806377287 305286201330210571209565931)
      ·
        refine ⟨457929301995315856814348897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305286201330210571209565931 457929301995315856814348897)
        ·
          refine ⟨343446976496486892610761673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457929301995315856814348897 343446976496486892610761673)
          ·
            refine ⟨257585232372365169458071255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343446976496486892610761673 257585232372365169458071255)
            ·
              refine ⟨386377848558547754187106883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257585232372365169458071255 386377848558547754187106883)
              ·
                refine ⟨579566772837821631280660325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386377848558547754187106883 579566772837821631280660325)
                ·
                  refine ⟨108668769907091555865123811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579566772837821631280660325 108668769907091555865123811)
                  ·
                    refine ⟨163003154860637333797685717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108668769907091555865123811 163003154860637333797685717)
                    ·
                      refine ⟨3820386442046187510883259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163003154860637333797685717 3820386442046187510883259)
                      ·
                        rfl

theorem cell23_7440176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_7440176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440176 prefixEnd_7440176 := by exact prefixLift 7440176
  have htrace : WordTrace (prefixWord ++ tailWord_7440176) baseStart_7440176 baseEnd_7440176 := by
    simpa [prefixWord, tailWord_7440176, baseEnd_7440176] using wordTrace_append hprefix tailTrace_7440176
  have hstable : (prefixWord ++ tailWord_7440176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440176).length < 2 ^ (prefixWord ++ tailWord_7440176).sum := by decide
  have hdescent : baseEnd_7440176 < baseStart_7440176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440200 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 1, 5]
def baseStart_7440200 : Nat := 118140960795 + 7440200 * 2 ^ 59
def prefixEnd_7440200 : Nat := 4983230072969 + 3 ^ 40 * 7440200 * 2
def baseEnd_7440200 : Nat := 1273466255193965138994383

theorem tailTrace_7440200 : CollatzResearch.WordTrace tailWord_7440200 prefixEnd_7440200 1273466255193965138994383 := by
  unfold tailWord_7440200
  simp only [CollatzResearch.WordTrace]
  refine ⟨135683193822716779920355027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180910925096955706560473369 135683193822716779920355027)
  ·
    refine ⟨203524790734075169880532541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135683193822716779920355027 203524790734075169880532541)
    ·
      refine ⟨76321796525278188705199703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203524790734075169880532541 76321796525278188705199703)
      ·
        refine ⟨114482694787917283057799555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76321796525278188705199703 114482694787917283057799555)
        ·
          refine ⟨171724042181875924586699333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114482694787917283057799555 171724042181875924586699333)
          ·
            refine ⟨32198257909101735860006125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171724042181875924586699333 32198257909101735860006125)
            ·
              refine ⟨12074346715913150947502297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32198257909101735860006125 12074346715913150947502297)
              ·
                refine ⟨9055760036934863210626723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12074346715913150947502297 9055760036934863210626723)
                ·
                  refine ⟨13583640055402294815940085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9055760036934863210626723 13583640055402294815940085)
                  ·
                    refine ⟨1273466255193965138994383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13583640055402294815940085 1273466255193965138994383)
                    ·
                      rfl

theorem cell23_7440200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_7440200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440200 prefixEnd_7440200 := by exact prefixLift 7440200
  have htrace : WordTrace (prefixWord ++ tailWord_7440200) baseStart_7440200 baseEnd_7440200 := by
    simpa [prefixWord, tailWord_7440200, baseEnd_7440200] using wordTrace_append hprefix tailTrace_7440200
  have hstable : (prefixWord ++ tailWord_7440200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440200).length < 2 ^ (prefixWord ++ tailWord_7440200).sum := by decide
  have hdescent : baseEnd_7440200 < baseStart_7440200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440213 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_7440213 : Nat := 118140960795 + 7440213 * 2 ^ 59
def prefixEnd_7440213 : Nat := 4983230072969 + 3 ^ 40 * 7440213 * 2
def baseEnd_7440213 : Nat := 1273468480276801288706863

theorem tailTrace_7440213 : CollatzResearch.WordTrace tailWord_7440213 prefixEnd_7440213 1273468480276801288706863 := by
  unfold tailWord_7440213
  simp only [CollatzResearch.WordTrace]
  refine ⟨271366861794386463060933293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180911241196257642040622195 271366861794386463060933293)
  ·
    refine ⟨101762573172894923647849985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271366861794386463060933293 101762573172894923647849985)
    ·
      refine ⟨76321929879671192735887489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101762573172894923647849985 76321929879671192735887489)
      ·
        refine ⟨57241447409753394551915617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76321929879671192735887489 57241447409753394551915617)
        ·
          refine ⟨42931085557315045913936713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57241447409753394551915617 42931085557315045913936713)
          ·
            refine ⟨32198314167986284435452535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42931085557315045913936713 32198314167986284435452535)
            ·
              refine ⟨48297471251979426653178803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32198314167986284435452535 48297471251979426653178803)
              ·
                refine ⟨72446206877969139979768205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48297471251979426653178803 72446206877969139979768205)
                ·
                  refine ⟨27167327579238427492413077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72446206877969139979768205 27167327579238427492413077)
                  ·
                    refine ⟨1273468480276801288706863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27167327579238427492413077 1273468480276801288706863)
                    ·
                      rfl

theorem cell23_7440213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_7440213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440213 prefixEnd_7440213 := by exact prefixLift 7440213
  have htrace : WordTrace (prefixWord ++ tailWord_7440213) baseStart_7440213 baseEnd_7440213 := by
    simpa [prefixWord, tailWord_7440213, baseEnd_7440213] using wordTrace_append hprefix tailTrace_7440213
  have hstable : (prefixWord ++ tailWord_7440213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440213).length < 2 ^ (prefixWord ++ tailWord_7440213).sum := by decide
  have hdescent : baseEnd_7440213 < baseStart_7440213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440274 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_7440274 : Nat := 118140960795 + 7440274 * 2 ^ 59
def prefixEnd_7440274 : Nat := 4983230072969 + 3 ^ 40 * 7440274 * 2
def baseEnd_7440274 : Nat := 3820436763150328127457809

theorem tailTrace_7440274 : CollatzResearch.WordTrace tailWord_7440274 prefixEnd_7440274 3820436763150328127457809 := by
  unfold tailWord_7440274
  simp only [CollatzResearch.WordTrace]
  refine ⟨67842271661791367619725969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180912724431443646985935917 67842271661791367619725969)
  ·
    refine ⟨50881703746343525714794477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67842271661791367619725969 50881703746343525714794477)
    ·
      refine ⟨19080638904878822143047929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50881703746343525714794477 19080638904878822143047929)
      ·
        refine ⟨14310479178659116607285947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19080638904878822143047929 14310479178659116607285947)
        ·
          refine ⟨21465718767988674910928921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14310479178659116607285947 21465718767988674910928921)
          ·
            refine ⟨16099289075991506183196691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21465718767988674910928921 16099289075991506183196691)
            ·
              refine ⟨24148933613987259274795037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16099289075991506183196691 24148933613987259274795037)
              ·
                refine ⟨9055850105245222228048139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24148933613987259274795037 9055850105245222228048139)
                ·
                  refine ⟨13583775157867833342072209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9055850105245222228048139 13583775157867833342072209)
                  ·
                    refine ⟨10187831368400875006554157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13583775157867833342072209 10187831368400875006554157)
                    ·
                      refine ⟨3820436763150328127457809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10187831368400875006554157 3820436763150328127457809)
                      ·
                        rfl

theorem cell23_7440274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_7440274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440274 prefixEnd_7440274 := by exact prefixLift 7440274
  have htrace : WordTrace (prefixWord ++ tailWord_7440274) baseStart_7440274 baseEnd_7440274 := by
    simpa [prefixWord, tailWord_7440274, baseEnd_7440274] using wordTrace_append hprefix tailTrace_7440274
  have hstable : (prefixWord ++ tailWord_7440274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440274).length < 2 ^ (prefixWord ++ tailWord_7440274).sum := by decide
  have hdescent : baseEnd_7440274 < baseStart_7440274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440293 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_7440293 : Nat := 118140960795 + 7440293 * 2 ^ 59
def prefixEnd_7440293 : Nat := 4983230072969 + 3 ^ 40 * 7440293 * 2
def baseEnd_7440293 : Nat := 3820446519282763553120221

theorem tailTrace_7440293 : CollatzResearch.WordTrace tailWord_7440293 prefixEnd_7440293 3820446519282763553120221 := by
  unfold tailWord_7440293
  simp only [CollatzResearch.WordTrace]
  refine ⟨271369779634096636723845533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180913186422731091149230355 271369779634096636723845533)
  ·
    refine ⟨101763667362786238771442075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271369779634096636723845533 101763667362786238771442075)
    ·
      refine ⟨152645501044179358157163113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101763667362786238771442075 152645501044179358157163113)
      ·
        refine ⟨114484125783134518617872335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152645501044179358157163113 114484125783134518617872335)
        ·
          refine ⟨171726188674701777926808503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114484125783134518617872335 171726188674701777926808503)
          ·
            refine ⟨257589283012052666890212755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171726188674701777926808503 257589283012052666890212755)
            ·
              refine ⟨386383924518079000335319133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257589283012052666890212755 386383924518079000335319133)
              ·
                refine ⟨144893971694279625125744675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386383924518079000335319133 144893971694279625125744675)
                ·
                  refine ⟨217340957541419437688617013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144893971694279625125744675 217340957541419437688617013)
                  ·
                    refine ⟨20375714769508072283307845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217340957541419437688617013 20375714769508072283307845)
                    ·
                      refine ⟨3820446519282763553120221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20375714769508072283307845 3820446519282763553120221)
                      ·
                        rfl

theorem cell23_7440293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_7440293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440293 prefixEnd_7440293 := by exact prefixLift 7440293
  have htrace : WordTrace (prefixWord ++ tailWord_7440293) baseStart_7440293 baseEnd_7440293 := by
    simpa [prefixWord, tailWord_7440293, baseEnd_7440293] using wordTrace_append hprefix tailTrace_7440293
  have hstable : (prefixWord ++ tailWord_7440293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440293).length < 2 ^ (prefixWord ++ tailWord_7440293).sum := by decide
  have hdescent : baseEnd_7440293 < baseStart_7440293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440303 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 2, 6]
def baseStart_7440303 : Nat := 118140960795 + 7440303 * 2 ^ 59
def prefixEnd_7440303 : Nat := 4983230072969 + 3 ^ 40 * 7440303 * 2
def baseEnd_7440303 : Nat := 1273483884696436171331725

theorem tailTrace_7440303 : CollatzResearch.WordTrace tailWord_7440303 prefixEnd_7440303 1273483884696436171331725 := by
  unfold tailWord_7440303
  simp only [CollatzResearch.WordTrace]
  refine ⟨271370144364060408431709563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180913429576040272287806375 271370144364060408431709563)
  ·
    refine ⟨407055216546090612647564345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271370144364060408431709563 407055216546090612647564345)
    ·
      refine ⟨305291412409567959485673259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407055216546090612647564345 305291412409567959485673259)
      ·
        refine ⟨457937118614351939228509889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305291412409567959485673259 457937118614351939228509889)
        ·
          refine ⟨343452838960763954421382417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457937118614351939228509889 343452838960763954421382417)
          ·
            refine ⟨257589629220572965816036813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343452838960763954421382417 257589629220572965816036813)
            ·
              refine ⟨96596110957714862181013805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257589629220572965816036813 96596110957714862181013805)
              ·
                refine ⟨36223541609143073317880177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96596110957714862181013805 36223541609143073317880177)
                ·
                  refine ⟨27167656206857304988410133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36223541609143073317880177 27167656206857304988410133)
                  ·
                    refine ⟨1273483884696436171331725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27167656206857304988410133 1273483884696436171331725)
                    ·
                      rfl

theorem cell23_7440303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_7440303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440303 prefixEnd_7440303 := by exact prefixLift 7440303
  have htrace : WordTrace (prefixWord ++ tailWord_7440303) baseStart_7440303 baseEnd_7440303 := by
    simpa [prefixWord, tailWord_7440303, baseEnd_7440303] using wordTrace_append hprefix tailTrace_7440303
  have hstable : (prefixWord ++ tailWord_7440303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440303).length < 2 ^ (prefixWord ++ tailWord_7440303).sum := by decide
  have hdescent : baseEnd_7440303 < baseStart_7440303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440343 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_7440343 : Nat := 118140960795 + 7440343 * 2 ^ 59
def prefixEnd_7440343 : Nat := 4983230072969 + 3 ^ 40 * 7440343 * 2
def baseEnd_7440343 : Nat := 3820472193315488357494991

theorem tailTrace_7440343 : CollatzResearch.WordTrace tailWord_7440343 prefixEnd_7440343 3820472193315488357494991 := by
  unfold tailWord_7440343
  simp only [CollatzResearch.WordTrace]
  refine ⟨271371603283915495263165683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180914402189276996842110455 271371603283915495263165683)
  ·
    refine ⟨407057404925873242894748525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271371603283915495263165683 407057404925873242894748525)
    ·
      refine ⟨152646526847202466085530697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407057404925873242894748525 152646526847202466085530697)
      ·
        refine ⟨114484895135401849564148023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152646526847202466085530697 114484895135401849564148023)
        ·
          refine ⟨171727342703102774346222035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114484895135401849564148023 171727342703102774346222035)
          ·
            refine ⟨257591014054654161519333053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171727342703102774346222035 257591014054654161519333053)
            ·
              refine ⟨96596630270495310569749895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257591014054654161519333053 96596630270495310569749895)
              ·
                refine ⟨144894945405742965854624843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96596630270495310569749895 144894945405742965854624843)
                ·
                  refine ⟨217342418108614448781937265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144894945405742965854624843 217342418108614448781937265)
                  ·
                    refine ⟨163006813581460836586452949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217342418108614448781937265 163006813581460836586452949)
                    ·
                      refine ⟨3820472193315488357494991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163006813581460836586452949 3820472193315488357494991)
                      ·
                        rfl

theorem cell23_7440343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_7440343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440343 prefixEnd_7440343 := by exact prefixLift 7440343
  have htrace : WordTrace (prefixWord ++ tailWord_7440343) baseStart_7440343 baseEnd_7440343 := by
    simpa [prefixWord, tailWord_7440343, baseEnd_7440343] using wordTrace_append hprefix tailTrace_7440343
  have hstable : (prefixWord ++ tailWord_7440343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440343).length < 2 ^ (prefixWord ++ tailWord_7440343).sum := by decide
  have hdescent : baseEnd_7440343 < baseStart_7440343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440344 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 2, 2, 2]
def baseStart_7440344 : Nat := 118140960795 + 7440344 * 2 ^ 59
def prefixEnd_7440344 : Nat := 4983230072969 + 3 ^ 40 * 7440344 * 2
def baseEnd_7440344 : Nat := 3820472706796142853582487

theorem tailTrace_7440344 : CollatzResearch.WordTrace tailWord_7440344 prefixEnd_7440344 3820472706796142853582487 := by
  unfold tailWord_7440344
  simp only [CollatzResearch.WordTrace]
  refine ⟨135685819878455936216976043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180914426504607914955968057 135685819878455936216976043)
  ·
    refine ⟨203528729817683904325464065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135685819878455936216976043 203528729817683904325464065)
    ·
      refine ⟨152646547363262928244098049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203528729817683904325464065 152646547363262928244098049)
      ·
        refine ⟨114484910522447196183073537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152646547363262928244098049 114484910522447196183073537)
        ·
          refine ⟨85863682891835397137305153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114484910522447196183073537 85863682891835397137305153)
          ·
            refine ⟨64397762168876547852978865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85863682891835397137305153 64397762168876547852978865)
            ·
              refine ⟨48298321626657410889734149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64397762168876547852978865 48298321626657410889734149)
              ·
                refine ⟨9055935304998264541825153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48298321626657410889734149 9055935304998264541825153)
                ·
                  refine ⟨6791951478748698406368865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9055935304998264541825153 6791951478748698406368865)
                  ·
                    refine ⟨5093963609061523804776649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6791951478748698406368865 5093963609061523804776649)
                    ·
                      refine ⟨3820472706796142853582487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093963609061523804776649 3820472706796142853582487)
                      ·
                        rfl

theorem cell23_7440344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_7440344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440344 prefixEnd_7440344 := by exact prefixLift 7440344
  have htrace : WordTrace (prefixWord ++ tailWord_7440344) baseStart_7440344 baseEnd_7440344 := by
    simpa [prefixWord, tailWord_7440344, baseEnd_7440344] using wordTrace_append hprefix tailTrace_7440344
  have hstable : (prefixWord ++ tailWord_7440344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440344).length < 2 ^ (prefixWord ++ tailWord_7440344).sum := by decide
  have hdescent : baseEnd_7440344 < baseStart_7440344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440360 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_7440360 : Nat := 118140960795 + 7440360 * 2 ^ 59
def prefixEnd_7440360 : Nat := 4983230072969 + 3 ^ 40 * 7440360 * 2
def baseEnd_7440360 : Nat := 3820480922486614790982413

theorem tailTrace_7440360 : CollatzResearch.WordTrace tailWord_7440360 prefixEnd_7440360 3820480922486614790982413 := by
  unfold tailWord_7440360
  simp only [CollatzResearch.WordTrace]
  refine ⟨135686111662426953583267267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180914815549902604777689689 135686111662426953583267267)
  ·
    refine ⟨203529167493640430374900901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135686111662426953583267267 203529167493640430374900901)
    ·
      refine ⟨38161718905057580695293919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203529167493640430374900901 38161718905057580695293919)
      ·
        refine ⟨57242578357586371042940879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38161718905057580695293919 57242578357586371042940879)
        ·
          refine ⟨85863867536379556564411319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57242578357586371042940879 85863867536379556564411319)
          ·
            refine ⟨128795801304569334846616979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85863867536379556564411319 128795801304569334846616979)
            ·
              refine ⟨193193701956854002269925469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128795801304569334846616979 193193701956854002269925469)
              ·
                refine ⟨72447638233820250851222051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193193701956854002269925469 72447638233820250851222051)
                ·
                  refine ⟨108671457350730376276833077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72447638233820250851222051 108671457350730376276833077)
                  ·
                    refine ⟨10187949126630972775953101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108671457350730376276833077 10187949126630972775953101)
                    ·
                      refine ⟨3820480922486614790982413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10187949126630972775953101 3820480922486614790982413)
                      ·
                        rfl

theorem cell23_7440360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_7440360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440360 prefixEnd_7440360 := by exact prefixLift 7440360
  have htrace : WordTrace (prefixWord ++ tailWord_7440360) baseStart_7440360 baseEnd_7440360 := by
    simpa [prefixWord, tailWord_7440360, baseEnd_7440360] using wordTrace_append hprefix tailTrace_7440360
  have hstable : (prefixWord ++ tailWord_7440360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440360).length < 2 ^ (prefixWord ++ tailWord_7440360).sum := by decide
  have hdescent : baseEnd_7440360 < baseStart_7440360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440363 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 3, 7]
def baseStart_7440363 : Nat := 118140960795 + 7440363 * 2 ^ 59
def prefixEnd_7440363 : Nat := 4983230072969 + 3 ^ 40 * 7440363 * 2
def baseEnd_7440363 : Nat := 1273494154309526093081633

theorem tailTrace_7440363 : CollatzResearch.WordTrace tailWord_7440363 prefixEnd_7440363 1273494154309526093081633 := by
  unfold tailWord_7440363
  simp only [CollatzResearch.WordTrace]
  refine ⟨271372332743843038678893743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180914888495895359119262495 271372332743843038678893743)
  ·
    refine ⟨407058499115764558018340615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271372332743843038678893743 407058499115764558018340615)
    ·
      refine ⟨610587748673646837027510923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407058499115764558018340615 610587748673646837027510923)
      ·
        refine ⟨915881623010470255541266385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610587748673646837027510923 915881623010470255541266385)
        ·
          refine ⟨686911217257852691655949789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 915881623010470255541266385 686911217257852691655949789)
          ·
            refine ⟨257591706471694759370981171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686911217257852691655949789 257591706471694759370981171)
            ·
              refine ⟨386387559707542139056471757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257591706471694759370981171 386387559707542139056471757)
              ·
                refine ⟨144895334890328302146176909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386387559707542139056471757 144895334890328302146176909)
                ·
                  refine ⟨54335750583873113304816341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144895334890328302146176909 54335750583873113304816341)
                  ·
                    refine ⟨1273494154309526093081633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54335750583873113304816341 1273494154309526093081633)
                    ·
                      rfl

theorem cell23_7440363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_7440363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440363 prefixEnd_7440363 := by exact prefixLift 7440363
  have htrace : WordTrace (prefixWord ++ tailWord_7440363) baseStart_7440363 baseEnd_7440363 := by
    simpa [prefixWord, tailWord_7440363, baseEnd_7440363] using wordTrace_append hprefix tailTrace_7440363
  have hstable : (prefixWord ++ tailWord_7440363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440363).length < 2 ^ (prefixWord ++ tailWord_7440363).sum := by decide
  have hdescent : baseEnd_7440363 < baseStart_7440363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440365 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7440365 : Nat := 118140960795 + 7440365 * 2 ^ 59
def prefixEnd_7440365 : Nat := 4983230072969 + 3 ^ 40 * 7440365 * 2
def baseEnd_7440365 : Nat := 3820483489889887271419891

theorem tailTrace_7440365 : CollatzResearch.WordTrace tailWord_7440365 prefixEnd_7440365 3820483489889887271419891 := by
  unfold tailWord_7440365
  simp only [CollatzResearch.WordTrace]
  refine ⟨271372405689835793020466549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180914937126557195346977699 271372405689835793020466549)
  ·
    refine ⟨25441163033422105595668739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271372405689835793020466549 25441163033422105595668739)
    ·
      refine ⟨38161744550133158393503109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25441163033422105595668739 38161744550133158393503109)
      ·
        refine ⟨7155327103149967198781833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38161744550133158393503109 7155327103149967198781833)
        ·
          refine ⟨5366495327362475399086375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7155327103149967198781833 5366495327362475399086375)
          ·
            refine ⟨8049742991043713098629563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366495327362475399086375 8049742991043713098629563)
            ·
              refine ⟨12074614486565569647944345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049742991043713098629563 12074614486565569647944345)
              ·
                refine ⟨9055960864924177235958259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12074614486565569647944345 9055960864924177235958259)
                ·
                  refine ⟨13583941297386265853937389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9055960864924177235958259 13583941297386265853937389)
                  ·
                    refine ⟨5093977986519849695226521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13583941297386265853937389 5093977986519849695226521)
                    ·
                      refine ⟨3820483489889887271419891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5093977986519849695226521 3820483489889887271419891)
                      ·
                        rfl

theorem cell23_7440365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7440365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440365 prefixEnd_7440365 := by exact prefixLift 7440365
  have htrace : WordTrace (prefixWord ++ tailWord_7440365) baseStart_7440365 baseEnd_7440365 := by
    simpa [prefixWord, tailWord_7440365, baseEnd_7440365] using wordTrace_append hprefix tailTrace_7440365
  have hstable : (prefixWord ++ tailWord_7440365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440365).length < 2 ^ (prefixWord ++ tailWord_7440365).sum := by decide
  have hdescent : baseEnd_7440365 < baseStart_7440365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440434 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_7440434 : Nat := 118140960795 + 7440434 * 2 ^ 59
def prefixEnd_7440434 : Nat := 4983230072969 + 3 ^ 40 * 7440434 * 2
def baseEnd_7440434 : Nat := 3820518920055047501457073

theorem tailTrace_7440434 : CollatzResearch.WordTrace tailWord_7440434 prefixEnd_7440434 3820518920055047501457073 := by
  unfold tailWord_7440434
  simp only [CollatzResearch.WordTrace]
  refine ⟨67843730581646454451182089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180916614884390545203152237 67843730581646454451182089)
  ·
    refine ⟨50882797936234840838386567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67843730581646454451182089 50882797936234840838386567)
    ·
      refine ⟨76324196904352261257579851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50882797936234840838386567 76324196904352261257579851)
      ·
        refine ⟨114486295356528391886369777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76324196904352261257579851 114486295356528391886369777)
        ·
          refine ⟨85864721517396293914777333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114486295356528391886369777 85864721517396293914777333)
          ·
            refine ⟨8049817642255902554510375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85864721517396293914777333 8049817642255902554510375)
            ·
              refine ⟨12074726463383853831765563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049817642255902554510375 12074726463383853831765563)
              ·
                refine ⟨18112089695075780747648345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12074726463383853831765563 18112089695075780747648345)
                ·
                  refine ⟨13584067271306835560736259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18112089695075780747648345 13584067271306835560736259)
                  ·
                    refine ⟨20376100906960253341104389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13584067271306835560736259 20376100906960253341104389)
                    ·
                      refine ⟨3820518920055047501457073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20376100906960253341104389 3820518920055047501457073)
                      ·
                        rfl

theorem cell23_7440434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_7440434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440434 prefixEnd_7440434 := by exact prefixLift 7440434
  have htrace : WordTrace (prefixWord ++ tailWord_7440434) baseStart_7440434 baseEnd_7440434 := by
    simpa [prefixWord, tailWord_7440434, baseEnd_7440434] using wordTrace_append hprefix tailTrace_7440434
  have hstable : (prefixWord ++ tailWord_7440434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440434).length < 2 ^ (prefixWord ++ tailWord_7440434).sum := by decide
  have hdescent : baseEnd_7440434 < baseStart_7440434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440460 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_7440460 : Nat := 118140960795 + 7440460 * 2 ^ 59
def prefixEnd_7440460 : Nat := 4983230072969 + 3 ^ 40 * 7440460 * 2
def baseEnd_7440460 : Nat := 3820532270552064399731953

theorem tailTrace_7440460 : CollatzResearch.WordTrace tailWord_7440460 prefixEnd_7440460 3820532270552064399731953 := by
  unfold tailWord_7440460
  simp only [CollatzResearch.WordTrace]
  refine ⟨135687935312245812122587417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180917247082994416163449889 135687935312245812122587417)
  ·
    refine ⟨101765951484184359091940563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135687935312245812122587417 101765951484184359091940563)
    ·
      refine ⟨152648927226276538637910845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101765951484184359091940563 152648927226276538637910845)
      ·
        refine ⟨57243347709853701989216567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152648927226276538637910845 57243347709853701989216567)
        ·
          refine ⟨85865021564780552983824851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57243347709853701989216567 85865021564780552983824851)
          ·
            refine ⟨128797532347170829475737277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85865021564780552983824851 128797532347170829475737277)
            ·
              refine ⟨48299074630189061053401479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128797532347170829475737277 48299074630189061053401479)
              ·
                refine ⟨72448611945283591580102219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48299074630189061053401479 72448611945283591580102219)
                ·
                  refine ⟨108672917917925387370153329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72448611945283591580102219 108672917917925387370153329)
                  ·
                    refine ⟨81504688438444040527614997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108672917917925387370153329 81504688438444040527614997)
                    ·
                      refine ⟨3820532270552064399731953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81504688438444040527614997 3820532270552064399731953)
                      ·
                        rfl

theorem cell23_7440460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_7440460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440460 prefixEnd_7440460 := by exact prefixLift 7440460
  have htrace : WordTrace (prefixWord ++ tailWord_7440460) baseStart_7440460 baseEnd_7440460 := by
    simpa [prefixWord, tailWord_7440460, baseEnd_7440460] using wordTrace_append hprefix tailTrace_7440460
  have hstable : (prefixWord ++ tailWord_7440460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440460).length < 2 ^ (prefixWord ++ tailWord_7440460).sum := by decide
  have hdescent : baseEnd_7440460 < baseStart_7440460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440461 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_7440461 : Nat := 118140960795 + 7440461 * 2 ^ 59
def prefixEnd_7440461 : Nat := 4983230072969 + 3 ^ 40 * 7440461 * 2
def baseEnd_7440461 : Nat := 1273510928010906298606483

theorem tailTrace_7440461 : CollatzResearch.WordTrace tailWord_7440461 prefixEnd_7440461 1273510928010906298606483 := by
  unfold tailWord_7440461
  simp only [CollatzResearch.WordTrace]
  refine ⟨271375907097488001415961237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180917271398325334277307491 271375907097488001415961237)
  ·
    refine ⟨12720745645194750066373183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 271375907097488001415961237 12720745645194750066373183)
    ·
      refine ⟨19081118467792125099559775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12720745645194750066373183 19081118467792125099559775)
      ·
        refine ⟨28621677701688187649339663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19081118467792125099559775 28621677701688187649339663)
        ·
          refine ⟨42932516552532281474009495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28621677701688187649339663 42932516552532281474009495)
          ·
            refine ⟨64398774828798422211014243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42932516552532281474009495 64398774828798422211014243)
            ·
              refine ⟨96598162243197633316521365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64398774828798422211014243 96598162243197633316521365)
              ·
                refine ⟨4528038855149889061711939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96598162243197633316521365 4528038855149889061711939)
                ·
                  refine ⟨6792058282724833592567909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4528038855149889061711939 6792058282724833592567909)
                  ·
                    refine ⟨1273510928010906298606483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6792058282724833592567909 1273510928010906298606483)
                    ·
                      rfl

theorem cell23_7440461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_7440461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440461 prefixEnd_7440461 := by exact prefixLift 7440461
  have htrace : WordTrace (prefixWord ++ tailWord_7440461) baseStart_7440461 baseEnd_7440461 := by
    simpa [prefixWord, tailWord_7440461, baseEnd_7440461] using wordTrace_append hprefix tailTrace_7440461
  have hstable : (prefixWord ++ tailWord_7440461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440461).length < 2 ^ (prefixWord ++ tailWord_7440461).sum := by decide
  have hdescent : baseEnd_7440461 < baseStart_7440461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440484 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_7440484 : Nat := 118140960795 + 7440484 * 2 ^ 59
def prefixEnd_7440484 : Nat := 4983230072969 + 3 ^ 40 * 7440484 * 2
def baseEnd_7440484 : Nat := 3820544594087772305831843

theorem tailTrace_7440484 : CollatzResearch.WordTrace tailWord_7440484 prefixEnd_7440484 3820544594087772305831843 := by
  unfold tailWord_7440484
  simp only [CollatzResearch.WordTrace]
  refine ⟨135688372988202338172024253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180917830650936450896032337 135688372988202338172024253)
  ·
    refine ⟨50883139870575876814509095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135688372988202338172024253 50883139870575876814509095)
    ·
      refine ⟨76324709805863815221763643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50883139870575876814509095 76324709805863815221763643)
      ·
        refine ⟨114487064708795722832645465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76324709805863815221763643 114487064708795722832645465)
        ·
          refine ⟨85865298531596792124484099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114487064708795722832645465 85865298531596792124484099)
          ·
            refine ⟨128797947797395188186726149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85865298531596792124484099 128797947797395188186726149)
            ·
              refine ⟨24149615212011597785011153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128797947797395188186726149 24149615212011597785011153)
              ·
                refine ⟨18112211409008698338758365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24149615212011597785011153 18112211409008698338758365)
                ·
                  refine ⟨6792079278378261877034387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18112211409008698338758365 6792079278378261877034387)
                  ·
                    refine ⟨10188118917567392815551581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6792079278378261877034387 10188118917567392815551581)
                    ·
                      refine ⟨3820544594087772305831843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10188118917567392815551581 3820544594087772305831843)
                      ·
                        rfl

theorem cell23_7440484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_7440484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440484 prefixEnd_7440484 := by exact prefixLift 7440484
  have htrace : WordTrace (prefixWord ++ tailWord_7440484) baseStart_7440484 baseEnd_7440484 := by
    simpa [prefixWord, tailWord_7440484, baseEnd_7440484] using wordTrace_append hprefix tailTrace_7440484
  have hstable : (prefixWord ++ tailWord_7440484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440484).length < 2 ^ (prefixWord ++ tailWord_7440484).sum := by decide
  have hdescent : baseEnd_7440484 < baseStart_7440484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440494 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_7440494 : Nat := 118140960795 + 7440494 * 2 ^ 59
def prefixEnd_7440494 : Nat := 4983230072969 + 3 ^ 40 * 7440494 * 2
def baseEnd_7440494 : Nat := 3820549728894317266706797

theorem tailTrace_7440494 : CollatzResearch.WordTrace tailWord_7440494 prefixEnd_7440494 3820549728894317266706797 := by
  unfold tailWord_7440494
  simp only [CollatzResearch.WordTrace]
  refine ⟨33922138838296056006489067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180918073804245632034608357 33922138838296056006489067)
  ·
    refine ⟨50883208257444084009733601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33922138838296056006489067 50883208257444084009733601)
    ·
      refine ⟨38162406193083063007300201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50883208257444084009733601 38162406193083063007300201)
      ·
        refine ⟨28621804644812297255475151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38162406193083063007300201 28621804644812297255475151)
        ·
          refine ⟨42932706967218445883212727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28621804644812297255475151 42932706967218445883212727)
          ·
            refine ⟨64399060450827668824819091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42932706967218445883212727 64399060450827668824819091)
            ·
              refine ⟨96598590676241503237228637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64399060450827668824819091 96598590676241503237228637)
              ·
                refine ⟨36224471503590563713960739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96598590676241503237228637 36224471503590563713960739)
                ·
                  refine ⟨54336707255385845570941109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36224471503590563713960739 54336707255385845570941109)
                  ·
                    refine ⟨5094066305192423022275729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54336707255385845570941109 5094066305192423022275729)
                    ·
                      refine ⟨3820549728894317266706797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5094066305192423022275729 3820549728894317266706797)
                      ·
                        rfl

theorem cell23_7440494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_7440494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440494 prefixEnd_7440494 := by exact prefixLift 7440494
  have htrace : WordTrace (prefixWord ++ tailWord_7440494) baseStart_7440494 baseEnd_7440494 := by
    simpa [prefixWord, tailWord_7440494, baseEnd_7440494] using wordTrace_append hprefix tailTrace_7440494
  have hstable : (prefixWord ++ tailWord_7440494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440494).length < 2 ^ (prefixWord ++ tailWord_7440494).sum := by decide
  have hdescent : baseEnd_7440494 < baseStart_7440494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7440538 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_7440538 : Nat := 118140960795 + 7440538 * 2 ^ 59
def prefixEnd_7440538 : Nat := 4983230072969 + 3 ^ 40 * 7440538 * 2
def baseEnd_7440538 : Nat := 1273524107347705031518865

theorem tailTrace_7440538 : CollatzResearch.WordTrace tailWord_7440538 prefixEnd_7440538 1273524107347705031518865 := by
  unfold tailWord_7440538
  simp only [CollatzResearch.WordTrace]
  refine ⟨67844678879552260891628567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180919143678806029044342845 67844678879552260891628567)
  ·
    refine ⟨101767018319328391337442851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67844678879552260891628567 101767018319328391337442851)
    ·
      refine ⟨152650527478992587006164277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101767018319328391337442851 152650527478992587006164277)
      ·
        refine ⟨14310986951155555031827901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152650527478992587006164277 14310986951155555031827901)
        ·
          refine ⟨5366620106683333136935463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14310986951155555031827901 5366620106683333136935463)
          ·
            refine ⟨8049930160024999705403195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366620106683333136935463 8049930160024999705403195)
            ·
              refine ⟨12074895240037499558104793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049930160024999705403195 12074895240037499558104793)
              ·
                refine ⟨9056171430028124668578595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12074895240037499558104793 9056171430028124668578595)
                ·
                  refine ⟨13584257145042187002867893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9056171430028124668578595 13584257145042187002867893)
                  ·
                    refine ⟨1273524107347705031518865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13584257145042187002867893 1273524107347705031518865)
                    ·
                      rfl

theorem cell23_7440538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_7440538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7440538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7440538 prefixEnd_7440538 := by exact prefixLift 7440538
  have htrace : WordTrace (prefixWord ++ tailWord_7440538) baseStart_7440538 baseEnd_7440538 := by
    simpa [prefixWord, tailWord_7440538, baseEnd_7440538] using wordTrace_append hprefix tailTrace_7440538
  have hstable : (prefixWord ++ tailWord_7440538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7440538).length < 2 ^ (prefixWord ++ tailWord_7440538).sum := by decide
  have hdescent : baseEnd_7440538 < baseStart_7440538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7440538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
