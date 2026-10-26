import V185TrunkScan23Chunk0907

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5374168 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5374168 : Nat := 118140960795 + 5374168 * 2 ^ 59
def prefixEnd_5374168 : Nat := 4983230072969 + 3 ^ 40 * 5374168 * 2
def baseEnd_5374168 : Nat := 2759531302012034776684657

theorem tailTrace_5374168 : CollatzResearch.WordTrace tailWord_5374168 prefixEnd_5374168 2759531302012034776684657 := by
  unfold tailWord_5374168
  simp only [CollatzResearch.WordTrace]
  refine ⟨98006004997157322833473579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130674673329543097111298105 98006004997157322833473579)
  ·
    refine ⟨147009007495735984250210369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98006004997157322833473579 147009007495735984250210369)
    ·
      refine ⟨110256755621801988187657777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147009007495735984250210369 110256755621801988187657777)
      ·
        refine ⟨82692566716351491140743333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110256755621801988187657777 82692566716351491140743333)
        ·
          refine ⟨15504856259315904588889375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82692566716351491140743333 15504856259315904588889375)
          ·
            refine ⟨23257284388973856883334063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15504856259315904588889375 23257284388973856883334063)
            ·
              refine ⟨34885926583460785325001095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23257284388973856883334063 34885926583460785325001095)
              ·
                refine ⟨52328889875191177987501643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34885926583460785325001095 52328889875191177987501643)
                ·
                  refine ⟨78493334812786766981252465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52328889875191177987501643 78493334812786766981252465)
                  ·
                    refine ⟨58870001109590075235939349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78493334812786766981252465 58870001109590075235939349)
                    ·
                      refine ⟨2759531302012034776684657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58870001109590075235939349 2759531302012034776684657)
                      ·
                        rfl

theorem cell23_5374168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5374168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374168 prefixEnd_5374168 := by exact prefixLift 5374168
  have htrace : WordTrace (prefixWord ++ tailWord_5374168) baseStart_5374168 baseEnd_5374168 := by
    simpa [prefixWord, tailWord_5374168, baseEnd_5374168] using wordTrace_append hprefix tailTrace_5374168
  have hstable : (prefixWord ++ tailWord_5374168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374168).length < 2 ^ (prefixWord ++ tailWord_5374168).sum := by decide
  have hdescent : baseEnd_5374168 < baseStart_5374168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374185 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 4, 3, 2]
def baseStart_5374185 : Nat := 118140960795 + 5374185 * 2 ^ 59
def prefixEnd_5374185 : Nat := 4983230072969 + 3 ^ 40 * 5374185 * 2
def baseEnd_5374185 : Nat := 2759540031183161210172079

theorem tailTrace_5374185 : CollatzResearch.WordTrace tailWord_5374185 prefixEnd_5374185 2759540031183161210172079 := by
  unfold tailWord_5374185
  simp only [CollatzResearch.WordTrace]
  refine ⟨196012630035253057570316009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130675086690168705046877339 196012630035253057570316009)
  ·
    refine ⟨147009472526439793177737007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196012630035253057570316009 147009472526439793177737007)
    ·
      refine ⟨220514208789659689766605511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147009472526439793177737007 220514208789659689766605511)
      ·
        refine ⟨330771313184489534649908267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220514208789659689766605511 330771313184489534649908267)
        ·
          refine ⟨496156969776734301974862401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330771313184489534649908267 496156969776734301974862401)
          ·
            refine ⟨372117727332550726481146801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496156969776734301974862401 372117727332550726481146801)
            ·
              refine ⟨279088295499413044860860101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372117727332550726481146801 279088295499413044860860101)
              ·
                refine ⟨52329055406139945911411269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 279088295499413044860860101 52329055406139945911411269)
                ·
                  refine ⟨9811697888651239858389613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52329055406139945911411269 9811697888651239858389613)
                  ·
                    refine ⟨3679386708244214946896105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9811697888651239858389613 3679386708244214946896105)
                    ·
                      refine ⟨2759540031183161210172079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679386708244214946896105 2759540031183161210172079)
                      ·
                        rfl

theorem cell23_5374185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 3, 2].length) (baseStart_5374185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374185 prefixEnd_5374185 := by exact prefixLift 5374185
  have htrace : WordTrace (prefixWord ++ tailWord_5374185) baseStart_5374185 baseEnd_5374185 := by
    simpa [prefixWord, tailWord_5374185, baseEnd_5374185] using wordTrace_append hprefix tailTrace_5374185
  have hstable : (prefixWord ++ tailWord_5374185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374185).length < 2 ^ (prefixWord ++ tailWord_5374185).sum := by decide
  have hdescent : baseEnd_5374185 < baseStart_5374185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374195 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 1, 5]
def baseStart_5374195 : Nat := 118140960795 + 5374195 * 2 ^ 59
def prefixEnd_5374195 : Nat := 4983230072969 + 3 ^ 40 * 5374195 * 2
def baseEnd_5374195 : Nat := 919848388663235390349011

theorem tailTrace_5374195 : CollatzResearch.WordTrace tailWord_5374195 prefixEnd_5374195 919848388663235390349011 := by
  unfold tailWord_5374195
  simp only [CollatzResearch.WordTrace]
  refine ⟨196012994765216829278180039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130675329843477886185453359 196012994765216829278180039)
  ·
    refine ⟨294019492147825243917270059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196012994765216829278180039 294019492147825243917270059)
    ·
      refine ⟨441029238221737865875905089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294019492147825243917270059 441029238221737865875905089)
      ·
        refine ⟨330771928666303399406928817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441029238221737865875905089 330771928666303399406928817)
        ·
          refine ⟨248078946499727549555196613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330771928666303399406928817 248078946499727549555196613)
          ·
            refine ⟨46514802468698915541599365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248078946499727549555196613 46514802468698915541599365)
            ·
              refine ⟨8721525462881046664049881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46514802468698915541599365 8721525462881046664049881)
              ·
                refine ⟨6541144097160784998037411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8721525462881046664049881 6541144097160784998037411)
                ·
                  refine ⟨9811716145741177497056117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6541144097160784998037411 9811716145741177497056117)
                  ·
                    refine ⟨919848388663235390349011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9811716145741177497056117 919848388663235390349011)
                    ·
                      rfl

theorem cell23_5374195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 5].length) (baseStart_5374195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374195 prefixEnd_5374195 := by exact prefixLift 5374195
  have htrace : WordTrace (prefixWord ++ tailWord_5374195) baseStart_5374195 baseEnd_5374195 := by
    simpa [prefixWord, tailWord_5374195, baseEnd_5374195] using wordTrace_append hprefix tailTrace_5374195
  have hstable : (prefixWord ++ tailWord_5374195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374195).length < 2 ^ (prefixWord ++ tailWord_5374195).sum := by decide
  have hdescent : baseEnd_5374195 < baseStart_5374195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374208 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_5374208 : Nat := 118140960795 + 5374208 * 2 ^ 59
def prefixEnd_5374208 : Nat := 4983230072969 + 3 ^ 40 * 5374208 * 2
def baseEnd_5374208 : Nat := 919850613746071540061491

theorem tailTrace_5374208 : CollatzResearch.WordTrace tailWord_5374208 prefixEnd_5374208 919850613746071540061491 := by
  unfold tailWord_5374208
  simp only [CollatzResearch.WordTrace]
  refine ⟨98006734457084866249201639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130675645942779821665602185 98006734457084866249201639)
  ·
    refine ⟨147010101685627299373802459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98006734457084866249201639 147010101685627299373802459)
    ·
      refine ⟨220515152528440949060703689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147010101685627299373802459 220515152528440949060703689)
      ·
        refine ⟨165386364396330711795527767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220515152528440949060703689 165386364396330711795527767)
        ·
          refine ⟨248079546594496067693291651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165386364396330711795527767 248079546594496067693291651)
          ·
            refine ⟨372119319891744101539937477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248079546594496067693291651 372119319891744101539937477)
            ·
              refine ⟨69772372479702019038738277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 372119319891744101539937477 69772372479702019038738277)
              ·
                refine ⟨13082319839944128569763427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69772372479702019038738277 13082319839944128569763427)
                ·
                  refine ⟨19623479759916192854645141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13082319839944128569763427 19623479759916192854645141)
                  ·
                    refine ⟨919850613746071540061491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19623479759916192854645141 919850613746071540061491)
                    ·
                      rfl

theorem cell23_5374208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_5374208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374208 prefixEnd_5374208 := by exact prefixLift 5374208
  have htrace : WordTrace (prefixWord ++ tailWord_5374208) baseStart_5374208 baseEnd_5374208 := by
    simpa [prefixWord, tailWord_5374208, baseEnd_5374208] using wordTrace_append hprefix tailTrace_5374208
  have hstable : (prefixWord ++ tailWord_5374208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374208).length < 2 ^ (prefixWord ++ tailWord_5374208).sum := by decide
  have hdescent : baseEnd_5374208 < baseStart_5374208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374225 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 4, 4]
def baseStart_5374225 : Nat := 118140960795 + 5374225 * 2 ^ 59
def prefixEnd_5374225 : Nat := 4983230072969 + 3 ^ 40 * 5374225 * 2
def baseEnd_5374225 : Nat := 919853523469780351223965

theorem tailTrace_5374225 : CollatzResearch.WordTrace tailWord_5374225 prefixEnd_5374225 919853523469780351223965 := by
  unfold tailWord_5374225
  simp only [CollatzResearch.WordTrace]
  refine ⟨196014088955108144401772129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130676059303405429601181419 196014088955108144401772129)
  ·
    refine ⟨147010566716331108301329097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196014088955108144401772129 147010566716331108301329097)
    ·
      refine ⟨110257925037248331225996823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147010566716331108301329097 110257925037248331225996823)
      ·
        refine ⟨165386887555872496838995235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110257925037248331225996823 165386887555872496838995235)
        ·
          refine ⟨248080331333808745258492853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165386887555872496838995235 248080331333808745258492853)
          ·
            refine ⟨23257531062544569867983705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248080331333808745258492853 23257531062544569867983705)
            ·
              refine ⟨17443148296908427400987779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23257531062544569867983705 17443148296908427400987779)
              ·
                refine ⟨26164722445362641101481669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17443148296908427400987779 26164722445362641101481669)
                ·
                  refine ⟨4905885458505495206527813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26164722445362641101481669 4905885458505495206527813)
                  ·
                    refine ⟨919853523469780351223965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4905885458505495206527813 919853523469780351223965)
                    ·
                      rfl

theorem cell23_5374225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_5374225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374225 prefixEnd_5374225 := by exact prefixLift 5374225
  have htrace : WordTrace (prefixWord ++ tailWord_5374225) baseStart_5374225 baseEnd_5374225 := by
    simpa [prefixWord, tailWord_5374225, baseEnd_5374225] using wordTrace_append hprefix tailTrace_5374225
  have hstable : (prefixWord ++ tailWord_5374225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374225).length < 2 ^ (prefixWord ++ tailWord_5374225).sum := by decide
  have hdescent : baseEnd_5374225 < baseStart_5374225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374252 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_5374252 : Nat := 118140960795 + 5374252 * 2 ^ 59
def prefixEnd_5374252 : Nat := 4983230072969 + 3 ^ 40 * 5374252 * 2
def baseEnd_5374252 : Nat := 2759574434387012448034271

theorem tailTrace_5374252 : CollatzResearch.WordTrace tailWord_5374252 prefixEnd_5374252 2759574434387012448034271 := by
  unfold tailWord_5374252
  simp only [CollatzResearch.WordTrace]
  refine ⟨98007536863005164006502505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130676715817340218675336673 98007536863005164006502505)
  ·
    refine ⟨73505652647253873004876879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98007536863005164006502505 73505652647253873004876879)
    ·
      refine ⟨110258478970880809507315319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73505652647253873004876879 110258478970880809507315319)
      ·
        refine ⟨165387718456321214260972979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110258478970880809507315319 165387718456321214260972979)
        ·
          refine ⟨248081577684481821391459469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165387718456321214260972979 248081577684481821391459469)
          ·
            refine ⟨93030591631680683021797301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248081577684481821391459469 93030591631680683021797301)
            ·
              refine ⟨8721617965470064033293497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93030591631680683021797301 8721617965470064033293497)
              ·
                refine ⟨6541213474102548024970123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8721617965470064033293497 6541213474102548024970123)
                ·
                  refine ⟨9811820211153822037455185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6541213474102548024970123 9811820211153822037455185)
                  ·
                    refine ⟨7358865158365366528091389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9811820211153822037455185 7358865158365366528091389)
                    ·
                      refine ⟨2759574434387012448034271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7358865158365366528091389 2759574434387012448034271)
                      ·
                        rfl

theorem cell23_5374252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_5374252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374252 prefixEnd_5374252 := by exact prefixLift 5374252
  have htrace : WordTrace (prefixWord ++ tailWord_5374252) baseStart_5374252 baseEnd_5374252 := by
    simpa [prefixWord, tailWord_5374252, baseEnd_5374252] using wordTrace_append hprefix tailTrace_5374252
  have hstable : (prefixWord ++ tailWord_5374252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374252).length < 2 ^ (prefixWord ++ tailWord_5374252).sum := by decide
  have hdescent : baseEnd_5374252 < baseStart_5374252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374276 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5374276 : Nat := 118140960795 + 5374276 * 2 ^ 59
def prefixEnd_5374276 : Nat := 4983230072969 + 3 ^ 40 * 5374276 * 2
def baseEnd_5374276 : Nat := 919862252640906784711387

theorem tailTrace_5374276 : CollatzResearch.WordTrace tailWord_5374276 prefixEnd_5374276 919862252640906784711387 := by
  unfold tailWord_5374276
  simp only [CollatzResearch.WordTrace]
  refine ⟨98007974538961690055939341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130677299385282253407919121 98007974538961690055939341)
  ·
    refine ⟨36752990452110633770977253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98007974538961690055939341 36752990452110633770977253)
    ·
      refine ⟨6891185709770743832058235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36752990452110633770977253 6891185709770743832058235)
      ·
        refine ⟨10336778564656115748087353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6891185709770743832058235 10336778564656115748087353)
        ·
          refine ⟨7752583923492086811065515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10336778564656115748087353 7752583923492086811065515)
          ·
            refine ⟨11628875885238130216598273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752583923492086811065515 11628875885238130216598273)
            ·
              refine ⟨8721656913928597662448705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11628875885238130216598273 8721656913928597662448705)
              ·
                refine ⟨6541242685446448246836529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8721656913928597662448705 6541242685446448246836529)
                ·
                  refine ⟨4905932014084836185127397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6541242685446448246836529 4905932014084836185127397)
                  ·
                    refine ⟨919862252640906784711387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4905932014084836185127397 919862252640906784711387)
                    ·
                      rfl

theorem cell23_5374276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5374276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374276 prefixEnd_5374276 := by exact prefixLift 5374276
  have htrace : WordTrace (prefixWord ++ tailWord_5374276) baseStart_5374276 baseEnd_5374276 := by
    simpa [prefixWord, tailWord_5374276, baseEnd_5374276] using wordTrace_append hprefix tailTrace_5374276
  have hstable : (prefixWord ++ tailWord_5374276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374276).length < 2 ^ (prefixWord ++ tailWord_5374276).sum := by decide
  have hdescent : baseEnd_5374276 < baseStart_5374276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374345 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 7]
def baseStart_5374345 : Nat := 118140960795 + 5374345 * 2 ^ 59
def prefixEnd_5374345 : Nat := 4983230072969 + 3 ^ 40 * 5374345 * 2
def baseEnd_5374345 : Nat := 306624687565320064907927

theorem tailTrace_5374345 : CollatzResearch.WordTrace tailWord_5374345 prefixEnd_5374345 306624687565320064907927 := by
  unfold tailWord_5374345
  simp only [CollatzResearch.WordTrace]
  refine ⟨196018465714673404896140489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130678977143115603264093659 196018465714673404896140489)
  ·
    refine ⟨147013849286005053672105367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196018465714673404896140489 147013849286005053672105367)
    ·
      refine ⟨220520773929007580508158051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147013849286005053672105367 220520773929007580508158051)
      ·
        refine ⟨330781160893511370762237077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220520773929007580508158051 330781160893511370762237077)
        ·
          refine ⟨15505366916883345504479863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 330781160893511370762237077 15505366916883345504479863)
          ·
            refine ⟨23258050375325018256719795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15505366916883345504479863 23258050375325018256719795)
            ·
              refine ⟨34887075562987527385079693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23258050375325018256719795 34887075562987527385079693)
              ·
                refine ⟨13082653336120322769404885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34887075562987527385079693 13082653336120322769404885)
                ·
                  refine ⟨306624687565320064907927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13082653336120322769404885 306624687565320064907927)
                  ·
                    rfl

theorem cell23_5374345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 7].length) (baseStart_5374345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374345 prefixEnd_5374345 := by exact prefixLift 5374345
  have htrace : WordTrace (prefixWord ++ tailWord_5374345) baseStart_5374345 baseEnd_5374345 := by
    simpa [prefixWord, tailWord_5374345, baseEnd_5374345] using wordTrace_append hprefix tailTrace_5374345
  have hstable : (prefixWord ++ tailWord_5374345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374345).length < 2 ^ (prefixWord ++ tailWord_5374345).sum := by decide
  have hdescent : baseEnd_5374345 < baseStart_5374345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374396 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 5]
def baseStart_5374396 : Nat := 118140960795 + 5374396 * 2 ^ 59
def prefixEnd_5374396 : Nat := 4983230072969 + 3 ^ 40 * 5374396 * 2
def baseEnd_5374396 : Nat := 306627597289028876070401

theorem tailTrace_5374396 : CollatzResearch.WordTrace tailWord_5374396 prefixEnd_5374396 306627597289028876070401 := by
  unfold tailWord_5374396
  simp only [CollatzResearch.WordTrace]
  refine ⟨98010162918744320303123521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130680217224992427070831361 98010162918744320303123521)
  ·
    refine ⟨73507622189058240227342641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98010162918744320303123521 73507622189058240227342641)
    ·
      refine ⟨55130716641793680170506981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73507622189058240227342641 55130716641793680170506981)
      ·
        refine ⟨10337009370336315031970059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55130716641793680170506981 10337009370336315031970059)
        ·
          refine ⟨15505514055504472547955089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10337009370336315031970059 15505514055504472547955089)
          ·
            refine ⟨11629135541628354410966317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15505514055504472547955089 11629135541628354410966317)
            ·
              refine ⟨4360925828110632904112369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11629135541628354410966317 4360925828110632904112369)
              ·
                refine ⟨3270694371082974678084277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4360925828110632904112369 3270694371082974678084277)
                ·
                  refine ⟨306627597289028876070401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3270694371082974678084277 306627597289028876070401)
                  ·
                    rfl

theorem cell23_5374396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_5374396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374396 prefixEnd_5374396 := by exact prefixLift 5374396
  have htrace : WordTrace (prefixWord ++ tailWord_5374396) baseStart_5374396 baseEnd_5374396 := by
    simpa [prefixWord, tailWord_5374396, baseEnd_5374396] using wordTrace_append hprefix tailTrace_5374396
  have hstable : (prefixWord ++ tailWord_5374396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374396).length < 2 ^ (prefixWord ++ tailWord_5374396).sum := by decide
  have hdescent : baseEnd_5374396 < baseStart_5374396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374429 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_5374429 : Nat := 118140960795 + 5374429 * 2 ^ 59
def prefixEnd_5374429 : Nat := 4983230072969 + 3 ^ 40 * 5374429 * 2
def baseEnd_5374429 : Nat := 2759665320462858255520957

theorem tailTrace_5374429 : CollatzResearch.WordTrace tailWord_5374429 prefixEnd_5374429 2759665320462858255520957 := by
  unfold tailWord_5374429
  simp only [CollatzResearch.WordTrace]
  refine ⟨196021529446369087242198341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130681019630912724828132227 196021529446369087242198341)
  ·
    refine ⟨36754036771194203857912189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196021529446369087242198341 36754036771194203857912189)
    ·
      refine ⟨13782763789197826446717071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36754036771194203857912189 13782763789197826446717071)
      ·
        refine ⟨20674145683796739670075607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13782763789197826446717071 20674145683796739670075607)
        ·
          refine ⟨31011218525695109505113411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20674145683796739670075607 31011218525695109505113411)
          ·
            refine ⟨46516827788542664257670117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31011218525695109505113411 46516827788542664257670117)
            ·
              refine ⟨8721905210351749548313147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46516827788542664257670117 8721905210351749548313147)
              ·
                refine ⟨13082857815527624322469721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8721905210351749548313147 13082857815527624322469721)
                ·
                  refine ⟨9812143361645718241852291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13082857815527624322469721 9812143361645718241852291)
                  ·
                    refine ⟨14718215042468577362778437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9812143361645718241852291 14718215042468577362778437)
                    ·
                      refine ⟨2759665320462858255520957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14718215042468577362778437 2759665320462858255520957)
                      ·
                        rfl

theorem cell23_5374429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_5374429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374429 prefixEnd_5374429 := by exact prefixLift 5374429
  have htrace : WordTrace (prefixWord ++ tailWord_5374429) baseStart_5374429 baseEnd_5374429 := by
    simpa [prefixWord, tailWord_5374429, baseEnd_5374429] using wordTrace_append hprefix tailTrace_5374429
  have hstable : (prefixWord ++ tailWord_5374429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374429).length < 2 ^ (prefixWord ++ tailWord_5374429).sum := by decide
  have hdescent : baseEnd_5374429 < baseStart_5374429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374499 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 1, 5]
def baseStart_5374499 : Nat := 118140960795 + 5374499 * 2 ^ 59
def prefixEnd_5374499 : Nat := 4983230072969 + 3 ^ 40 * 5374499 * 2
def baseEnd_5374499 : Nat := 919900421369557660548545

theorem tailTrace_5374499 : CollatzResearch.WordTrace tailWord_5374499 prefixEnd_5374499 919900421369557660548545 := by
  unfold tailWord_5374499
  simp only [CollatzResearch.WordTrace]
  refine ⟨196024082556115489197246551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130682721704076992798164367 196024082556115489197246551)
  ·
    refine ⟨294036123834173233795869827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196024082556115489197246551 294036123834173233795869827)
    ·
      refine ⟨441054185751259850693804741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294036123834173233795869827 441054185751259850693804741)
      ·
        refine ⟨82697659828361222005088389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441054185751259850693804741 82697659828361222005088389)
        ·
          refine ⟨15505811217817729125954073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82697659828361222005088389 15505811217817729125954073)
          ·
            refine ⟨11629358413363296844465555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15505811217817729125954073 11629358413363296844465555)
            ·
              refine ⟨17444037620044945266698333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11629358413363296844465555 17444037620044945266698333)
              ·
                refine ⟨6541514107516854475011875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17444037620044945266698333 6541514107516854475011875)
                ·
                  refine ⟨9812271161275281712517813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6541514107516854475011875 9812271161275281712517813)
                  ·
                    refine ⟨919900421369557660548545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9812271161275281712517813 919900421369557660548545)
                    ·
                      rfl

theorem cell23_5374499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 5].length) (baseStart_5374499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374499 prefixEnd_5374499 := by exact prefixLift 5374499
  have htrace : WordTrace (prefixWord ++ tailWord_5374499) baseStart_5374499 baseEnd_5374499 := by
    simpa [prefixWord, tailWord_5374499, baseEnd_5374499] using wordTrace_append hprefix tailTrace_5374499
  have hstable : (prefixWord ++ tailWord_5374499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374499).length < 2 ^ (prefixWord ++ tailWord_5374499).sum := by decide
  have hdescent : baseEnd_5374499 < baseStart_5374499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374503 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 6]
def baseStart_5374503 : Nat := 118140960795 + 5374503 * 2 ^ 59
def prefixEnd_5374503 : Nat := 4983230072969 + 3 ^ 40 * 5374503 * 2
def baseEnd_5374503 : Nat := 306633702003476773999513

theorem tailTrace_5374503 : CollatzResearch.WordTrace tailWord_5374503 prefixEnd_5374503 306633702003476773999513 := by
  unfold tailWord_5374503
  simp only [CollatzResearch.WordTrace]
  refine ⟨196024228448100997880392163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130682818965400665253594775 196024228448100997880392163)
  ·
    refine ⟨294036342672151496820588245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196024228448100997880392163 294036342672151496820588245)
    ·
      refine ⟨6891476781378550706732537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 294036342672151496820588245 6891476781378550706732537)
      ·
        refine ⟨5168607586033913030049403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6891476781378550706732537 5168607586033913030049403)
        ·
          refine ⟨7752911379050869545074105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5168607586033913030049403 7752911379050869545074105)
          ·
            refine ⟨5814683534288152158805579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7752911379050869545074105 5814683534288152158805579)
            ·
              refine ⟨8722025301432228238208369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5814683534288152158805579 8722025301432228238208369)
              ·
                refine ⟨6541518976074171178656277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8722025301432228238208369 6541518976074171178656277)
                ·
                  refine ⟨306633702003476773999513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6541518976074171178656277 306633702003476773999513)
                  ·
                    rfl

theorem cell23_5374503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 6].length) (baseStart_5374503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374503 prefixEnd_5374503 := by exact prefixLift 5374503
  have htrace : WordTrace (prefixWord ++ tailWord_5374503) baseStart_5374503 baseEnd_5374503 := by
    simpa [prefixWord, tailWord_5374503, baseEnd_5374503] using wordTrace_append hprefix tailTrace_5374503
  have hstable : (prefixWord ++ tailWord_5374503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374503).length < 2 ^ (prefixWord ++ tailWord_5374503).sum := by decide
  have hdescent : baseEnd_5374503 < baseStart_5374503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374522 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_5374522 : Nat := 118140960795 + 5374522 * 2 ^ 59
def prefixEnd_5374522 : Nat := 4983230072969 + 3 ^ 40 * 5374522 * 2
def baseEnd_5374522 : Nat := 2759713074163726391658029

theorem tailTrace_5374522 : CollatzResearch.WordTrace tailWord_5374522 prefixEnd_5374522 2759713074163726391658029 := by
  unfold tailWord_5374522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49006230358758041031333455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130683280956688109416889213 49006230358758041031333455)
  ·
    refine ⟨73509345538137061547000183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49006230358758041031333455 73509345538137061547000183)
    ·
      refine ⟨110264018307205592320500275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73509345538137061547000183 110264018307205592320500275)
      ·
        refine ⟨165396027460808388480750413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110264018307205592320500275 165396027460808388480750413)
        ·
          refine ⟨62023510297803145680281405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165396027460808388480750413 62023510297803145680281405)
          ·
            refine ⟨23258816361676179630105527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62023510297803145680281405 23258816361676179630105527)
            ·
              refine ⟨34888224542514269445158291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23258816361676179630105527 34888224542514269445158291)
              ·
                refine ⟨52332336813771404167737437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34888224542514269445158291 52332336813771404167737437)
                ·
                  refine ⟨19624626305164276562901539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52332336813771404167737437 19624626305164276562901539)
                  ·
                    refine ⟨29436939457746414844352309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19624626305164276562901539 29436939457746414844352309)
                    ·
                      refine ⟨2759713074163726391658029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29436939457746414844352309 2759713074163726391658029)
                      ·
                        rfl

theorem cell23_5374522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_5374522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374522 prefixEnd_5374522 := by exact prefixLift 5374522
  have htrace : WordTrace (prefixWord ++ tailWord_5374522) baseStart_5374522 baseEnd_5374522 := by
    simpa [prefixWord, tailWord_5374522, baseEnd_5374522] using wordTrace_append hprefix tailTrace_5374522
  have hstable : (prefixWord ++ tailWord_5374522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374522).length < 2 ^ (prefixWord ++ tailWord_5374522).sum := by decide
  have hdescent : baseEnd_5374522 < baseStart_5374522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374529 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 1, 6]
def baseStart_5374529 : Nat := 118140960795 + 5374529 * 2 ^ 59
def prefixEnd_5374529 : Nat := 4983230072969 + 3 ^ 40 * 5374529 * 2
def baseEnd_5374529 : Nat := 919905556176102621423499

theorem tailTrace_5374529 : CollatzResearch.WordTrace tailWord_5374529 prefixEnd_5374529 919905556176102621423499 := by
  unfold tailWord_5374529
  simp only [CollatzResearch.WordTrace]
  refine ⟨196025176746006804320838641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130683451164004536213892427 196025176746006804320838641)
  ·
    refine ⟨147018882559505103240628981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196025176746006804320838641 147018882559505103240628981)
    ·
      refine ⟨13783020239953603428808967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147018882559505103240628981 13783020239953603428808967)
      ·
        refine ⟨20674530359930405143213451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13783020239953603428808967 20674530359930405143213451)
        ·
          refine ⟨31011795539895607714820177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20674530359930405143213451 31011795539895607714820177)
          ·
            refine ⟨23258846654921705786115133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31011795539895607714820177 23258846654921705786115133)
            ·
              refine ⟨8722067495595639669793175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23258846654921705786115133 8722067495595639669793175)
              ·
                refine ⟨13083101243393459504689763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8722067495595639669793175 13083101243393459504689763)
                ·
                  refine ⟨19624651865090189257034645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13083101243393459504689763 19624651865090189257034645)
                  ·
                    refine ⟨919905556176102621423499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19624651865090189257034645 919905556176102621423499)
                    ·
                      rfl

theorem cell23_5374529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_5374529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374529 prefixEnd_5374529 := by exact prefixLift 5374529
  have htrace : WordTrace (prefixWord ++ tailWord_5374529) baseStart_5374529 baseEnd_5374529 := by
    simpa [prefixWord, tailWord_5374529, baseEnd_5374529] using wordTrace_append hprefix tailTrace_5374529
  have hstable : (prefixWord ++ tailWord_5374529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374529).length < 2 ^ (prefixWord ++ tailWord_5374529).sum := by decide
  have hdescent : baseEnd_5374529 < baseStart_5374529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374539 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 3]
def baseStart_5374539 : Nat := 118140960795 + 5374539 * 2 ^ 59
def prefixEnd_5374539 : Nat := 4983230072969 + 3 ^ 40 * 5374539 * 2
def baseEnd_5374539 : Nat := 2759721803334852825145451

theorem tailTrace_5374539 : CollatzResearch.WordTrace tailWord_5374539 prefixEnd_5374539 2759721803334852825145451 := by
  unfold tailWord_5374539
  simp only [CollatzResearch.WordTrace]
  refine ⟨196025541475970576028702671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130683694317313717352468447 196025541475970576028702671)
  ·
    refine ⟨294038312213955864043054007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196025541475970576028702671 294038312213955864043054007)
    ·
      refine ⟨441057468320933796064581011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294038312213955864043054007 441057468320933796064581011)
      ·
        refine ⟨661586202481400694096871517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441057468320933796064581011 661586202481400694096871517)
        ·
          refine ⟨248094825930525260286326819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 661586202481400694096871517 248094825930525260286326819)
          ·
            refine ⟨372142238895787890429490229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248094825930525260286326819 372142238895787890429490229)
            ·
              refine ⟨34888334896480114727764709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372142238895787890429490229 34888334896480114727764709)
              ·
                refine ⟨6541562793090021511455883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34888334896480114727764709 6541562793090021511455883)
                ·
                  refine ⟨9812344189635032267183825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6541562793090021511455883 9812344189635032267183825)
                  ·
                    refine ⟨7359258142226274200387869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9812344189635032267183825 7359258142226274200387869)
                    ·
                      refine ⟨2759721803334852825145451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7359258142226274200387869 2759721803334852825145451)
                      ·
                        rfl

theorem cell23_5374539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 2, 3].length) (baseStart_5374539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374539 prefixEnd_5374539 := by exact prefixLift 5374539
  have htrace : WordTrace (prefixWord ++ tailWord_5374539) baseStart_5374539 baseEnd_5374539 := by
    simpa [prefixWord, tailWord_5374539, baseEnd_5374539] using wordTrace_append hprefix tailTrace_5374539
  have hstable : (prefixWord ++ tailWord_5374539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374539).length < 2 ^ (prefixWord ++ tailWord_5374539).sum := by decide
  have hdescent : baseEnd_5374539 < baseStart_5374539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374556 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5374556 : Nat := 118140960795 + 5374556 * 2 ^ 59
def prefixEnd_5374556 : Nat := 4983230072969 + 3 ^ 40 * 5374556 * 2
def baseEnd_5374556 : Nat := 2759730532505979258632873

theorem tailTrace_5374556 : CollatzResearch.WordTrace tailWord_5374556 prefixEnd_5374556 2759730532505979258632873 := by
  unfold tailWord_5374556
  simp only [CollatzResearch.WordTrace]
  refine ⟨98013080758454493966035761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130684107677939325288047681 98013080758454493966035761)
  ·
    refine ⟨73509810568840870474526821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98013080758454493966035761 73509810568840870474526821)
    ·
      refine ⟨13783089481657663213973779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73509810568840870474526821 13783089481657663213973779)
      ·
        refine ⟨20674634222486494820960669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13783089481657663213973779 20674634222486494820960669)
        ·
          refine ⟨7752987833432435557860251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20674634222486494820960669 7752987833432435557860251)
          ·
            refine ⟨11629481750148653336790377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752987833432435557860251 11629481750148653336790377)
            ·
              refine ⟨8722111312611490002592783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11629481750148653336790377 8722111312611490002592783)
              ·
                refine ⟨13083166968917235003889175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8722111312611490002592783 13083166968917235003889175)
                ·
                  refine ⟨19624750453375852505833763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13083166968917235003889175 19624750453375852505833763)
                  ·
                    refine ⟨29437125680063778758750645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19624750453375852505833763 29437125680063778758750645)
                    ·
                      refine ⟨2759730532505979258632873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29437125680063778758750645 2759730532505979258632873)
                      ·
                        rfl

theorem cell23_5374556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5374556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374556 prefixEnd_5374556 := by exact prefixLift 5374556
  have htrace : WordTrace (prefixWord ++ tailWord_5374556) baseStart_5374556 baseEnd_5374556 := by
    simpa [prefixWord, tailWord_5374556, baseEnd_5374556] using wordTrace_append hprefix tailTrace_5374556
  have hstable : (prefixWord ++ tailWord_5374556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374556).length < 2 ^ (prefixWord ++ tailWord_5374556).sum := by decide
  have hdescent : baseEnd_5374556 < baseStart_5374556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374639 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_5374639 : Nat := 118140960795 + 5374639 * 2 ^ 59
def prefixEnd_5374639 : Nat := 4983230072969 + 3 ^ 40 * 5374639 * 2
def baseEnd_5374639 : Nat := 2759773151400302433894991

theorem tailTrace_5374639 : CollatzResearch.WordTrace tailWord_5374639 prefixEnd_5374639 2759773151400302433894991 := by
  unfold tailWord_5374639
  simp only [CollatzResearch.WordTrace]
  refine ⟨196029188775608293107342971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130686125850405528738228647 196029188775608293107342971)
  ·
    refine ⟨294043783163412439661014457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196029188775608293107342971 294043783163412439661014457)
    ·
      refine ⟨220532837372559329745760843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294043783163412439661014457 220532837372559329745760843)
      ·
        refine ⟨330799256058838994618641265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220532837372559329745760843 330799256058838994618641265)
        ·
          refine ⟨248099442044129245963980949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330799256058838994618641265 248099442044129245963980949)
          ·
            refine ⟨11629661345818558404561607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248099442044129245963980949 11629661345818558404561607)
            ·
              refine ⟨17444492018727837606842411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11629661345818558404561607 17444492018727837606842411)
              ·
                refine ⟨26166738028091756410263617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17444492018727837606842411 26166738028091756410263617)
                ·
                  refine ⟨19625053521068817307697713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26166738028091756410263617 19625053521068817307697713)
                  ·
                    refine ⟨14718790140801612980773285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19625053521068817307697713 14718790140801612980773285)
                    ·
                      refine ⟨2759773151400302433894991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14718790140801612980773285 2759773151400302433894991)
                      ·
                        rfl

theorem cell23_5374639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_5374639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374639 prefixEnd_5374639 := by exact prefixLift 5374639
  have htrace : WordTrace (prefixWord ++ tailWord_5374639) baseStart_5374639 baseEnd_5374639 := by
    simpa [prefixWord, tailWord_5374639, baseEnd_5374639] using wordTrace_append hprefix tailTrace_5374639
  have hstable : (prefixWord ++ tailWord_5374639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374639).length < 2 ^ (prefixWord ++ tailWord_5374639).sum := by decide
  have hdescent : baseEnd_5374639 < baseStart_5374639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374643 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 2, 2, 2]
def baseStart_5374643 : Nat := 118140960795 + 5374643 * 2 ^ 59
def prefixEnd_5374643 : Nat := 4983230072969 + 3 ^ 40 * 5374643 * 2
def baseEnd_5374643 : Nat := 2759775205322920418244973

theorem tailTrace_5374643 : CollatzResearch.WordTrace tailWord_5374643 prefixEnd_5374643 2759775205322920418244973 := by
  unfold tailWord_5374643
  simp only [CollatzResearch.WordTrace]
  refine ⟨196029334667593801790488583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130686223111729201193659055 196029334667593801790488583)
  ·
    refine ⟨294044002001390702685732875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196029334667593801790488583 294044002001390702685732875)
    ·
      refine ⟨441066003002086054028599313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294044002001390702685732875 441066003002086054028599313)
      ·
        refine ⟨330799502251564540521449485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441066003002086054028599313 330799502251564540521449485)
        ·
          refine ⟨124049813344336702695543557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330799502251564540521449485 124049813344336702695543557)
          ·
            refine ⟨23259340002063131755414417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124049813344336702695543557 23259340002063131755414417)
            ·
              refine ⟨17444505001547348816560813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23259340002063131755414417 17444505001547348816560813)
              ·
                refine ⟨6541689375580255806210305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17444505001547348816560813 6541689375580255806210305)
                ·
                  refine ⟨4906267031685191854657729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6541689375580255806210305 4906267031685191854657729)
                  ·
                    refine ⟨3679700273763893890993297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4906267031685191854657729 3679700273763893890993297)
                    ·
                      refine ⟨2759775205322920418244973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679700273763893890993297 2759775205322920418244973)
                      ·
                        rfl

theorem cell23_5374643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 2, 2].length) (baseStart_5374643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374643 prefixEnd_5374643 := by exact prefixLift 5374643
  have htrace : WordTrace (prefixWord ++ tailWord_5374643) baseStart_5374643 baseEnd_5374643 := by
    simpa [prefixWord, tailWord_5374643, baseEnd_5374643] using wordTrace_append hprefix tailTrace_5374643
  have hstable : (prefixWord ++ tailWord_5374643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374643).length < 2 ^ (prefixWord ++ tailWord_5374643).sum := by decide
  have hdescent : baseEnd_5374643 < baseStart_5374643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374666 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_5374666 : Nat := 118140960795 + 5374666 * 2 ^ 59
def prefixEnd_5374666 : Nat := 4983230072969 + 3 ^ 40 * 5374666 * 2
def baseEnd_5374666 : Nat := 306643001708663758695263

theorem tailTrace_5374666 : CollatzResearch.WordTrace tailWord_5374666 prefixEnd_5374666 306643001708663758695263 := by
  unfold tailWord_5374666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49007543386627619179643963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130686782364340317812383901 49007543386627619179643963)
  ·
    refine ⟨73511315079941428769465945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49007543386627619179643963 73511315079941428769465945)
    ·
      refine ⟨55133486309956071577099459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73511315079941428769465945 55133486309956071577099459)
      ·
        refine ⟨82700229464934107365649189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55133486309956071577099459 82700229464934107365649189)
        ·
          refine ⟨15506293024675145131059223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82700229464934107365649189 15506293024675145131059223)
          ·
            refine ⟨23259439537012717696588835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15506293024675145131059223 23259439537012717696588835)
            ·
              refine ⟨34889159305519076544883253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23259439537012717696588835 34889159305519076544883253)
              ·
                refine ⟨3270858684892413426082805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34889159305519076544883253 3270858684892413426082805)
                ·
                  refine ⟨306643001708663758695263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3270858684892413426082805 306643001708663758695263)
                  ·
                    rfl

theorem cell23_5374666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_5374666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374666 prefixEnd_5374666 := by exact prefixLift 5374666
  have htrace : WordTrace (prefixWord ++ tailWord_5374666) baseStart_5374666 baseEnd_5374666 := by
    simpa [prefixWord, tailWord_5374666, baseEnd_5374666] using wordTrace_append hprefix tailTrace_5374666
  have hstable : (prefixWord ++ tailWord_5374666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374666).length < 2 ^ (prefixWord ++ tailWord_5374666).sum := by decide
  have hdescent : baseEnd_5374666 < baseStart_5374666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374739 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 6]
def baseStart_5374739 : Nat := 118140960795 + 5374739 * 2 ^ 59
def prefixEnd_5374739 : Nat := 4983230072969 + 3 ^ 40 * 5374739 * 2
def baseEnd_5374739 : Nat := 306647166607305782516059

theorem tailTrace_5374739 : CollatzResearch.WordTrace tailWord_5374739 prefixEnd_5374739 306647166607305782516059 := by
  unfold tailWord_5374739
  simp only [CollatzResearch.WordTrace]
  refine ⟨196032836075246010185983271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130688557383497340123988847 196032836075246010185983271)
  ·
    refine ⟨294049254112869015278974907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196032836075246010185983271 294049254112869015278974907)
    ·
      refine ⟨441073881169303522918462361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294049254112869015278974907 441073881169303522918462361)
      ·
        refine ⟨330805410876977642188846771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441073881169303522918462361 330805410876977642188846771)
        ·
          refine ⟨496208116315466463283270157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330805410876977642188846771 496208116315466463283270157)
          ·
            refine ⟨186078043618299923731226309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496208116315466463283270157 186078043618299923731226309)
            ·
              refine ⟨34889633178431235699604933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186078043618299923731226309 34889633178431235699604933)
              ·
                refine ⟨6541806220955856693675925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34889633178431235699604933 6541806220955856693675925)
                ·
                  refine ⟨306647166607305782516059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6541806220955856693675925 306647166607305782516059)
                  ·
                    rfl

theorem cell23_5374739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 6].length) (baseStart_5374739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374739 prefixEnd_5374739 := by exact prefixLift 5374739
  have htrace : WordTrace (prefixWord ++ tailWord_5374739) baseStart_5374739 baseEnd_5374739 := by
    simpa [prefixWord, tailWord_5374739, baseEnd_5374739] using wordTrace_append hprefix tailTrace_5374739
  have hstable : (prefixWord ++ tailWord_5374739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374739).length < 2 ^ (prefixWord ++ tailWord_5374739).sum := by decide
  have hdescent : baseEnd_5374739 < baseStart_5374739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374793 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 2, 3, 2]
def baseStart_5374793 : Nat := 118140960795 + 5374793 * 2 ^ 59
def prefixEnd_5374793 : Nat := 4983230072969 + 3 ^ 40 * 5374793 * 2
def baseEnd_5374793 : Nat := 2759852227421094831369283

theorem tailTrace_5374793 : CollatzResearch.WordTrace tailWord_5374793 prefixEnd_5374793 2759852227421094831369283 := by
  unfold tailWord_5374793
  simp only [CollatzResearch.WordTrace]
  refine ⟨196034805617050377408449033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130689870411366918272299355 196034805617050377408449033)
  ·
    refine ⟨147026104212787783056336775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196034805617050377408449033 147026104212787783056336775)
    ·
      refine ⟨220539156319181674584505163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147026104212787783056336775 220539156319181674584505163)
      ·
        refine ⟨330808734478772511876757745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220539156319181674584505163 330808734478772511876757745)
        ·
          refine ⟨248106550859079383907568309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330808734478772511876757745 248106550859079383907568309)
          ·
            refine ⟨23259989143038692241334529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248106550859079383907568309 23259989143038692241334529)
            ·
              refine ⟨17444991857279019181000897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23259989143038692241334529 17444991857279019181000897)
              ·
                refine ⟨13083743892959264385750673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17444991857279019181000897 13083743892959264385750673)
                ·
                  refine ⟨9812807919719448289313005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13083743892959264385750673 9812807919719448289313005)
                  ·
                    refine ⟨3679802969894793108492377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9812807919719448289313005 3679802969894793108492377)
                    ·
                      refine ⟨2759852227421094831369283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679802969894793108492377 2759852227421094831369283)
                      ·
                        rfl

theorem cell23_5374793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 3, 2].length) (baseStart_5374793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374793 prefixEnd_5374793 := by exact prefixLift 5374793
  have htrace : WordTrace (prefixWord ++ tailWord_5374793) baseStart_5374793 baseEnd_5374793 := by
    simpa [prefixWord, tailWord_5374793, baseEnd_5374793] using wordTrace_append hprefix tailTrace_5374793
  have hstable : (prefixWord ++ tailWord_5374793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374793).length < 2 ^ (prefixWord ++ tailWord_5374793).sum := by decide
  have hdescent : baseEnd_5374793 < baseStart_5374793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374816 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 1, 6]
def baseStart_5374816 : Nat := 118140960795 + 5374816 * 2 ^ 59
def prefixEnd_5374816 : Nat := 4983230072969 + 3 ^ 40 * 5374816 * 2
def baseEnd_5374816 : Nat := 919954679158716080460559

theorem tailTrace_5374816 : CollatzResearch.WordTrace tailWord_5374816 prefixEnd_5374816 919954679158716080460559 := by
  unfold tailWord_5374816
  simp only [CollatzResearch.WordTrace]
  refine ⟨98017822247983526168268151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130690429663978034891024201 98017822247983526168268151)
  ·
    refine ⟨147026733371975289252402227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98017822247983526168268151 147026733371975289252402227)
    ·
      refine ⟨220540100057962933878603341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147026733371975289252402227 220540100057962933878603341)
      ·
        refine ⟨82702537521736100204476253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220540100057962933878603341 82702537521736100204476253)
        ·
          refine ⟨31013451570651037576678595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82702537521736100204476253 31013451570651037576678595)
          ·
            refine ⟨46520177355976556365017893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31013451570651037576678595 46520177355976556365017893)
            ·
              refine ⟨8722533254245604318440855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46520177355976556365017893 8722533254245604318440855)
              ·
                refine ⟨13083799881368406477661283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8722533254245604318440855 13083799881368406477661283)
                ·
                  refine ⟨19625699822052609716491925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13083799881368406477661283 19625699822052609716491925)
                  ·
                    refine ⟨919954679158716080460559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19625699822052609716491925 919954679158716080460559)
                    ·
                      rfl

theorem cell23_5374816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_5374816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374816 prefixEnd_5374816 := by exact prefixLift 5374816
  have htrace : WordTrace (prefixWord ++ tailWord_5374816) baseStart_5374816 baseEnd_5374816 := by
    simpa [prefixWord, tailWord_5374816, baseEnd_5374816] using wordTrace_append hprefix tailTrace_5374816
  have hstable : (prefixWord ++ tailWord_5374816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374816).length < 2 ^ (prefixWord ++ tailWord_5374816).sum := by decide
  have hdescent : baseEnd_5374816 < baseStart_5374816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374857 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 1, 2, 2]
def baseStart_5374857 : Nat := 118140960795 + 5374857 * 2 ^ 59
def prefixEnd_5374857 : Nat := 4983230072969 + 3 ^ 40 * 5374857 * 2
def baseEnd_5374857 : Nat := 2759885090182982580968989

theorem tailTrace_5374857 : CollatzResearch.WordTrace tailWord_5374857 prefixEnd_5374857 2759885090182982580968989 := by
  unfold tailWord_5374857
  simp only [CollatzResearch.WordTrace]
  refine ⟨196037139888818516338778825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130691426592545677559185883 196037139888818516338778825)
  ·
    refine ⟨147027854916613887254084119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196037139888818516338778825 147027854916613887254084119)
    ·
      refine ⟨220541782374920830881126179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147027854916613887254084119 220541782374920830881126179)
      ·
        refine ⟨330812673562381246321689269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220541782374920830881126179 330812673562381246321689269)
        ·
          refine ⟨31013688146473241842658369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330812673562381246321689269 31013688146473241842658369)
          ·
            refine ⟨23260266109854931381993777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31013688146473241842658369 23260266109854931381993777)
            ·
              refine ⟨17445199582391198536495333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23260266109854931381993777 17445199582391198536495333)
              ·
                refine ⟨3270974921698349725592875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17445199582391198536495333 3270974921698349725592875)
                ·
                  refine ⟨4906462382547524588389313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3270974921698349725592875 4906462382547524588389313)
                  ·
                    refine ⟨3679846786910643441291985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4906462382547524588389313 3679846786910643441291985)
                    ·
                      refine ⟨2759885090182982580968989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679846786910643441291985 2759885090182982580968989)
                      ·
                        rfl

theorem cell23_5374857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 2, 2].length) (baseStart_5374857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374857 prefixEnd_5374857 := by exact prefixLift 5374857
  have htrace : WordTrace (prefixWord ++ tailWord_5374857) baseStart_5374857 baseEnd_5374857 := by
    simpa [prefixWord, tailWord_5374857, baseEnd_5374857] using wordTrace_append hprefix tailTrace_5374857
  have hstable : (prefixWord ++ tailWord_5374857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374857).length < 2 ^ (prefixWord ++ tailWord_5374857).sum := by decide
  have hdescent : baseEnd_5374857 < baseStart_5374857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374859 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 9]
def baseStart_5374859 : Nat := 118140960795 + 5374859 * 2 ^ 59
def prefixEnd_5374859 : Nat := 4983230072969 + 3 ^ 40 * 5374859 * 2
def baseEnd_5374859 : Nat := 919962039048097191047993

theorem tailTrace_5374859 : CollatzResearch.WordTrace tailWord_5374859 prefixEnd_5374859 919962039048097191047993 := by
  unfold tailWord_5374859
  simp only [CollatzResearch.WordTrace]
  refine ⟨196037212834811270680351631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130691475223207513786901087 196037212834811270680351631)
  ·
    refine ⟨294055819252216906020527447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196037212834811270680351631 294055819252216906020527447)
    ·
      refine ⟨441083728878325359030791171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294055819252216906020527447 441083728878325359030791171)
      ·
        refine ⟨661625593317488038546186757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441083728878325359030791171 661625593317488038546186757)
        ·
          refine ⟨124054798747029007227410017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 661625593317488038546186757 124054798747029007227410017)
          ·
            refine ⟨93041099060271755420557513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124054798747029007227410017 93041099060271755420557513)
            ·
              refine ⟨69780824295203816565418135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93041099060271755420557513 69780824295203816565418135)
              ·
                refine ⟨104671236442805724848127203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69780824295203816565418135 104671236442805724848127203)
                ·
                  refine ⟨157006854664208587272190805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104671236442805724848127203 157006854664208587272190805)
                  ·
                    refine ⟨919962039048097191047993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157006854664208587272190805 919962039048097191047993)
                    ·
                      rfl

theorem cell23_5374859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 9].length) (baseStart_5374859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374859 prefixEnd_5374859 := by exact prefixLift 5374859
  have htrace : WordTrace (prefixWord ++ tailWord_5374859) baseStart_5374859 baseEnd_5374859 := by
    simpa [prefixWord, tailWord_5374859, baseEnd_5374859] using wordTrace_append hprefix tailTrace_5374859
  have hstable : (prefixWord ++ tailWord_5374859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374859).length < 2 ^ (prefixWord ++ tailWord_5374859).sum := by decide
  have hdescent : baseEnd_5374859 < baseStart_5374859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374883 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 3, 3, 2]
def baseStart_5374883 : Nat := 118140960795 + 5374883 * 2 ^ 59
def prefixEnd_5374883 : Nat := 4983230072969 + 3 ^ 40 * 5374883 * 2
def baseEnd_5374883 : Nat := 2759898440679999479243869

theorem tailTrace_5374883 : CollatzResearch.WordTrace tailWord_5374883 prefixEnd_5374883 2759898440679999479243869 := by
  unfold tailWord_5374883
  simp only [CollatzResearch.WordTrace]
  refine ⟨196038088186724322779225303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130692058791149548519483535 196038088186724322779225303)
  ·
    refine ⟨294057132280086484168837955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196038088186724322779225303 294057132280086484168837955)
    ·
      refine ⟨441085698420129726253256933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294057132280086484168837955 441085698420129726253256933)
      ·
        refine ⟨82703568453774323672485675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441085698420129726253256933 82703568453774323672485675)
        ·
          refine ⟨124055352680661485508728513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82703568453774323672485675 124055352680661485508728513)
          ·
            refine ⟨93041514510496114131546385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124055352680661485508728513 93041514510496114131546385)
            ·
              refine ⟨69781135882872085598659789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93041514510496114131546385 69781135882872085598659789)
              ·
                refine ⟨26167925956077032099497421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69781135882872085598659789 26167925956077032099497421)
                ·
                  refine ⟨9812972233528887037311533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26167925956077032099497421 9812972233528887037311533)
                  ·
                    refine ⟨3679864587573332638991825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9812972233528887037311533 3679864587573332638991825)
                    ·
                      refine ⟨2759898440679999479243869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679864587573332638991825 2759898440679999479243869)
                      ·
                        rfl

theorem cell23_5374883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_5374883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374883 prefixEnd_5374883 := by exact prefixLift 5374883
  have htrace : WordTrace (prefixWord ++ tailWord_5374883) baseStart_5374883 baseEnd_5374883 := by
    simpa [prefixWord, tailWord_5374883, baseEnd_5374883] using wordTrace_append hprefix tailTrace_5374883
  have hstable : (prefixWord ++ tailWord_5374883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374883).length < 2 ^ (prefixWord ++ tailWord_5374883).sum := by decide
  have hdescent : baseEnd_5374883 < baseStart_5374883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374934 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5374934 : Nat := 118140960795 + 5374934 * 2 ^ 59
def prefixEnd_5374934 : Nat := 4983230072969 + 3 ^ 40 * 5374934 * 2
def baseEnd_5374934 : Nat := 2759924628193378779706135

theorem tailTrace_5374934 : CollatzResearch.WordTrace tailWord_5374934 prefixEnd_5374934 2759924628193378779706135 := by
  unfold tailWord_5374934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12252496769346222405583241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130693298873026372326221237 12252496769346222405583241)
  ·
    refine ⟨9189372577009666804187431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12252496769346222405583241 9189372577009666804187431)
    ·
      refine ⟨13784058865514500206281147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9189372577009666804187431 13784058865514500206281147)
      ·
        refine ⟨20676088298271750309421721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13784058865514500206281147 20676088298271750309421721)
        ·
          refine ⟨15507066223703812732066291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20676088298271750309421721 15507066223703812732066291)
          ·
            refine ⟨23260599335555719098099437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15507066223703812732066291 23260599335555719098099437)
            ·
              refine ⟨8722724750833394661787289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23260599335555719098099437 8722724750833394661787289)
              ·
                refine ⟨6542043563125045996340467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8722724750833394661787289 6542043563125045996340467)
                ·
                  refine ⟨9813065344687568994510701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6542043563125045996340467 9813065344687568994510701)
                  ·
                    refine ⟨3679899504257838372941513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9813065344687568994510701 3679899504257838372941513)
                    ·
                      refine ⟨2759924628193378779706135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679899504257838372941513 2759924628193378779706135)
                      ·
                        rfl

theorem cell23_5374934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5374934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374934 prefixEnd_5374934 := by exact prefixLift 5374934
  have htrace : WordTrace (prefixWord ++ tailWord_5374934) baseStart_5374934 baseEnd_5374934 := by
    simpa [prefixWord, tailWord_5374934, baseEnd_5374934] using wordTrace_append hprefix tailTrace_5374934
  have hstable : (prefixWord ++ tailWord_5374934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374934).length < 2 ^ (prefixWord ++ tailWord_5374934).sum := by decide
  have hdescent : baseEnd_5374934 < baseStart_5374934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375000 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 2, 5]
def baseStart_5375000 : Nat := 118140960795 + 5375000 * 2 ^ 59
def prefixEnd_5375000 : Nat := 4983230072969 + 3 ^ 40 * 5375000 * 2
def baseEnd_5375000 : Nat := 919986172638858507160277

theorem tailTrace_5375000 : CollatzResearch.WordTrace tailWord_5375000 prefixEnd_5375000 919986172638858507160277 := by
  unfold tailWord_5375000
  simp only [CollatzResearch.WordTrace]
  refine ⟨98021177763650225880617227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130694903684866967840822969 98021177763650225880617227)
  ·
    refine ⟨147031766645475338820925841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98021177763650225880617227 147031766645475338820925841)
    ·
      refine ⟨110273824984106504115694381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147031766645475338820925841 110273824984106504115694381)
      ·
        refine ⟨41352684369039939043385393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110273824984106504115694381 41352684369039939043385393)
        ·
          refine ⟨31014513276779954282539045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41352684369039939043385393 31014513276779954282539045)
          ·
            refine ⟨5815221239396241427976071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31014513276779954282539045 5815221239396241427976071)
            ·
              refine ⟨8722831859094362141964107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5815221239396241427976071 8722831859094362141964107)
              ·
                refine ⟨13084247788641543212946161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8722831859094362141964107 13084247788641543212946161)
                ·
                  refine ⟨9813185841481157409709621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13084247788641543212946161 9813185841481157409709621)
                  ·
                    refine ⟨919986172638858507160277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9813185841481157409709621 919986172638858507160277)
                    ·
                      rfl

theorem cell23_5375000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_5375000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375000 prefixEnd_5375000 := by exact prefixLift 5375000
  have htrace : WordTrace (prefixWord ++ tailWord_5375000) baseStart_5375000 baseEnd_5375000 := by
    simpa [prefixWord, tailWord_5375000, baseEnd_5375000] using wordTrace_append hprefix tailTrace_5375000
  have hstable : (prefixWord ++ tailWord_5375000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375000).length < 2 ^ (prefixWord ++ tailWord_5375000).sum := by decide
  have hdescent : baseEnd_5375000 < baseStart_5375000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375013 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_5375013 : Nat := 118140960795 + 5375013 * 2 ^ 59
def prefixEnd_5375013 : Nat := 4983230072969 + 3 ^ 40 * 5375013 * 2
def baseEnd_5375013 : Nat := 919988397721694656872757

theorem tailTrace_5375013 : CollatzResearch.WordTrace tailWord_5375013 prefixEnd_5375013 919988397721694656872757 := by
  unfold tailWord_5375013
  simp only [CollatzResearch.WordTrace]
  refine ⟨196042829676253354981457693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130695219784168903320971795 196042829676253354981457693)
  ·
    refine ⟨73516061128595008118046635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196042829676253354981457693 73516061128595008118046635)
    ·
      refine ⟨110274091692892512177069953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73516061128595008118046635 110274091692892512177069953)
      ·
        refine ⟨82705568769669384132802465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110274091692892512177069953 82705568769669384132802465)
        ·
          refine ⟨62029176577252038099601849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82705568769669384132802465 62029176577252038099601849)
          ·
            refine ⟨46521882432939028574701387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62029176577252038099601849 46521882432939028574701387)
            ·
              refine ⟨69782823649408542862052081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46521882432939028574701387 69782823649408542862052081)
              ·
                refine ⟨52337117737056407146539061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69782823649408542862052081 52337117737056407146539061)
                ·
                  refine ⟨4906604787849038169988037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52337117737056407146539061 4906604787849038169988037)
                  ·
                    refine ⟨919988397721694656872757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4906604787849038169988037 919988397721694656872757)
                    ·
                      rfl

theorem cell23_5375013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_5375013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375013 prefixEnd_5375013 := by exact prefixLift 5375013
  have htrace : WordTrace (prefixWord ++ tailWord_5375013) baseStart_5375013 baseEnd_5375013 := by
    simpa [prefixWord, tailWord_5375013, baseEnd_5375013] using wordTrace_append hprefix tailTrace_5375013
  have hstable : (prefixWord ++ tailWord_5375013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375013).length < 2 ^ (prefixWord ++ tailWord_5375013).sum := by decide
  have hdescent : baseEnd_5375013 < baseStart_5375013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375056 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_5375056 : Nat := 118140960795 + 5375056 * 2 ^ 59
def prefixEnd_5375056 : Nat := 4983230072969 + 3 ^ 40 * 5375056 * 2
def baseEnd_5375056 : Nat := 919995757611075767460191

theorem tailTrace_5375056 : CollatzResearch.WordTrace tailWord_5375056 prefixEnd_5375056 919995757611075767460191 := by
  unfold tailWord_5375056
  simp only [CollatzResearch.WordTrace]
  refine ⟨98022199007548786662636511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130696265343398382216848681 98022199007548786662636511)
  ·
    refine ⟨147033298511323179993954767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98022199007548786662636511 147033298511323179993954767)
    ·
      refine ⟨220549947766984769990932151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147033298511323179993954767 220549947766984769990932151)
      ·
        refine ⟨330824921650477154986398227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220549947766984769990932151 330824921650477154986398227)
        ·
          refine ⟨496237382475715732479597341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330824921650477154986398227 496237382475715732479597341)
          ·
            refine ⟨186089018428393399679849003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496237382475715732479597341 186089018428393399679849003)
            ·
              refine ⟨279133527642590099519773505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186089018428393399679849003 279133527642590099519773505)
              ·
                refine ⟨209350145731942574639830129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279133527642590099519773505 209350145731942574639830129)
                ·
                  refine ⟨157012609298956930979872597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209350145731942574639830129 157012609298956930979872597)
                  ·
                    refine ⟨919995757611075767460191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157012609298956930979872597 919995757611075767460191)
                    ·
                      rfl

theorem cell23_5375056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_5375056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375056 prefixEnd_5375056 := by exact prefixLift 5375056
  have htrace : WordTrace (prefixWord ++ tailWord_5375056) baseStart_5375056 baseEnd_5375056 := by
    simpa [prefixWord, tailWord_5375056, baseEnd_5375056] using wordTrace_append hprefix tailTrace_5375056
  have hstable : (prefixWord ++ tailWord_5375056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375056).length < 2 ^ (prefixWord ++ tailWord_5375056).sum := by decide
  have hdescent : baseEnd_5375056 < baseStart_5375056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375123 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4]
def baseStart_5375123 : Nat := 118140960795 + 5375123 * 2 ^ 59
def prefixEnd_5375123 : Nat := 4983230072969 + 3 ^ 40 * 5375123 * 2
def baseEnd_5375123 : Nat := 2760021676037078540242765

theorem tailTrace_5375123 : CollatzResearch.WordTrace tailWord_5375123 prefixEnd_5375123 2760021676037078540242765 := by
  unfold tailWord_5375123
  simp only [CollatzResearch.WordTrace]
  refine ⟨196046841705854843767962023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130697894470569895845308015 196046841705854843767962023)
  ·
    refine ⟨294070262558782265651943035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196046841705854843767962023 294070262558782265651943035)
    ·
      refine ⟨441105393838173398477914553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294070262558782265651943035 441105393838173398477914553)
      ·
        refine ⟨330829045378630048858435915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441105393838173398477914553 330829045378630048858435915)
        ·
          refine ⟨496243568067945073287653873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330829045378630048858435915 496243568067945073287653873)
          ·
            refine ⟨372182676050958804965740405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496243568067945073287653873 372182676050958804965740405)
            ·
              refine ⟨34892125879777387965538163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372182676050958804965740405 34892125879777387965538163)
              ·
                refine ⟨52338188819666081948307245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34892125879777387965538163 52338188819666081948307245)
                ·
                  refine ⟨19626820807374780730615217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52338188819666081948307245 19626820807374780730615217)
                  ·
                    refine ⟨14720115605531085547961413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19626820807374780730615217 14720115605531085547961413)
                    ·
                      refine ⟨2760021676037078540242765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14720115605531085547961413 2760021676037078540242765)
                      ·
                        rfl

theorem cell23_5375123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_5375123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375123 prefixEnd_5375123 := by exact prefixLift 5375123
  have htrace : WordTrace (prefixWord ++ tailWord_5375123) baseStart_5375123 baseEnd_5375123 := by
    simpa [prefixWord, tailWord_5375123, baseEnd_5375123] using wordTrace_append hprefix tailTrace_5375123
  have hstable : (prefixWord ++ tailWord_5375123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375123).length < 2 ^ (prefixWord ++ tailWord_5375123).sum := by decide
  have hdescent : baseEnd_5375123 < baseStart_5375123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375137 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 2, 4]
def baseStart_5375137 : Nat := 118140960795 + 5375137 * 2 ^ 59
def prefixEnd_5375137 : Nat := 4983230072969 + 3 ^ 40 * 5375137 * 2
def baseEnd_5375137 : Nat := 920009621588747161822567

theorem tailTrace_5375137 : CollatzResearch.WordTrace tailWord_5375137 prefixEnd_5375137 920009621588747161822567 := by
  unfold tailWord_5375137
  simp only [CollatzResearch.WordTrace]
  refine ⟨196047352327804124158971665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130698234885202749439314443 196047352327804124158971665)
  ·
    refine ⟨147035514245853093119228749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196047352327804124158971665 147035514245853093119228749)
    ·
      refine ⟨55138317842194909919710781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147035514245853093119228749 55138317842194909919710781)
      ·
        refine ⟨20676869190823091219891543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55138317842194909919710781 20676869190823091219891543)
        ·
          refine ⟨31015303786234636829837315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20676869190823091219891543 31015303786234636829837315)
          ·
            refine ⟨46522955679351955244755973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31015303786234636829837315 46522955679351955244755973)
            ·
              refine ⟨8723054189878491608391745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46522955679351955244755973 8723054189878491608391745)
              ·
                refine ⟨6542290642408868706293809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8723054189878491608391745 6542290642408868706293809)
                ·
                  refine ⟨4906717981806651529720357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6542290642408868706293809 4906717981806651529720357)
                  ·
                    refine ⟨920009621588747161822567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4906717981806651529720357 920009621588747161822567)
                    ·
                      rfl

theorem cell23_5375137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_5375137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375137 prefixEnd_5375137 := by exact prefixLift 5375137
  have htrace : WordTrace (prefixWord ++ tailWord_5375137) baseStart_5375137 baseEnd_5375137 := by
    simpa [prefixWord, tailWord_5375137, baseEnd_5375137] using wordTrace_append hprefix tailTrace_5375137
  have hstable : (prefixWord ++ tailWord_5375137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375137).length < 2 ^ (prefixWord ++ tailWord_5375137).sum := by decide
  have hdescent : baseEnd_5375137 < baseStart_5375137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375173 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_5375173 : Nat := 118140960795 + 5375173 * 2 ^ 59
def prefixEnd_5375173 : Nat := 4983230072969 + 3 ^ 40 * 5375173 * 2
def baseEnd_5375173 : Nat := 2760047350069803344617535

theorem tailTrace_5375173 : CollatzResearch.WordTrace tailWord_5375173 prefixEnd_5375173 2760047350069803344617535 := by
  unfold tailWord_5375173
  simp only [CollatzResearch.WordTrace]
  refine ⟨196048665355673702307282173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130699110237115801538188115 196048665355673702307282173)
  ·
    refine ⟨73518249508377638365230815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196048665355673702307282173 73518249508377638365230815)
    ·
      refine ⟨110277374262566457547846223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73518249508377638365230815 110277374262566457547846223)
      ·
        refine ⟨165416061393849686321769335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110277374262566457547846223 165416061393849686321769335)
        ·
          refine ⟨248124092090774529482654003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165416061393849686321769335 248124092090774529482654003)
          ·
            refine ⟨372186138136161794223981005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248124092090774529482654003 372186138136161794223981005)
            ·
              refine ⟨139569801801060672833992877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372186138136161794223981005 139569801801060672833992877)
              ·
                refine ⟨52338675675397752312747329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139569801801060672833992877 52338675675397752312747329)
                ·
                  refine ⟨39254006756548314234560497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52338675675397752312747329 39254006756548314234560497)
                  ·
                    refine ⟨29440505067411235675920373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39254006756548314234560497 29440505067411235675920373)
                    ·
                      refine ⟨2760047350069803344617535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29440505067411235675920373 2760047350069803344617535)
                      ·
                        rfl

theorem cell23_5375173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_5375173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375173 prefixEnd_5375173 := by exact prefixLift 5375173
  have htrace : WordTrace (prefixWord ++ tailWord_5375173) baseStart_5375173 baseEnd_5375173 := by
    simpa [prefixWord, tailWord_5375173, baseEnd_5375173] using wordTrace_append hprefix tailTrace_5375173
  have hstable : (prefixWord ++ tailWord_5375173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375173).length < 2 ^ (prefixWord ++ tailWord_5375173).sum := by decide
  have hdescent : baseEnd_5375173 < baseStart_5375173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375183 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_5375183 : Nat := 118140960795 + 5375183 * 2 ^ 59
def prefixEnd_5375183 : Nat := 4983230072969 + 3 ^ 40 * 5375183 * 2
def baseEnd_5375183 : Nat := 2760052484876348305492489

theorem tailTrace_5375183 : CollatzResearch.WordTrace tailWord_5375183 prefixEnd_5375183 2760052484876348305492489 := by
  unfold tailWord_5375183
  simp only [CollatzResearch.WordTrace]
  refine ⟨196049030085637474015146203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130699353390424982676764135 196049030085637474015146203)
  ·
    refine ⟨294073545128456211022719305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196049030085637474015146203 294073545128456211022719305)
    ·
      refine ⟨220555158846342158267039479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294073545128456211022719305 220555158846342158267039479)
      ·
        refine ⟨330832738269513237400559219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220555158846342158267039479 330832738269513237400559219)
        ·
          refine ⟨496249107404269856100838829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330832738269513237400559219 496249107404269856100838829)
          ·
            refine ⟨186093415276601196037814561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496249107404269856100838829 186093415276601196037814561)
            ·
              refine ⟨139570061457450897028360921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186093415276601196037814561 139570061457450897028360921)
              ·
                refine ⟨104677546093088172771270691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139570061457450897028360921 104677546093088172771270691)
                ·
                  refine ⟨157016319139632259156906037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104677546093088172771270691 157016319139632259156906037)
                  ·
                    refine ⟨14720279919340524295959941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157016319139632259156906037 14720279919340524295959941)
                    ·
                      refine ⟨2760052484876348305492489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14720279919340524295959941 2760052484876348305492489)
                      ·
                        rfl

theorem cell23_5375183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_5375183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375183 prefixEnd_5375183 := by exact prefixLift 5375183
  have htrace : WordTrace (prefixWord ++ tailWord_5375183) baseStart_5375183 baseEnd_5375183 := by
    simpa [prefixWord, tailWord_5375183, baseEnd_5375183] using wordTrace_append hprefix tailTrace_5375183
  have hstable : (prefixWord ++ tailWord_5375183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375183).length < 2 ^ (prefixWord ++ tailWord_5375183).sum := by decide
  have hdescent : baseEnd_5375183 < baseStart_5375183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375187 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 1, 3, 2]
def baseStart_5375187 : Nat := 118140960795 + 5375187 * 2 ^ 59
def prefixEnd_5375187 : Nat := 4983230072969 + 3 ^ 40 * 5375187 * 2
def baseEnd_5375187 : Nat := 2760054538798966289842471

theorem tailTrace_5375187 : CollatzResearch.WordTrace tailWord_5375187 prefixEnd_5375187 2760054538798966289842471 := by
  unfold tailWord_5375187
  simp only [CollatzResearch.WordTrace]
  refine ⟨196049175977622982698291815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130699450651748655132194543 196049175977622982698291815)
  ·
    refine ⟨294073763966434474047437723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196049175977622982698291815 294073763966434474047437723)
    ·
      refine ⟨441110645949651711071156585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294073763966434474047437723 441110645949651711071156585)
      ·
        refine ⟨330832984462238783303367439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441110645949651711071156585 330832984462238783303367439)
        ·
          refine ⟨496249476693358174955051159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330832984462238783303367439 496249476693358174955051159)
          ·
            refine ⟨744374215040037262432576739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496249476693358174955051159 744374215040037262432576739)
            ·
              refine ⟨1116561322560055893648865109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744374215040037262432576739 1116561322560055893648865109)
              ·
                refine ⟨6542351499375327501848819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1116561322560055893648865109 6542351499375327501848819)
                ·
                  refine ⟨9813527249062991252773229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6542351499375327501848819 9813527249062991252773229)
                  ·
                    refine ⟨3680072718398621719789961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9813527249062991252773229 3680072718398621719789961)
                    ·
                      refine ⟨2760054538798966289842471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680072718398621719789961 2760054538798966289842471)
                      ·
                        rfl

theorem cell23_5375187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 3, 2].length) (baseStart_5375187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375187 prefixEnd_5375187 := by exact prefixLift 5375187
  have htrace : WordTrace (prefixWord ++ tailWord_5375187) baseStart_5375187 baseEnd_5375187 := by
    simpa [prefixWord, tailWord_5375187, baseEnd_5375187] using wordTrace_append hprefix tailTrace_5375187
  have hstable : (prefixWord ++ tailWord_5375187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375187).length < 2 ^ (prefixWord ++ tailWord_5375187).sum := by decide
  have hdescent : baseEnd_5375187 < baseStart_5375187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375188 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_5375188 : Nat := 118140960795 + 5375188 * 2 ^ 59
def prefixEnd_5375188 : Nat := 4983230072969 + 3 ^ 40 * 5375188 * 2
def baseEnd_5375188 : Nat := 920018350759873595309989

theorem tailTrace_5375188 : CollatzResearch.WordTrace tailWord_5375188 prefixEnd_5375188 920018350759873595309989 := by
  unfold tailWord_5375188
  simp only [CollatzResearch.WordTrace]
  refine ⟨98024606225309679934539109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130699474967079573246052145 98024606225309679934539109)
  ·
    refine ⟨18379613667245564987726083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98024606225309679934539109 18379613667245564987726083)
    ·
      refine ⟨27569420500868347481589125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18379613667245564987726083 27569420500868347481589125)
      ·
        refine ⟨5169266343912815152797961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27569420500868347481589125 5169266343912815152797961)
        ·
          refine ⟨3876949757934611364598471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5169266343912815152797961 3876949757934611364598471)
          ·
            refine ⟨5815424636901917046897707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3876949757934611364598471 5815424636901917046897707)
            ·
              refine ⟨8723136955352875570346561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5815424636901917046897707 8723136955352875570346561)
              ·
                refine ⟨6542352716514656677759921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8723136955352875570346561 6542352716514656677759921)
                ·
                  refine ⟨4906764537385992508319941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6542352716514656677759921 4906764537385992508319941)
                  ·
                    refine ⟨920018350759873595309989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4906764537385992508319941 920018350759873595309989)
                    ·
                      rfl

theorem cell23_5375188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_5375188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375188 prefixEnd_5375188 := by exact prefixLift 5375188
  have htrace : WordTrace (prefixWord ++ tailWord_5375188) baseStart_5375188 baseEnd_5375188 := by
    simpa [prefixWord, tailWord_5375188, baseEnd_5375188] using wordTrace_append hprefix tailTrace_5375188
  have hstable : (prefixWord ++ tailWord_5375188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375188).length < 2 ^ (prefixWord ++ tailWord_5375188).sum := by decide
  have hdescent : baseEnd_5375188 < baseStart_5375188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375210 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_5375210 : Nat := 118140960795 + 5375210 * 2 ^ 59
def prefixEnd_5375210 : Nat := 4983230072969 + 3 ^ 40 * 5375210 * 2
def baseEnd_5375210 : Nat := 920022116284673233284955

theorem tailTrace_5375210 : CollatzResearch.WordTrace tailWord_5375210 prefixEnd_5375210 920022116284673233284955 := by
  unfold tailWord_5375210
  simp only [CollatzResearch.WordTrace]
  refine ⟨49012503714134914406594771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130700009904359771750919389 49012503714134914406594771)
  ·
    refine ⟨73518755571202371609892157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49012503714134914406594771 73518755571202371609892157)
    ·
      refine ⟨27569533339200889353709559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73518755571202371609892157 27569533339200889353709559)
      ·
        refine ⟨41354300008801334030564339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27569533339200889353709559 41354300008801334030564339)
        ·
          refine ⟨62031450013202001045846509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41354300008801334030564339 62031450013202001045846509)
          ·
            refine ⟨23261793754950750392192441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62031450013202001045846509 23261793754950750392192441)
            ·
              refine ⟨17446345316213062794144331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23261793754950750392192441 17446345316213062794144331)
              ·
                refine ⟨26169517974319594191216497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17446345316213062794144331 26169517974319594191216497)
                ·
                  refine ⟨19627138480739695643412373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26169517974319594191216497 19627138480739695643412373)
                  ·
                    refine ⟨920022116284673233284955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19627138480739695643412373 920022116284673233284955)
                    ·
                      rfl

theorem cell23_5375210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_5375210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375210 prefixEnd_5375210 := by exact prefixLift 5375210
  have htrace : WordTrace (prefixWord ++ tailWord_5375210) baseStart_5375210 baseEnd_5375210 := by
    simpa [prefixWord, tailWord_5375210, baseEnd_5375210] using wordTrace_append hprefix tailTrace_5375210
  have hstable : (prefixWord ++ tailWord_5375210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375210).length < 2 ^ (prefixWord ++ tailWord_5375210).sum := by decide
  have hdescent : baseEnd_5375210 < baseStart_5375210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375262 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5375262 : Nat := 118140960795 + 5375262 * 2 ^ 59
def prefixEnd_5375262 : Nat := 4983230072969 + 3 ^ 40 * 5375262 * 2
def baseEnd_5375262 : Nat := 2760093049848053496404627

theorem tailTrace_5375262 : CollatzResearch.WordTrace tailWord_5375262 prefixEnd_5375262 2760093049848053496404627 := by
  unfold tailWord_5375262
  simp only [CollatzResearch.WordTrace]
  refine ⟨24506488931543908813409005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130701274301567513671514693 24506488931543908813409005)
  ·
    refine ⟨9189933349328965805028377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24506488931543908813409005 9189933349328965805028377)
    ·
      refine ⟨6892450011996724353771283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9189933349328965805028377 6892450011996724353771283)
      ·
        refine ⟨10338675017995086530656925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892450011996724353771283 10338675017995086530656925)
        ·
          refine ⟨3877003131748157448996347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10338675017995086530656925 3877003131748157448996347)
          ·
            refine ⟨5815504697622236173494521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877003131748157448996347 5815504697622236173494521)
            ·
              refine ⟨4361628523216677130120891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5815504697622236173494521 4361628523216677130120891)
              ·
                refine ⟨6542442784825015695181337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4361628523216677130120891 6542442784825015695181337)
                ·
                  refine ⟨4906832088618761771386003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6542442784825015695181337 4906832088618761771386003)
                  ·
                    refine ⟨7360248132928142657079005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4906832088618761771386003 7360248132928142657079005)
                    ·
                      refine ⟨2760093049848053496404627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7360248132928142657079005 2760093049848053496404627)
                      ·
                        rfl

theorem cell23_5375262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5375262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375262 prefixEnd_5375262 := by exact prefixLift 5375262
  have htrace : WordTrace (prefixWord ++ tailWord_5375262) baseStart_5375262 baseEnd_5375262 := by
    simpa [prefixWord, tailWord_5375262, baseEnd_5375262] using wordTrace_append hprefix tailTrace_5375262
  have hstable : (prefixWord ++ tailWord_5375262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375262).length < 2 ^ (prefixWord ++ tailWord_5375262).sum := by decide
  have hdescent : baseEnd_5375262 < baseStart_5375262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375297 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5375297 : Nat := 118140960795 + 5375297 * 2 ^ 59
def prefixEnd_5375297 : Nat := 4983230072969 + 3 ^ 40 * 5375297 * 2
def baseEnd_5375297 : Nat := 2760111021670960859466965

theorem tailTrace_5375297 : CollatzResearch.WordTrace tailWord_5375297 prefixEnd_5375297 2760111021670960859466965 := by
  unfold tailWord_5375297
  simp only [CollatzResearch.WordTrace]
  refine ⟨196053188007224471484796145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130702125338149647656530763 196053188007224471484796145)
  ·
    refine ⟨147039891005418353613597109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196053188007224471484796145 147039891005418353613597109)
    ·
      refine ⟨13784989781757970651274729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147039891005418353613597109 13784989781757970651274729)
      ·
        refine ⟨10338742336318477988456047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13784989781757970651274729 10338742336318477988456047)
        ·
          refine ⟨15508113504477716982684071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10338742336318477988456047 15508113504477716982684071)
          ·
            refine ⟨23262170256716575474026107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15508113504477716982684071 23262170256716575474026107)
            ·
              refine ⟨34893255385074863211039161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23262170256716575474026107 34893255385074863211039161)
              ·
                refine ⟨26169941538806147408279371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34893255385074863211039161 26169941538806147408279371)
                ·
                  refine ⟨39254912308209221112419057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26169941538806147408279371 39254912308209221112419057)
                  ·
                    refine ⟨29441184231156915834314293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39254912308209221112419057 29441184231156915834314293)
                    ·
                      refine ⟨2760111021670960859466965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29441184231156915834314293 2760111021670960859466965)
                      ·
                        rfl

theorem cell23_5375297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5375297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375297 prefixEnd_5375297 := by exact prefixLift 5375297
  have htrace : WordTrace (prefixWord ++ tailWord_5375297) baseStart_5375297 baseEnd_5375297 := by
    simpa [prefixWord, tailWord_5375297, baseEnd_5375297] using wordTrace_append hprefix tailTrace_5375297
  have hstable : (prefixWord ++ tailWord_5375297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375297).length < 2 ^ (prefixWord ++ tailWord_5375297).sum := by decide
  have hdescent : baseEnd_5375297 < baseStart_5375297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375302 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5375302 : Nat := 118140960795 + 5375302 * 2 ^ 59
def prefixEnd_5375302 : Nat := 4983230072969 + 3 ^ 40 * 5375302 * 2
def baseEnd_5375302 : Nat := 2760113589074233339904443

theorem tailTrace_5375302 : CollatzResearch.WordTrace tailWord_5375302 prefixEnd_5375302 2760113589074233339904443 := by
  unfold tailWord_5375302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6126667824131448666835255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130702246914804238225818773 6126667824131448666835255)
  ·
    refine ⟨9190001736197173000252883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6126667824131448666835255 9190001736197173000252883)
    ·
      refine ⟨13785002604295759500379325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9190001736197173000252883 13785002604295759500379325)
      ·
        refine ⟨5169375976610909812642247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13785002604295759500379325 5169375976610909812642247)
        ·
          refine ⟨7754063964916364718963371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169375976610909812642247 7754063964916364718963371)
          ·
            refine ⟨11631095947374547078445057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754063964916364718963371 11631095947374547078445057)
            ·
              refine ⟨8723321960530910308833793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11631095947374547078445057 8723321960530910308833793)
              ·
                refine ⟨6542491470398182731625345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8723321960530910308833793 6542491470398182731625345)
                ·
                  refine ⟨4906868602798637048719009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6542491470398182731625345 4906868602798637048719009)
                  ·
                    refine ⟨3680151452098977786539257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4906868602798637048719009 3680151452098977786539257)
                    ·
                      refine ⟨2760113589074233339904443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680151452098977786539257 2760113589074233339904443)
                      ·
                        rfl

theorem cell23_5375302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5375302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375302 prefixEnd_5375302 := by exact prefixLift 5375302
  have htrace : WordTrace (prefixWord ++ tailWord_5375302) baseStart_5375302 baseEnd_5375302 := by
    simpa [prefixWord, tailWord_5375302, baseEnd_5375302] using wordTrace_append hprefix tailTrace_5375302
  have hstable : (prefixWord ++ tailWord_5375302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375302).length < 2 ^ (prefixWord ++ tailWord_5375302).sum := by decide
  have hdescent : baseEnd_5375302 < baseStart_5375302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375310 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_5375310 : Nat := 118140960795 + 5375310 * 2 ^ 59
def prefixEnd_5375310 : Nat := 4983230072969 + 3 ^ 40 * 5375310 * 2
def baseEnd_5375310 : Nat := 2760117696919469308604405

theorem tailTrace_5375310 : CollatzResearch.WordTrace tailWord_5375310 prefixEnd_5375310 2760117696919469308604405 := by
  unfold tailWord_5375310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24506707769522171838127423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130702441437451583136679589 24506707769522171838127423)
  ·
    refine ⟨36760061654283257757191135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24506707769522171838127423 36760061654283257757191135)
    ·
      refine ⟨55140092481424886635786703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36760061654283257757191135 55140092481424886635786703)
      ·
        refine ⟨82710138722137329953680055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55140092481424886635786703 82710138722137329953680055)
        ·
          refine ⟨124065208083205994930520083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82710138722137329953680055 124065208083205994930520083)
          ·
            refine ⟨186097812124808992395780125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124065208083205994930520083 186097812124808992395780125)
            ·
              refine ⟨69786679546803372148417547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186097812124808992395780125 69786679546803372148417547)
              ·
                refine ⟨104680019320205058222626321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69786679546803372148417547 104680019320205058222626321)
                ·
                  refine ⟨78510014490153793666969741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104680019320205058222626321 78510014490153793666969741)
                  ·
                    refine ⟨29441255433807672625113653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78510014490153793666969741 29441255433807672625113653)
                    ·
                      refine ⟨2760117696919469308604405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29441255433807672625113653 2760117696919469308604405)
                      ·
                        rfl

theorem cell23_5375310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_5375310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375310 prefixEnd_5375310 := by exact prefixLift 5375310
  have htrace : WordTrace (prefixWord ++ tailWord_5375310) baseStart_5375310 baseEnd_5375310 := by
    simpa [prefixWord, tailWord_5375310, baseEnd_5375310] using wordTrace_append hprefix tailTrace_5375310
  have hstable : (prefixWord ++ tailWord_5375310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375310).length < 2 ^ (prefixWord ++ tailWord_5375310).sum := by decide
  have hdescent : baseEnd_5375310 < baseStart_5375310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375364 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 6]
def baseStart_5375364 : Nat := 118140960795 + 5375364 * 2 ^ 59
def prefixEnd_5375364 : Nat := 4983230072969 + 3 ^ 40 * 5375364 * 2
def baseEnd_5375364 : Nat := 306682824986090233036573

theorem tailTrace_5375364 : CollatzResearch.WordTrace tailWord_5375364 prefixEnd_5375364 306682824986090233036573 := by
  unfold tailWord_5375364
  simp only [CollatzResearch.WordTrace]
  refine ⟨98027815848990870963742573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130703754465321161284990097 98027815848990870963742573)
  ·
    refine ⟨36760430943371576611403465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98027815848990870963742573 36760430943371576611403465)
    ·
      refine ⟨27570323207528682458552599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36760430943371576611403465 27570323207528682458552599)
      ·
        refine ⟨41355484811293023687828899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27570323207528682458552599 41355484811293023687828899)
        ·
          refine ⟨62033227216939535531743349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41355484811293023687828899 62033227216939535531743349)
          ·
            refine ⟨5815615051588081456100939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62033227216939535531743349 5815615051588081456100939)
            ·
              refine ⟨8723422577382122184151409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5815615051588081456100939 8723422577382122184151409)
              ·
                refine ⟨6542566933036591638113557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8723422577382122184151409 6542566933036591638113557)
                ·
                  refine ⟨306682824986090233036573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6542566933036591638113557 306682824986090233036573)
                  ·
                    rfl

theorem cell23_5375364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_5375364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375364 prefixEnd_5375364 := by exact prefixLift 5375364
  have htrace : WordTrace (prefixWord ++ tailWord_5375364) baseStart_5375364 baseEnd_5375364 := by
    simpa [prefixWord, tailWord_5375364, baseEnd_5375364] using wordTrace_append hprefix tailTrace_5375364
  have hstable : (prefixWord ++ tailWord_5375364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375364).length < 2 ^ (prefixWord ++ tailWord_5375364).sum := by decide
  have hdescent : baseEnd_5375364 < baseStart_5375364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375394 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_5375394 : Nat := 118140960795 + 5375394 * 2 ^ 59
def prefixEnd_5375394 : Nat := 4983230072969 + 3 ^ 40 * 5375394 * 2
def baseEnd_5375394 : Nat := 920053609764815659984673

theorem tailTrace_5375394 : CollatzResearch.WordTrace tailWord_5375394 prefixEnd_5375394 920053609764815659984673 := by
  unfold tailWord_5375394
  simp only [CollatzResearch.WordTrace]
  refine ⟨49014181471968264262769309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130704483925248704700718157 49014181471968264262769309)
  ·
    refine ⟨18380318051988099098538491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49014181471968264262769309 18380318051988099098538491)
    ·
      refine ⟨27570477077982148647807737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18380318051988099098538491 27570477077982148647807737)
      ·
        refine ⟨20677857808486611485855803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27570477077982148647807737 20677857808486611485855803)
        ·
          refine ⟨31016786712729917228783705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20677857808486611485855803 31016786712729917228783705)
          ·
            refine ⟨23262590034547437921587779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31016786712729917228783705 23262590034547437921587779)
            ·
              refine ⟨34893885051821156882381669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23262590034547437921587779 34893885051821156882381669)
              ·
                refine ⟨6542603447216466915446563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34893885051821156882381669 6542603447216466915446563)
                ·
                  refine ⟨9813905170824700373169845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6542603447216466915446563 9813905170824700373169845)
                  ·
                    refine ⟨920053609764815659984673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9813905170824700373169845 920053609764815659984673)
                    ·
                      rfl

theorem cell23_5375394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_5375394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375394 prefixEnd_5375394 := by exact prefixLift 5375394
  have htrace : WordTrace (prefixWord ++ tailWord_5375394) baseStart_5375394 baseEnd_5375394 := by
    simpa [prefixWord, tailWord_5375394, baseEnd_5375394] using wordTrace_append hprefix tailTrace_5375394
  have hstable : (prefixWord ++ tailWord_5375394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375394).length < 2 ^ (prefixWord ++ tailWord_5375394).sum := by decide
  have hdescent : baseEnd_5375394 < baseStart_5375394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375447 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_5375447 : Nat := 118140960795 + 5375447 * 2 ^ 59
def prefixEnd_5375447 : Nat := 4983230072969 + 3 ^ 40 * 5375447 * 2
def baseEnd_5375447 : Nat := 2760188043769135272591275

theorem tailTrace_5375447 : CollatzResearch.WordTrace tailWord_5375447 prefixEnd_5375447 2760188043769135272591275 := by
  unfold tailWord_5375447
  simp only [CollatzResearch.WordTrace]
  refine ⟨196058658956681047102756595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130705772637787364735171063 196058658956681047102756595)
  ·
    refine ⟨294087988435021570654134893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196058658956681047102756595 294087988435021570654134893)
    ·
      refine ⟨110282995663133088995300585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294087988435021570654134893 110282995663133088995300585)
      ·
        refine ⟨82712246747349816746475439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110282995663133088995300585 82712246747349816746475439)
        ·
          refine ⟨124068370121024725119713159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82712246747349816746475439 124068370121024725119713159)
          ·
            refine ⟨186102555181537087679569739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124068370121024725119713159 186102555181537087679569739)
            ·
              refine ⟨279153832772305631519354609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186102555181537087679569739 279153832772305631519354609)
              ·
                refine ⟨209365374579229223639515957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279153832772305631519354609 209365374579229223639515957)
                ·
                  refine ⟨19628003866802739716204621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209365374579229223639515957 19628003866802739716204621)
                  ·
                    refine ⟨7360501450051027393576733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19628003866802739716204621 7360501450051027393576733)
                    ·
                      refine ⟨2760188043769135272591275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7360501450051027393576733 2760188043769135272591275)
                      ·
                        rfl

theorem cell23_5375447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_5375447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375447 prefixEnd_5375447 := by exact prefixLift 5375447
  have htrace : WordTrace (prefixWord ++ tailWord_5375447) baseStart_5375447 baseEnd_5375447 := by
    simpa [prefixWord, tailWord_5375447, baseEnd_5375447] using wordTrace_append hprefix tailTrace_5375447
  have hstable : (prefixWord ++ tailWord_5375447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375447).length < 2 ^ (prefixWord ++ tailWord_5375447).sum := by decide
  have hdescent : baseEnd_5375447 < baseStart_5375447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375464 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_5375464 : Nat := 118140960795 + 5375464 * 2 ^ 59
def prefixEnd_5375464 : Nat := 4983230072969 + 3 ^ 40 * 5375464 * 2
def baseEnd_5375464 : Nat := 2760196772940261706078697

theorem tailTrace_5375464 : CollatzResearch.WordTrace tailWord_5375464 prefixEnd_5375464 2760196772940261706078697 := by
  unfold tailWord_5375464
  simp only [CollatzResearch.WordTrace]
  refine ⟨98029639498809729503062723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130706185998412972670750297 98029639498809729503062723)
  ·
    refine ⟨147044459248214594254594085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98029639498809729503062723 147044459248214594254594085)
    ·
      refine ⟨27570836109040236422736391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147044459248214594254594085 27570836109040236422736391)
      ·
        refine ⟨41356254163560354634104587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27570836109040236422736391 41356254163560354634104587)
        ·
          refine ⟨62034381245340531951156881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41356254163560354634104587 62034381245340531951156881)
          ·
            refine ⟨46525785934005398963367661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62034381245340531951156881 46525785934005398963367661)
            ·
              refine ⟨17447169725252024611262873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46525785934005398963367661 17447169725252024611262873)
              ·
                refine ⟨13085377293939018458447155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17447169725252024611262873 13085377293939018458447155)
                ·
                  refine ⟨19628065940908527687670733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13085377293939018458447155 19628065940908527687670733)
                  ·
                    refine ⟨7360524727840697882876525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19628065940908527687670733 7360524727840697882876525)
                    ·
                      refine ⟨2760196772940261706078697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7360524727840697882876525 2760196772940261706078697)
                      ·
                        rfl

theorem cell23_5375464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_5375464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375464 prefixEnd_5375464 := by exact prefixLift 5375464
  have htrace : WordTrace (prefixWord ++ tailWord_5375464) baseStart_5375464 baseEnd_5375464 := by
    simpa [prefixWord, tailWord_5375464, baseEnd_5375464] using wordTrace_append hprefix tailTrace_5375464
  have hstable : (prefixWord ++ tailWord_5375464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375464).length < 2 ^ (prefixWord ++ tailWord_5375464).sum := by decide
  have hdescent : baseEnd_5375464 < baseStart_5375464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375497 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 2, 6]
def baseStart_5375497 : Nat := 118140960795 + 5375497 * 2 ^ 59
def prefixEnd_5375497 : Nat := 4983230072969 + 3 ^ 40 * 5375497 * 2
def baseEnd_5375497 : Nat := 920071239267286692322015

theorem tailTrace_5375497 : CollatzResearch.WordTrace tailWord_5375497 prefixEnd_5375497 920071239267286692322015 := by
  unfold tailWord_5375497
  simp only [CollatzResearch.WordTrace]
  refine ⟨196060482606499905642076745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130706988404333270428051163 196060482606499905642076745)
  ·
    refine ⟨147045361954874929231557559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196060482606499905642076745 147045361954874929231557559)
    ·
      refine ⟨220568042932312393847336339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147045361954874929231557559 220568042932312393847336339)
      ·
        refine ⟨330852064398468590771004509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220568042932312393847336339 330852064398468590771004509)
        ·
          refine ⟨124069524149425721539126691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330852064398468590771004509 124069524149425721539126691)
          ·
            refine ⟨186104286224138582308690037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124069524149425721539126691 186104286224138582308690037)
            ·
              refine ⟨17447276833512992091439691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186104286224138582308690037 17447276833512992091439691)
              ·
                refine ⟨26170915250269488137159537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17447276833512992091439691 26170915250269488137159537)
                ·
                  refine ⟨19628186437702116102869653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26170915250269488137159537 19628186437702116102869653)
                  ·
                    refine ⟨920071239267286692322015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19628186437702116102869653 920071239267286692322015)
                    ·
                      rfl

theorem cell23_5375497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_5375497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375497 prefixEnd_5375497 := by exact prefixLift 5375497
  have htrace : WordTrace (prefixWord ++ tailWord_5375497) baseStart_5375497 baseEnd_5375497 := by
    simpa [prefixWord, tailWord_5375497, baseEnd_5375497] using wordTrace_append hprefix tailTrace_5375497
  have hstable : (prefixWord ++ tailWord_5375497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375497).length < 2 ^ (prefixWord ++ tailWord_5375497).sum := by decide
  have hdescent : baseEnd_5375497 < baseStart_5375497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375521 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_5375521 : Nat := 118140960795 + 5375521 * 2 ^ 59
def prefixEnd_5375521 : Nat := 4983230072969 + 3 ^ 40 * 5375521 * 2
def baseEnd_5375521 : Nat := 2760226041337567983065935

theorem tailTrace_5375521 : CollatzResearch.WordTrace tailWord_5375521 prefixEnd_5375521 2760226041337567983065935 := by
  unfold tailWord_5375521
  simp only [CollatzResearch.WordTrace]
  refine ⟨196061357958412957740950417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130707571972275305160633611 196061357958412957740950417)
  ·
    refine ⟨147046018468809718305712813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196061357958412957740950417 147046018468809718305712813)
    ·
      refine ⟨55142256925803644364642305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147046018468809718305712813 55142256925803644364642305)
      ·
        refine ⟨41356692694352733273481729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55142256925803644364642305 41356692694352733273481729)
        ·
          refine ⟨31017519520764549955111297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41356692694352733273481729 31017519520764549955111297)
          ·
            refine ⟨23263139640573412466333473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31017519520764549955111297 23263139640573412466333473)
            ·
              refine ⟨17447354730430059349750105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23263139640573412466333473 17447354730430059349750105)
              ·
                refine ⟨13085516047822544512312579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17447354730430059349750105 13085516047822544512312579)
                ·
                  refine ⟨19628274071733816768468869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13085516047822544512312579 19628274071733816768468869)
                  ·
                    refine ⟨3680301388450090644087913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19628274071733816768468869 3680301388450090644087913)
                    ·
                      refine ⟨2760226041337567983065935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680301388450090644087913 2760226041337567983065935)
                      ·
                        rfl

theorem cell23_5375521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_5375521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375521 prefixEnd_5375521 := by exact prefixLift 5375521
  have htrace : WordTrace (prefixWord ++ tailWord_5375521) baseStart_5375521 baseEnd_5375521 := by
    simpa [prefixWord, tailWord_5375521, baseEnd_5375521] using wordTrace_append hprefix tailTrace_5375521
  have hstable : (prefixWord ++ tailWord_5375521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375521).length < 2 ^ (prefixWord ++ tailWord_5375521).sum := by decide
  have hdescent : baseEnd_5375521 < baseStart_5375521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375544 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 7]
def baseStart_5375544 : Nat := 118140960795 + 5375544 * 2 ^ 59
def prefixEnd_5375544 : Nat := 4983230072969 + 3 ^ 40 * 5375544 * 2
def baseEnd_5375544 : Nat := 306693094599180154786481

theorem tailTrace_5375544 : CollatzResearch.WordTrace tailWord_5375544 prefixEnd_5375544 306693094599180154786481 := by
  unfold tailWord_5375544
  simp only [CollatzResearch.WordTrace]
  refine ⟨98031098418664816334518843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130708131224886421779358457 98031098418664816334518843)
  ·
    refine ⟨147046647627997224501778265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98031098418664816334518843 147046647627997224501778265)
    ·
      refine ⟨110284985720997918376333699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147046647627997224501778265 110284985720997918376333699)
      ·
        refine ⟨165427478581496877564500549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110284985720997918376333699 165427478581496877564500549)
        ·
          refine ⟨31017652234030664543343853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165427478581496877564500549 31017652234030664543343853)
          ·
            refine ⟨11631619587761499203753945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31017652234030664543343853 11631619587761499203753945)
            ·
              refine ⟨8723714690821124402815459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11631619587761499203753945 8723714690821124402815459)
              ·
                refine ⟨13085572036231686604223189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8723714690821124402815459 13085572036231686604223189)
                ·
                  refine ⟨306693094599180154786481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13085572036231686604223189 306693094599180154786481)
                  ·
                    rfl

theorem cell23_5375544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 7].length) (baseStart_5375544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375544 prefixEnd_5375544 := by exact prefixLift 5375544
  have htrace : WordTrace (prefixWord ++ tailWord_5375544) baseStart_5375544 baseEnd_5375544 := by
    simpa [prefixWord, tailWord_5375544, baseEnd_5375544] using wordTrace_append hprefix tailTrace_5375544
  have hstable : (prefixWord ++ tailWord_5375544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375544).length < 2 ^ (prefixWord ++ tailWord_5375544).sum := by decide
  have hdescent : baseEnd_5375544 < baseStart_5375544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375557 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_5375557 : Nat := 118140960795 + 5375557 * 2 ^ 59
def prefixEnd_5375557 : Nat := 4983230072969 + 3 ^ 40 * 5375557 * 2
def baseEnd_5375557 : Nat := 920081508880376614071923

theorem tailTrace_5375557 : CollatzResearch.WordTrace tailWord_5375557 prefixEnd_5375557 920081508880376614071923 := by
  unfold tailWord_5375557
  simp only [CollatzResearch.WordTrace]
  refine ⟨196062670986282535889260925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130708447324188357259507283 196062670986282535889260925)
  ·
    refine ⟨73523501619855950958472847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196062670986282535889260925 73523501619855950958472847)
    ·
      refine ⟨110285252429783926437709271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73523501619855950958472847 110285252429783926437709271)
      ·
        refine ⟨165427878644675889656563907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110285252429783926437709271 165427878644675889656563907)
        ·
          refine ⟨248141817967013834484845861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165427878644675889656563907 248141817967013834484845861)
          ·
            refine ⟨46526590868815093965908599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248141817967013834484845861 46526590868815093965908599)
            ·
              refine ⟨69789886303222640948862899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46526590868815093965908599 69789886303222640948862899)
              ·
                refine ⟨104684829454833961423294349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69789886303222640948862899 104684829454833961423294349)
                ·
                  refine ⟨39256811045562735533735381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104684829454833961423294349 39256811045562735533735381)
                  ·
                    refine ⟨920081508880376614071923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39256811045562735533735381 920081508880376614071923)
                    ·
                      rfl

theorem cell23_5375557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_5375557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375557 prefixEnd_5375557 := by exact prefixLift 5375557
  have htrace : WordTrace (prefixWord ++ tailWord_5375557) baseStart_5375557 baseEnd_5375557 := by
    simpa [prefixWord, tailWord_5375557, baseEnd_5375557] using wordTrace_append hprefix tailTrace_5375557
  have hstable : (prefixWord ++ tailWord_5375557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375557).length < 2 ^ (prefixWord ++ tailWord_5375557).sum := by decide
  have hdescent : baseEnd_5375557 < baseStart_5375557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375567 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_5375567 : Nat := 118140960795 + 5375567 * 2 ^ 59
def prefixEnd_5375567 : Nat := 4983230072969 + 3 ^ 40 * 5375567 * 2
def baseEnd_5375567 : Nat := 2760249661447674803090723

theorem tailTrace_5375567 : CollatzResearch.WordTrace tailWord_5375567 prefixEnd_5375567 2760249661447674803090723 := by
  unfold tailWord_5375567
  simp only [CollatzResearch.WordTrace]
  refine ⟨196063035716246307597124955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130708690477497538398083303 196063035716246307597124955)
  ·
    refine ⟨294094553574369461395687433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196063035716246307597124955 294094553574369461395687433)
    ·
      refine ⟨220570915180777096046765575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294094553574369461395687433 220570915180777096046765575)
      ·
        refine ⟨330856372771165644070148363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220570915180777096046765575 330856372771165644070148363)
        ·
          refine ⟨496284559156748466105222545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330856372771165644070148363 496284559156748466105222545)
          ·
            refine ⟨372213419367561349578916909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496284559156748466105222545 372213419367561349578916909)
            ·
              refine ⟨139580032262835506092093841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372213419367561349578916909 139580032262835506092093841)
              ·
                refine ⟨104685024197126629569070381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139580032262835506092093841 104685024197126629569070381)
                ·
                  refine ⟨39256884073922486088401393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104685024197126629569070381 39256884073922486088401393)
                  ·
                    refine ⟨29442663055441864566301045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39256884073922486088401393 29442663055441864566301045)
                    ·
                      refine ⟨2760249661447674803090723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29442663055441864566301045 2760249661447674803090723)
                      ·
                        rfl

theorem cell23_5375567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_5375567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375567 prefixEnd_5375567 := by exact prefixLift 5375567
  have htrace : WordTrace (prefixWord ++ tailWord_5375567) baseStart_5375567 baseEnd_5375567 := by
    simpa [prefixWord, tailWord_5375567, baseEnd_5375567] using wordTrace_append hprefix tailTrace_5375567
  have hstable : (prefixWord ++ tailWord_5375567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375567).length < 2 ^ (prefixWord ++ tailWord_5375567).sum := by decide
  have hdescent : baseEnd_5375567 < baseStart_5375567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375664 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_5375664 : Nat := 118140960795 + 5375664 * 2 ^ 59
def prefixEnd_5375664 : Nat := 4983230072969 + 3 ^ 40 * 5375664 * 2
def baseEnd_5375664 : Nat := 920099823023720307859259

theorem tailTrace_5375664 : CollatzResearch.WordTrace tailWord_5375664 prefixEnd_5375664 920099823023720307859259 := by
  unfold tailWord_5375664
  simp only [CollatzResearch.WordTrace]
  refine ⟨98033286798447446581703023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130711049064596595442270697 98033286798447446581703023)
  ·
    refine ⟨147049930197671169872554535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98033286798447446581703023 147049930197671169872554535)
    ·
      refine ⟨220574895296506754808831803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147049930197671169872554535 220574895296506754808831803)
      ·
        refine ⟨330862342944760132213247705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220574895296506754808831803 330862342944760132213247705)
        ·
          refine ⟨248146757208570099159935779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330862342944760132213247705 248146757208570099159935779)
          ·
            refine ⟨372220135812855148739903669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248146757208570099159935779 372220135812855148739903669)
            ·
              refine ⟨34895637732455170194365969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372220135812855148739903669 34895637732455170194365969)
              ·
                refine ⟨26171728299341377645774477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34895637732455170194365969 26171728299341377645774477)
                ·
                  refine ⟨9814398112253016617165429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26171728299341377645774477 9814398112253016617165429)
                  ·
                    refine ⟨920099823023720307859259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9814398112253016617165429 920099823023720307859259)
                    ·
                      rfl

theorem cell23_5375664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_5375664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375664 prefixEnd_5375664 := by exact prefixLift 5375664
  have htrace : WordTrace (prefixWord ++ tailWord_5375664) baseStart_5375664 baseEnd_5375664 := by
    simpa [prefixWord, tailWord_5375664, baseEnd_5375664] using wordTrace_append hprefix tailTrace_5375664
  have hstable : (prefixWord ++ tailWord_5375664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375664).length < 2 ^ (prefixWord ++ tailWord_5375664).sum := by decide
  have hdescent : baseEnd_5375664 < baseStart_5375664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375678 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_5375678 : Nat := 118140960795 + 5375678 * 2 ^ 59
def prefixEnd_5375678 : Nat := 4983230072969 + 3 ^ 40 * 5375678 * 2
def baseEnd_5375678 : Nat := 2760306657800323868802713

theorem tailTrace_5375678 : CollatzResearch.WordTrace tailWord_5375678 prefixEnd_5375678 2760306657800323868802713 := by
  unfold tailWord_5375678
  simp only [CollatzResearch.WordTrace]
  refine ⟨24508385527355521694301961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130711389479229449036277125 24508385527355521694301961)
  ·
    refine ⟨18381289145516641270726471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24508385527355521694301961 18381289145516641270726471)
    ·
      refine ⟨27571933718274961906089707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18381289145516641270726471 27571933718274961906089707)
      ·
        refine ⟨41357900577412442859134561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27571933718274961906089707 41357900577412442859134561)
        ·
          refine ⟨31018425433059332144350921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41357900577412442859134561 31018425433059332144350921)
          ·
            refine ⟨23263819074794499108263191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31018425433059332144350921 23263819074794499108263191)
            ·
              refine ⟨34895728612191748662394787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23263819074794499108263191 34895728612191748662394787)
              ·
                refine ⟨52343592918287622993592181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34895728612191748662394787 52343592918287622993592181)
                ·
                  refine ⟨4907211836089464655649267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52343592918287622993592181 4907211836089464655649267)
                  ·
                    refine ⟨7360817754134196983473901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4907211836089464655649267 7360817754134196983473901)
                    ·
                      refine ⟨2760306657800323868802713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7360817754134196983473901 2760306657800323868802713)
                      ·
                        rfl

theorem cell23_5375678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_5375678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375678 prefixEnd_5375678 := by exact prefixLift 5375678
  have htrace : WordTrace (prefixWord ++ tailWord_5375678) baseStart_5375678 baseEnd_5375678 := by
    simpa [prefixWord, tailWord_5375678, baseEnd_5375678] using wordTrace_append hprefix tailTrace_5375678
  have hstable : (prefixWord ++ tailWord_5375678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375678).length < 2 ^ (prefixWord ++ tailWord_5375678).sum := by decide
  have hdescent : baseEnd_5375678 < baseStart_5375678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375682 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5375682 : Nat := 118140960795 + 5375682 * 2 ^ 59
def prefixEnd_5375682 : Nat := 4983230072969 + 3 ^ 40 * 5375682 * 2
def baseEnd_5375682 : Nat := 2760308711722941853152695

theorem tailTrace_5375682 : CollatzResearch.WordTrace tailWord_5375682 prefixEnd_5375682 2760308711722941853152695 := by
  unfold tailWord_5375682
  simp only [CollatzResearch.WordTrace]
  refine ⟨49016807527707420559390325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130711486740553121491707533 49016807527707420559390325)
  ·
    refine ⟨4595325705722570677442843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49016807527707420559390325 4595325705722570677442843)
    ·
      refine ⟨6892988558583856016164265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595325705722570677442843 6892988558583856016164265)
      ·
        refine ⟨5169741418937892012123199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6892988558583856016164265 5169741418937892012123199)
        ·
          refine ⟨7754612128406838018184799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169741418937892012123199 7754612128406838018184799)
          ·
            refine ⟨11631918192610257027277199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754612128406838018184799 11631918192610257027277199)
            ·
              refine ⟨17447877288915385540915799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11631918192610257027277199 17447877288915385540915799)
              ·
                refine ⟨26171815933373078311373699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17447877288915385540915799 26171815933373078311373699)
                ·
                  refine ⟨39257723900059617467060549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26171815933373078311373699 39257723900059617467060549)
                  ·
                    refine ⟨7360823231261178275073853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39257723900059617467060549 7360823231261178275073853)
                    ·
                      refine ⟨2760308711722941853152695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7360823231261178275073853 2760308711722941853152695)
                      ·
                        rfl

theorem cell23_5375682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5375682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375682 prefixEnd_5375682 := by exact prefixLift 5375682
  have htrace : WordTrace (prefixWord ++ tailWord_5375682) baseStart_5375682 baseEnd_5375682 := by
    simpa [prefixWord, tailWord_5375682, baseEnd_5375682] using wordTrace_append hprefix tailTrace_5375682
  have hstable : (prefixWord ++ tailWord_5375682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375682).length < 2 ^ (prefixWord ++ tailWord_5375682).sum := by decide
  have hdescent : baseEnd_5375682 < baseStart_5375682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375698 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_5375698 : Nat := 118140960795 + 5375698 * 2 ^ 59
def prefixEnd_5375698 : Nat := 4983230072969 + 3 ^ 40 * 5375698 * 2
def baseEnd_5375698 : Nat := 920105642471137930184207

theorem tailTrace_5375698 : CollatzResearch.WordTrace tailWord_5375698 prefixEnd_5375698 920105642471137930184207 := by
  unfold tailWord_5375698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49016953419692929242535937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130711875785847811313429165 49016953419692929242535937)
  ·
    refine ⟨36762715064769696931901953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49016953419692929242535937 36762715064769696931901953)
    ·
      refine ⟨27572036298577272698926465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36762715064769696931901953 27572036298577272698926465)
      ·
        refine ⟨20679027223932954524194849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27572036298577272698926465 20679027223932954524194849)
        ·
          refine ⟨15509270417949715893146137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20679027223932954524194849 15509270417949715893146137)
          ·
            refine ⟨11631952813462286919859603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15509270417949715893146137 11631952813462286919859603)
            ·
              refine ⟨17447929220193430379789405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11631952813462286919859603 17447929220193430379789405)
              ·
                refine ⟨6542973457572536392421027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17447929220193430379789405 6542973457572536392421027)
                ·
                  refine ⟨9814460186358804588631541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6542973457572536392421027 9814460186358804588631541)
                  ·
                    refine ⟨920105642471137930184207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9814460186358804588631541 920105642471137930184207)
                    ·
                      rfl

theorem cell23_5375698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_5375698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375698 prefixEnd_5375698 := by exact prefixLift 5375698
  have htrace : WordTrace (prefixWord ++ tailWord_5375698) baseStart_5375698 baseEnd_5375698 := by
    simpa [prefixWord, tailWord_5375698, baseEnd_5375698] using wordTrace_append hprefix tailTrace_5375698
  have hstable : (prefixWord ++ tailWord_5375698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375698).length < 2 ^ (prefixWord ++ tailWord_5375698).sum := by decide
  have hdescent : baseEnd_5375698 < baseStart_5375698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375702 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_5375702 : Nat := 118140960795 + 5375702 * 2 ^ 59
def prefixEnd_5375702 : Nat := 4983230072969 + 3 ^ 40 * 5375702 * 2
def baseEnd_5375702 : Nat := 306702109037336863878067

theorem tailTrace_5375702 : CollatzResearch.WordTrace tailWord_5375702 prefixEnd_5375702 306702109037336863878067 := by
  unfold tailWord_5375702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12254247473172326603330585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130711973047171483768859573 12254247473172326603330585)
  ·
    refine ⟨9190685604879244952497939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12254247473172326603330585 9190685604879244952497939)
    ·
      refine ⟨13786028407318867428746909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9190685604879244952497939 13786028407318867428746909)
      ·
        refine ⟨5169760652744575285780091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13786028407318867428746909 5169760652744575285780091)
        ·
          refine ⟨7754640979116862928670137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169760652744575285780091 7754640979116862928670137)
          ·
            refine ⟨5815980734337647196502603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7754640979116862928670137 5815980734337647196502603)
            ·
              refine ⟨8723971101506470794753905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5815980734337647196502603 8723971101506470794753905)
              ·
                refine ⟨6542978326129853096065429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8723971101506470794753905 6542978326129853096065429)
                ·
                  refine ⟨306702109037336863878067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6542978326129853096065429 306702109037336863878067)
                  ·
                    rfl

theorem cell23_5375702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_5375702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375702 prefixEnd_5375702 := by exact prefixLift 5375702
  have htrace : WordTrace (prefixWord ++ tailWord_5375702) baseStart_5375702 baseEnd_5375702 := by
    simpa [prefixWord, tailWord_5375702, baseEnd_5375702] using wordTrace_append hprefix tailTrace_5375702
  have hstable : (prefixWord ++ tailWord_5375702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375702).length < 2 ^ (prefixWord ++ tailWord_5375702).sum := by decide
  have hdescent : baseEnd_5375702 < baseStart_5375702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375711 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 4, 4]
def baseStart_5375711 : Nat := 118140960795 + 5375711 * 2 ^ 59
def prefixEnd_5375711 : Nat := 4983230072969 + 3 ^ 40 * 5375711 * 2
def baseEnd_5375711 : Nat := 920107867553974079896687

theorem tailTrace_5375711 : CollatzResearch.WordTrace tailWord_5375711 prefixEnd_5375711 920107867553974079896687 := by
  unfold tailWord_5375711
  simp only [CollatzResearch.WordTrace]
  refine ⟨196068287827724620190366987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130712191885149746793577991 196068287827724620190366987)
  ·
    refine ⟨294102431741586930285550481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196068287827724620190366987 294102431741586930285550481)
    ·
      refine ⟨220576823806190197714162861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294102431741586930285550481 220576823806190197714162861)
      ·
        refine ⟨82716308927321324142811073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220576823806190197714162861 82716308927321324142811073)
        ·
          refine ⟨62037231695490993107108305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82716308927321324142811073 62037231695490993107108305)
          ·
            refine ⟨46527923771618244830331229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62037231695490993107108305 46527923771618244830331229)
            ·
              refine ⟨17447971414356841811374211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46527923771618244830331229 17447971414356841811374211)
              ·
                refine ⟨26171957121535262717061317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17447971414356841811374211 26171957121535262717061317)
                ·
                  refine ⟨4907241960287861759448997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26171957121535262717061317 4907241960287861759448997)
                  ·
                    refine ⟨920107867553974079896687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4907241960287861759448997 920107867553974079896687)
                    ·
                      rfl

theorem cell23_5375711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_5375711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375711 prefixEnd_5375711 := by exact prefixLift 5375711
  have htrace : WordTrace (prefixWord ++ tailWord_5375711) baseStart_5375711 baseEnd_5375711 := by
    simpa [prefixWord, tailWord_5375711, baseEnd_5375711] using wordTrace_append hprefix tailTrace_5375711
  have hstable : (prefixWord ++ tailWord_5375711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375711).length < 2 ^ (prefixWord ++ tailWord_5375711).sum := by decide
  have hdescent : baseEnd_5375711 < baseStart_5375711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375731 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 4]
def baseStart_5375731 : Nat := 118140960795 + 5375731 * 2 ^ 59
def prefixEnd_5375731 : Nat := 4983230072969 + 3 ^ 40 * 5375731 * 2
def baseEnd_5375731 : Nat := 2760333872275012161439969

theorem tailTrace_5375731 : CollatzResearch.WordTrace tailWord_5375731 prefixEnd_5375731 2760333872275012161439969 := by
  unfold tailWord_5375731
  simp only [CollatzResearch.WordTrace]
  refine ⟨196069017287652163606095047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130712678191768109070730031 196069017287652163606095047)
  ·
    refine ⟨294103525931478245409142571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196069017287652163606095047 294103525931478245409142571)
    ·
      refine ⟨441155288897217368113713857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294103525931478245409142571 441155288897217368113713857)
      ·
        refine ⟨330866466672913026085285393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441155288897217368113713857 330866466672913026085285393)
        ·
          refine ⟨248149850004684769563964045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330866466672913026085285393 248149850004684769563964045)
          ·
            refine ⟨93056193751756788586486517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248149850004684769563964045 93056193751756788586486517)
            ·
              refine ⟨8724018164227198929983111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93056193751756788586486517 8724018164227198929983111)
              ·
                refine ⟨13086027246340798394974667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724018164227198929983111 13086027246340798394974667)
                ·
                  refine ⟨19629040869511197592462001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13086027246340798394974667 19629040869511197592462001)
                  ·
                    refine ⟨14721780652133398194346501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19629040869511197592462001 14721780652133398194346501)
                    ·
                      refine ⟨2760333872275012161439969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14721780652133398194346501 2760333872275012161439969)
                      ·
                        rfl

theorem cell23_5375731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_5375731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375731 prefixEnd_5375731 := by exact prefixLift 5375731
  have htrace : WordTrace (prefixWord ++ tailWord_5375731) baseStart_5375731 baseEnd_5375731 := by
    simpa [prefixWord, tailWord_5375731, baseEnd_5375731] using wordTrace_append hprefix tailTrace_5375731
  have hstable : (prefixWord ++ tailWord_5375731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375731).length < 2 ^ (prefixWord ++ tailWord_5375731).sum := by decide
  have hdescent : baseEnd_5375731 < baseStart_5375731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375732 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5375732 : Nat := 118140960795 + 5375732 * 2 ^ 59
def prefixEnd_5375732 : Nat := 4983230072969 + 3 ^ 40 * 5375732 * 2
def baseEnd_5375732 : Nat := 920111461918555552509155

theorem tailTrace_5375732 : CollatzResearch.WordTrace tailWord_5375732 prefixEnd_5375732 920111461918555552509155 := by
  unfold tailWord_5375732
  simp only [CollatzResearch.WordTrace]
  refine ⟨98034526880324270388440725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130712702507099027184587633 98034526880324270388440725)
  ·
    refine ⟨4595368447515200174458159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98034526880324270388440725 4595368447515200174458159)
    ·
      refine ⟨6893052671272800261687239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595368447515200174458159 6893052671272800261687239)
      ·
        refine ⟨10339579006909200392530859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6893052671272800261687239 10339579006909200392530859)
        ·
          refine ⟨15509368510363800588796289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10339579006909200392530859 15509368510363800588796289)
          ·
            refine ⟨11632026382772850441597217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15509368510363800588796289 11632026382772850441597217)
            ·
              refine ⟨8724019787079637831197913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11632026382772850441597217 8724019787079637831197913)
              ·
                refine ⟨6543014840309728373398435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8724019787079637831197913 6543014840309728373398435)
                ·
                  refine ⟨9814522260464592560097653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543014840309728373398435 9814522260464592560097653)
                  ·
                    refine ⟨920111461918555552509155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9814522260464592560097653 920111461918555552509155)
                    ·
                      rfl

theorem cell23_5375732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5375732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375732 prefixEnd_5375732 := by exact prefixLift 5375732
  have htrace : WordTrace (prefixWord ++ tailWord_5375732) baseStart_5375732 baseEnd_5375732 := by
    simpa [prefixWord, tailWord_5375732, baseEnd_5375732] using wordTrace_append hprefix tailTrace_5375732
  have hstable : (prefixWord ++ tailWord_5375732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375732).length < 2 ^ (prefixWord ++ tailWord_5375732).sum := by decide
  have hdescent : baseEnd_5375732 < baseStart_5375732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375768 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_5375768 : Nat := 118140960795 + 5375768 * 2 ^ 59
def prefixEnd_5375768 : Nat := 4983230072969 + 3 ^ 40 * 5375768 * 2
def baseEnd_5375768 : Nat := 2760352871059228516677299

theorem tailTrace_5375768 : CollatzResearch.WordTrace tailWord_5375768 prefixEnd_5375768 2760352871059228516677299 := by
  unfold tailWord_5375768
  simp only [CollatzResearch.WordTrace]
  refine ⟨98035183394259059462595979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130713577859012079283461305 98035183394259059462595979)
  ·
    refine ⟨147052775091388589193893969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98035183394259059462595979 147052775091388589193893969)
    ·
      refine ⟨110289581318541441895420477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147052775091388589193893969 110289581318541441895420477)
      ·
        refine ⟨41358592994453040710782679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110289581318541441895420477 41358592994453040710782679)
        ·
          refine ⟨62037889491679561066174019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41358592994453040710782679 62037889491679561066174019)
          ·
            refine ⟨93056834237519341599261029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62037889491679561066174019 93056834237519341599261029)
            ·
              refine ⟨17448156419534876549861443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93056834237519341599261029 17448156419534876549861443)
              ·
                refine ⟨26172234629302314824792165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17448156419534876549861443 26172234629302314824792165)
                ·
                  refine ⟨4907293992994184029648531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26172234629302314824792165 4907293992994184029648531)
                  ·
                    refine ⟨7360940989491276044472797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4907293992994184029648531 7360940989491276044472797)
                    ·
                      refine ⟨2760352871059228516677299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7360940989491276044472797 2760352871059228516677299)
                      ·
                        rfl

theorem cell23_5375768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_5375768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375768 prefixEnd_5375768 := by exact prefixLift 5375768
  have htrace : WordTrace (prefixWord ++ tailWord_5375768) baseStart_5375768 baseEnd_5375768 := by
    simpa [prefixWord, tailWord_5375768, baseEnd_5375768] using wordTrace_append hprefix tailTrace_5375768
  have hstable : (prefixWord ++ tailWord_5375768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375768).length < 2 ^ (prefixWord ++ tailWord_5375768).sum := by decide
  have hdescent : baseEnd_5375768 < baseStart_5375768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375795 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 3, 3, 2]
def baseStart_5375795 : Nat := 118140960795 + 5375795 * 2 ^ 59
def prefixEnd_5375795 : Nat := 4983230072969 + 3 ^ 40 * 5375795 * 2
def baseEnd_5375795 : Nat := 2760366735036899911039675

theorem tailTrace_5375795 : CollatzResearch.WordTrace tailWord_5375795 prefixEnd_5375795 2760366735036899911039675 := by
  unfold tailWord_5375795
  simp only [CollatzResearch.WordTrace]
  refine ⟨196071351559420302536424839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130714234372946868357616559 196071351559420302536424839)
  ·
    refine ⟨294107027339130453804637259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196071351559420302536424839 294107027339130453804637259)
    ·
      refine ⟨441160541008695680706955889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294107027339130453804637259 441160541008695680706955889)
      ·
        refine ⟨330870405756521760530216917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441160541008695680706955889 330870405756521760530216917)
        ·
          refine ⟨7754775134918478762426959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 330870405756521760530216917 7754775134918478762426959)
          ·
            refine ⟨11632162702377718143640439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754775134918478762426959 11632162702377718143640439)
            ·
              refine ⟨17448244053566577215460659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11632162702377718143640439 17448244053566577215460659)
              ·
                refine ⟨26172366080349865823190989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17448244053566577215460659 26172366080349865823190989)
                ·
                  refine ⟨9814637280131199683696621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26172366080349865823190989 9814637280131199683696621)
                  ·
                    refine ⟨3680488980049199881386233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9814637280131199683696621 3680488980049199881386233)
                    ·
                      refine ⟨2760366735036899911039675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680488980049199881386233 2760366735036899911039675)
                      ·
                        rfl

theorem cell23_5375795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 3, 2].length) (baseStart_5375795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375795 prefixEnd_5375795 := by exact prefixLift 5375795
  have htrace : WordTrace (prefixWord ++ tailWord_5375795) baseStart_5375795 baseEnd_5375795 := by
    simpa [prefixWord, tailWord_5375795, baseEnd_5375795] using wordTrace_append hprefix tailTrace_5375795
  have hstable : (prefixWord ++ tailWord_5375795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375795).length < 2 ^ (prefixWord ++ tailWord_5375795).sum := by decide
  have hdescent : baseEnd_5375795 < baseStart_5375795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375811 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5]
def baseStart_5375811 : Nat := 118140960795 + 5375811 * 2 ^ 59
def prefixEnd_5375811 : Nat := 4983230072969 + 3 ^ 40 * 5375811 * 2
def baseEnd_5375811 : Nat := 2760374950727371848439601

theorem tailTrace_5375811 : CollatzResearch.WordTrace tailWord_5375811 prefixEnd_5375811 2760374950727371848439601 := by
  unfold tailWord_5375811
  simp only [CollatzResearch.WordTrace]
  refine ⟨196071935127362337269007287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130714623418241558179338191 196071935127362337269007287)
  ·
    refine ⟨294107902691043505903510931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196071935127362337269007287 294107902691043505903510931)
    ·
      refine ⟨441161854036565258855266397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294107902691043505903510931 441161854036565258855266397)
      ·
        refine ⟨165435695263711972070724899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441161854036565258855266397 165435695263711972070724899)
        ·
          refine ⟨248153542895567958106087349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165435695263711972070724899 248153542895567958106087349)
          ·
            refine ⟨23264394646459496072445689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248153542895567958106087349 23264394646459496072445689)
            ·
              refine ⟨17448295984844622054334267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23264394646459496072445689 17448295984844622054334267)
              ·
                refine ⟨26172443977266933081501401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17448295984844622054334267 26172443977266933081501401)
                ·
                  refine ⟨19629332982950199811126051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26172443977266933081501401 19629332982950199811126051)
                  ·
                    refine ⟨29443999474425299716689077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19629332982950199811126051 29443999474425299716689077)
                    ·
                      refine ⟨2760374950727371848439601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29443999474425299716689077 2760374950727371848439601)
                      ·
                        rfl

theorem cell23_5375811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_5375811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375811 prefixEnd_5375811 := by exact prefixLift 5375811
  have htrace : WordTrace (prefixWord ++ tailWord_5375811) baseStart_5375811 baseEnd_5375811 := by
    simpa [prefixWord, tailWord_5375811, baseEnd_5375811] using wordTrace_append hprefix tailTrace_5375811
  have hstable : (prefixWord ++ tailWord_5375811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375811).length < 2 ^ (prefixWord ++ tailWord_5375811).sum := by decide
  have hdescent : baseEnd_5375811 < baseStart_5375811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375828 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_5375828 : Nat := 118140960795 + 5375828 * 2 ^ 59
def prefixEnd_5375828 : Nat := 4983230072969 + 3 ^ 40 * 5375828 * 2
def baseEnd_5375828 : Nat := 2760383679898498281927023

theorem tailTrace_5375828 : CollatzResearch.WordTrace tailWord_5375828 prefixEnd_5375828 2760383679898498281927023 := by
  unfold tailWord_5375828
  simp only [CollatzResearch.WordTrace]
  refine ⟨98036277584150374586188069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130715036778867166114917425 98036277584150374586188069)
  ·
    refine ⟨18381802047028195234910263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98036277584150374586188069 18381802047028195234910263)
    ·
      refine ⟨27572703070542292852365395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18381802047028195234910263 27572703070542292852365395)
      ·
        refine ⟨41359054605813439278548093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27572703070542292852365395 41359054605813439278548093)
        ·
          refine ⟨15509645477180039729455535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41359054605813439278548093 15509645477180039729455535)
          ·
            refine ⟨23264468215770059594183303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15509645477180039729455535 23264468215770059594183303)
            ·
              refine ⟨34896702323655089391274955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23264468215770059594183303 34896702323655089391274955)
              ·
                refine ⟨52345053485482634086912433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34896702323655089391274955 52345053485482634086912433)
                ·
                  refine ⟨39258790114111975565184325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52345053485482634086912433 39258790114111975565184325)
                  ·
                    refine ⟨7361023146395995418472061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39258790114111975565184325 7361023146395995418472061)
                    ·
                      refine ⟨2760383679898498281927023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7361023146395995418472061 2760383679898498281927023)
                      ·
                        rfl

theorem cell23_5375828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_5375828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375828 prefixEnd_5375828 := by exact prefixLift 5375828
  have htrace : WordTrace (prefixWord ++ tailWord_5375828) baseStart_5375828 baseEnd_5375828 := by
    simpa [prefixWord, tailWord_5375828, baseEnd_5375828] using wordTrace_append hprefix tailTrace_5375828
  have hstable : (prefixWord ++ tailWord_5375828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375828).length < 2 ^ (prefixWord ++ tailWord_5375828).sum := by decide
  have hdescent : baseEnd_5375828 < baseStart_5375828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375842 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5375842 : Nat := 118140960795 + 5375842 * 2 ^ 59
def prefixEnd_5375842 : Nat := 4983230072969 + 3 ^ 40 * 5375842 * 2
def baseEnd_5375842 : Nat := 2760390868627661227151959

theorem tailTrace_5375842 : CollatzResearch.WordTrace tailWord_5375842 prefixEnd_5375842 2760390868627661227151959 := by
  unfold tailWord_5375842
  simp only [CollatzResearch.WordTrace]
  refine ⟨49018266447562507390846445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130715377193500019708923853 49018266447562507390846445)
  ·
    refine ⟨18381849917835940271567417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49018266447562507390846445 18381849917835940271567417)
    ·
      refine ⟨13786387438376955203675563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18381849917835940271567417 13786387438376955203675563)
      ·
        refine ⟨20679581157565432805513345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13786387438376955203675563 20679581157565432805513345)
        ·
          refine ⟨15509685868174074604135009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20679581157565432805513345 15509685868174074604135009)
          ·
            refine ⟨11632264401130555953101257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15509685868174074604135009 11632264401130555953101257)
            ·
              refine ⟨8724198300847916964825943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11632264401130555953101257 8724198300847916964825943)
              ·
                refine ⟨13086297451271875447238915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724198300847916964825943 13086297451271875447238915)
                ·
                  refine ⟨19629446176907813170858373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13086297451271875447238915 19629446176907813170858373)
                  ·
                    refine ⟨3680521158170214969535945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19629446176907813170858373 3680521158170214969535945)
                    ·
                      refine ⟨2760390868627661227151959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680521158170214969535945 2760390868627661227151959)
                      ·
                        rfl

theorem cell23_5375842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5375842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375842 prefixEnd_5375842 := by exact prefixLift 5375842
  have htrace : WordTrace (prefixWord ++ tailWord_5375842) baseStart_5375842 baseEnd_5375842 := by
    simpa [prefixWord, tailWord_5375842, baseEnd_5375842] using wordTrace_append hprefix tailTrace_5375842
  have hstable : (prefixWord ++ tailWord_5375842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375842).length < 2 ^ (prefixWord ++ tailWord_5375842).sum := by decide
  have hdescent : baseEnd_5375842 < baseStart_5375842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375898 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5375898 : Nat := 118140960795 + 5375898 * 2 ^ 59
def prefixEnd_5375898 : Nat := 4983230072969 + 3 ^ 40 * 5375898 * 2
def baseEnd_5375898 : Nat := 2760419623544313008051701

theorem tailTrace_5375898 : CollatzResearch.WordTrace tailWord_5375898 prefixEnd_5375898 2760419623544313008051701 := by
  unfold tailWord_5375898
  simp only [CollatzResearch.WordTrace]
  refine ⟨49018777069511787781856087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130716738852031434084949565 49018777069511787781856087)
  ·
    refine ⟨73528165604267681672784131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49018777069511787781856087 73528165604267681672784131)
    ·
      refine ⟨110292248406401522509176197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73528165604267681672784131 110292248406401522509176197)
      ·
        refine ⟨20679796576200285470470537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110292248406401522509176197 20679796576200285470470537)
        ·
          refine ⟨15509847432150214102852903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20679796576200285470470537 15509847432150214102852903)
          ·
            refine ⟨23264771148225321154279355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15509847432150214102852903 23264771148225321154279355)
            ·
              refine ⟨34897156722337981731419033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23264771148225321154279355 34897156722337981731419033)
              ·
                refine ⟨26172867541753486298564275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34897156722337981731419033 26172867541753486298564275)
                ·
                  refine ⟨39259301312630229447846413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26172867541753486298564275 39259301312630229447846413)
                  ·
                    refine ⟨14722237992236336042942405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39259301312630229447846413 14722237992236336042942405)
                    ·
                      refine ⟨2760419623544313008051701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14722237992236336042942405 2760419623544313008051701)
                      ·
                        rfl

theorem cell23_5375898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5375898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375898 prefixEnd_5375898 := by exact prefixLift 5375898
  have htrace : WordTrace (prefixWord ++ tailWord_5375898) baseStart_5375898 baseEnd_5375898 := by
    simpa [prefixWord, tailWord_5375898, baseEnd_5375898] using wordTrace_append hprefix tailTrace_5375898
  have hstable : (prefixWord ++ tailWord_5375898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375898).length < 2 ^ (prefixWord ++ tailWord_5375898).sum := by decide
  have hdescent : baseEnd_5375898 < baseStart_5375898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375932 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5375932 : Nat := 118140960795 + 5375932 * 2 ^ 59
def prefixEnd_5375932 : Nat := 4983230072969 + 3 ^ 40 * 5375932 * 2
def baseEnd_5375932 : Nat := 2760437081886565875026545

theorem tailTrace_5375932 : CollatzResearch.WordTrace tailWord_5375932 prefixEnd_5375932 2760437081886565875026545 := by
  unfold tailWord_5375932
  simp only [CollatzResearch.WordTrace]
  refine ⟨98038174179961987467081025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130717565573282649956108033 98038174179961987467081025)
  ·
    refine ⟨73528630634971490600310769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98038174179961987467081025 73528630634971490600310769)
    ·
      refine ⟨55146472976228617950233077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73528630634971490600310769 55146472976228617950233077)
      ·
        refine ⟨5169981841521432932834351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55146472976228617950233077 5169981841521432932834351)
        ·
          refine ⟨7754972762282149399251527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169981841521432932834351 7754972762282149399251527)
          ·
            refine ⟨11632459143423224098877291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7754972762282149399251527 11632459143423224098877291)
            ·
              refine ⟨17448688715134836148315937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11632459143423224098877291 17448688715134836148315937)
              ·
                refine ⟨13086516536351127111236953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17448688715134836148315937 13086516536351127111236953)
                ·
                  refine ⟨9814887402263345333427715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13086516536351127111236953 9814887402263345333427715)
                  ·
                    refine ⟨14722331103395018000141573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9814887402263345333427715 14722331103395018000141573)
                    ·
                      refine ⟨2760437081886565875026545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14722331103395018000141573 2760437081886565875026545)
                      ·
                        rfl

theorem cell23_5375932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5375932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375932 prefixEnd_5375932 := by exact prefixLift 5375932
  have htrace : WordTrace (prefixWord ++ tailWord_5375932) baseStart_5375932 baseEnd_5375932 := by
    simpa [prefixWord, tailWord_5375932, baseEnd_5375932] using wordTrace_append hprefix tailTrace_5375932
  have hstable : (prefixWord ++ tailWord_5375932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375932).length < 2 ^ (prefixWord ++ tailWord_5375932).sum := by decide
  have hdescent : baseEnd_5375932 < baseStart_5375932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5375941 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_5375941 : Nat := 118140960795 + 5375941 * 2 ^ 59
def prefixEnd_5375941 : Nat := 4983230072969 + 3 ^ 40 * 5375941 * 2
def baseEnd_5375941 : Nat := 2760441703212456339814003

theorem tailTrace_5375941 : CollatzResearch.WordTrace tailWord_5375941 prefixEnd_5375941 2760441703212456339814003 := by
  unfold tailWord_5375941
  simp only [CollatzResearch.WordTrace]
  refine ⟨196076676616891369471239677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130717784411260912980826451 196076676616891369471239677)
  ·
    refine ⟨73528753731334263551714879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196076676616891369471239677 73528753731334263551714879)
    ·
      refine ⟨110293130597001395327572319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73528753731334263551714879 110293130597001395327572319)
      ·
        refine ⟨165439695895502092991358479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110293130597001395327572319 165439695895502092991358479)
        ·
          refine ⟨248159543843253139487037719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165439695895502092991358479 248159543843253139487037719)
          ·
            refine ⟨372239315764879709230556579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248159543843253139487037719 372239315764879709230556579)
            ·
              refine ⟨558358973647319563845834869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372239315764879709230556579 558358973647319563845834869)
              ·
                refine ⟨52346153779436209110547019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 558358973647319563845834869 52346153779436209110547019)
                ·
                  refine ⟨78519230669154313665820529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52346153779436209110547019 78519230669154313665820529)
                  ·
                    refine ⟨58889423001865735249365397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78519230669154313665820529 58889423001865735249365397)
                    ·
                      refine ⟨2760441703212456339814003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58889423001865735249365397 2760441703212456339814003)
                      ·
                        rfl

theorem cell23_5375941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_5375941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5375941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5375941 prefixEnd_5375941 := by exact prefixLift 5375941
  have htrace : WordTrace (prefixWord ++ tailWord_5375941) baseStart_5375941 baseEnd_5375941 := by
    simpa [prefixWord, tailWord_5375941, baseEnd_5375941] using wordTrace_append hprefix tailTrace_5375941
  have hstable : (prefixWord ++ tailWord_5375941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5375941).length < 2 ^ (prefixWord ++ tailWord_5375941).sum := by decide
  have hdescent : baseEnd_5375941 < baseStart_5375941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5375941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376008 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_5376008 : Nat := 118140960795 + 5376008 * 2 ^ 59
def prefixEnd_5376008 : Nat := 4983230072969 + 3 ^ 40 * 5376008 * 2
def baseEnd_5376008 : Nat := 2760476106416307577676195

theorem tailTrace_5376008 : CollatzResearch.WordTrace tailWord_5376008 prefixEnd_5376008 2760476106416307577676195 := by
  unfold tailWord_5376008
  simp only [CollatzResearch.WordTrace]
  refine ⟨98039560153824319956964339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130719413538432426609285785 98039560153824319956964339)
  ·
    refine ⟨147059340230736479935446509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98039560153824319956964339 147059340230736479935446509)
    ·
      refine ⟨55147252586526179975792441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147059340230736479935446509 55147252586526179975792441)
      ·
        refine ⟨41360439439894634981844331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55147252586526179975792441 41360439439894634981844331)
        ·
          refine ⟨62040659159841952472766497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41360439439894634981844331 62040659159841952472766497)
          ·
            refine ⟨46530494369881464354574873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62040659159841952472766497 46530494369881464354574873)
            ·
              refine ⟨34897870777411098265931155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46530494369881464354574873 34897870777411098265931155)
              ·
                refine ⟨52346806166116647398896733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34897870777411098265931155 52346806166116647398896733)
                ·
                  refine ⟨19630052312293742774586275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52346806166116647398896733 19630052312293742774586275)
                  ·
                    refine ⟨29445078468440614161879413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19630052312293742774586275 29445078468440614161879413)
                    ·
                      refine ⟨2760476106416307577676195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29445078468440614161879413 2760476106416307577676195)
                      ·
                        rfl

theorem cell23_5376008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_5376008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376008 prefixEnd_5376008 := by exact prefixLift 5376008
  have htrace : WordTrace (prefixWord ++ tailWord_5376008) baseStart_5376008 baseEnd_5376008 := by
    simpa [prefixWord, tailWord_5376008, baseEnd_5376008] using wordTrace_append hprefix tailTrace_5376008
  have hstable : (prefixWord ++ tailWord_5376008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376008).length < 2 ^ (prefixWord ++ tailWord_5376008).sum := by decide
  have hdescent : baseEnd_5376008 < baseStart_5376008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376025 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 3]
def baseStart_5376025 : Nat := 118140960795 + 5376025 * 2 ^ 59
def prefixEnd_5376025 : Nat := 4983230072969 + 3 ^ 40 * 5376025 * 2
def baseEnd_5376025 : Nat := 2760484835587434011163617

theorem tailTrace_5376025 : CollatzResearch.WordTrace tailWord_5376025 prefixEnd_5376025 2760484835587434011163617 := by
  unfold tailWord_5376025
  simp only [CollatzResearch.WordTrace]
  refine ⟨196079740348587051817297529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130719826899058034544865019 196079740348587051817297529)
  ·
    refine ⟨147059805261440288862973147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196079740348587051817297529 147059805261440288862973147)
    ·
      refine ⟨220589707892160433294459721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147059805261440288862973147 220589707892160433294459721)
      ·
        refine ⟨165442280919120324970844791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220589707892160433294459721 165442280919120324970844791)
        ·
          refine ⟨248163421378680487456267187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165442280919120324970844791 248163421378680487456267187)
          ·
            refine ⟨372245132068020731184400781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248163421378680487456267187 372245132068020731184400781)
            ·
              refine ⟨139591924525507774194150293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372245132068020731184400781 139591924525507774194150293)
              ·
                refine ⟨6543371462133176915350795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139591924525507774194150293 6543371462133176915350795)
                ·
                  refine ⟨9815057193199765373026193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543371462133176915350795 9815057193199765373026193)
                  ·
                    refine ⟨7361292894899824029769645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9815057193199765373026193 7361292894899824029769645)
                    ·
                      refine ⟨2760484835587434011163617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7361292894899824029769645 2760484835587434011163617)
                      ·
                        rfl

theorem cell23_5376025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_5376025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376025 prefixEnd_5376025 := by exact prefixLift 5376025
  have htrace : WordTrace (prefixWord ++ tailWord_5376025) baseStart_5376025 baseEnd_5376025 := by
    simpa [prefixWord, tailWord_5376025, baseEnd_5376025] using wordTrace_append hprefix tailTrace_5376025
  have hstable : (prefixWord ++ tailWord_5376025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376025).length < 2 ^ (prefixWord ++ tailWord_5376025).sum := by decide
  have hdescent : baseEnd_5376025 < baseStart_5376025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376036 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_5376036 : Nat := 118140960795 + 5376036 * 2 ^ 59
def prefixEnd_5376036 : Nat := 4983230072969 + 3 ^ 40 * 5376036 * 2
def baseEnd_5376036 : Nat := 920163494624877822708689

theorem tailTrace_5376036 : CollatzResearch.WordTrace tailWord_5376036 prefixEnd_5376036 920163494624877822708689 := by
  unfold tailWord_5376036
  simp only [CollatzResearch.WordTrace]
  refine ⟨98040070775773600347973981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130720094367698133797298641 98040070775773600347973981)
  ·
    refine ⟨36765026540915100130490243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98040070775773600347973981 36765026540915100130490243)
    ·
      refine ⟨55147539811372650195735365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36765026540915100130490243 55147539811372650195735365)
      ·
        refine ⟨10340163714632371911700381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55147539811372650195735365 10340163714632371911700381)
        ·
          refine ⟨3877561392987139466887643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10340163714632371911700381 3877561392987139466887643)
          ·
            refine ⟨5816342089480709200331465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3877561392987139466887643 5816342089480709200331465)
            ·
              refine ⟨4362256567110531900248599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5816342089480709200331465 4362256567110531900248599)
              ·
                refine ⟨6543384850665797850372899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4362256567110531900248599 6543384850665797850372899)
                ·
                  refine ⟨9815077275998696775559349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543384850665797850372899 9815077275998696775559349)
                  ·
                    refine ⟨920163494624877822708689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9815077275998696775559349 920163494624877822708689)
                    ·
                      rfl

theorem cell23_5376036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_5376036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376036 prefixEnd_5376036 := by exact prefixLift 5376036
  have htrace : WordTrace (prefixWord ++ tailWord_5376036) baseStart_5376036 baseEnd_5376036 := by
    simpa [prefixWord, tailWord_5376036, baseEnd_5376036] using wordTrace_append hprefix tailTrace_5376036
  have hstable : (prefixWord ++ tailWord_5376036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376036).length < 2 ^ (prefixWord ++ tailWord_5376036).sum := by decide
  have hdescent : baseEnd_5376036 < baseStart_5376036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376039 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5376039 : Nat := 118140960795 + 5376039 * 2 ^ 59
def prefixEnd_5376039 : Nat := 4983230072969 + 3 ^ 40 * 5376039 * 2
def baseEnd_5376039 : Nat := 2760492024316596956388553

theorem tailTrace_5376039 : CollatzResearch.WordTrace tailWord_5376039 prefixEnd_5376039 2760492024316596956388553 := by
  unfold tailWord_5376039
  simp only [CollatzResearch.WordTrace]
  refine ⟨196080250970536332208307171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130720167313690888138871447 196080250970536332208307171)
  ·
    refine ⟨294120376455804498312460757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196080250970536332208307171 294120376455804498312460757)
    ·
      refine ⟨6893446323182917929198299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 294120376455804498312460757 6893446323182917929198299)
      ·
        refine ⟨10340169484774376893797449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6893446323182917929198299 10340169484774376893797449)
        ·
          refine ⟨7755127113580782670348087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10340169484774376893797449 7755127113580782670348087)
          ·
            refine ⟨11632690670371174005522131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7755127113580782670348087 11632690670371174005522131)
            ·
              refine ⟨17449036005556761008283197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11632690670371174005522131 17449036005556761008283197)
              ·
                refine ⟨6543388502083785378106199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17449036005556761008283197 6543388502083785378106199)
                ·
                  refine ⟨9815082753125678067159299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543388502083785378106199 9815082753125678067159299)
                  ·
                    refine ⟨14722624129688517100738949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9815082753125678067159299 14722624129688517100738949)
                    ·
                      refine ⟨2760492024316596956388553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14722624129688517100738949 2760492024316596956388553)
                      ·
                        rfl

theorem cell23_5376039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5376039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376039 prefixEnd_5376039 := by exact prefixLift 5376039
  have htrace : WordTrace (prefixWord ++ tailWord_5376039) baseStart_5376039 baseEnd_5376039 := by
    simpa [prefixWord, tailWord_5376039, baseEnd_5376039] using wordTrace_append hprefix tailTrace_5376039
  have hstable : (prefixWord ++ tailWord_5376039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376039).length < 2 ^ (prefixWord ++ tailWord_5376039).sum := by decide
  have hdescent : baseEnd_5376039 < baseStart_5376039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376165 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_5376165 : Nat := 118140960795 + 5376165 * 2 ^ 59
def prefixEnd_5376165 : Nat := 4983230072969 + 3 ^ 40 * 5376165 * 2
def baseEnd_5376165 : Nat := 920185574293021154470991

theorem tailTrace_5376165 : CollatzResearch.WordTrace tailWord_5376165 prefixEnd_5376165 920185574293021154470991 := by
  unfold tailWord_5376165
  simp only [CollatzResearch.WordTrace]
  refine ⟨196084846568079855727393949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130723231045386570484929299 196084846568079855727393949)
  ·
    refine ⟨73531817463029945897772731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196084846568079855727393949 73531817463029945897772731)
    ·
      refine ⟨110297726194544918846659097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73531817463029945897772731 110297726194544918846659097)
      ·
        refine ⟨82723294645908689134994323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110297726194544918846659097 82723294645908689134994323)
        ·
          refine ⟨124084941968863033702491485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82723294645908689134994323 124084941968863033702491485)
          ·
            refine ⟨46531853238323637638434307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124084941968863033702491485 46531853238323637638434307)
            ·
              refine ⟨69797779857485456457651461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46531853238323637638434307 69797779857485456457651461)
              ·
                refine ⟨13087083723278523085809649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69797779857485456457651461 13087083723278523085809649)
                ·
                  refine ⟨9815312792458892314357237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13087083723278523085809649 9815312792458892314357237)
                  ·
                    refine ⟨920185574293021154470991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9815312792458892314357237 920185574293021154470991)
                    ·
                      rfl

theorem cell23_5376165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_5376165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376165 prefixEnd_5376165 := by exact prefixLift 5376165
  have htrace : WordTrace (prefixWord ++ tailWord_5376165) baseStart_5376165 baseEnd_5376165 := by
    simpa [prefixWord, tailWord_5376165, baseEnd_5376165] using wordTrace_append hprefix tailTrace_5376165
  have hstable : (prefixWord ++ tailWord_5376165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376165).length < 2 ^ (prefixWord ++ tailWord_5376165).sum := by decide
  have hdescent : baseEnd_5376165 < baseStart_5376165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376180 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5376180 : Nat := 118140960795 + 5376180 * 2 ^ 59
def prefixEnd_5376180 : Nat := 4983230072969 + 3 ^ 40 * 5376180 * 2
def baseEnd_5376180 : Nat := 2760564425088880904725405

theorem tailTrace_5376180 : CollatzResearch.WordTrace tailWord_5376180 prefixEnd_5376180 2760564425088880904725405 := by
  unfold tailWord_5376180
  simp only [CollatzResearch.WordTrace]
  refine ⟨98042696831512756644594997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130723595775350342192793329 98042696831512756644594997)
  ·
    refine ⟨9191502827954320935430781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98042696831512756644594997 9191502827954320935430781)
    ·
      refine ⟨3446813560482870350786543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9191502827954320935430781 3446813560482870350786543)
      ·
        refine ⟨5170220340724305526179815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446813560482870350786543 5170220340724305526179815)
        ·
          refine ⟨7755330511086458289269723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5170220340724305526179815 7755330511086458289269723)
          ·
            refine ⟨11632995766629687433904585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7755330511086458289269723 11632995766629687433904585)
            ·
              refine ⟨8724746824972265575428439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11632995766629687433904585 8724746824972265575428439)
              ·
                refine ⟨13087120237458398363142659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724746824972265575428439 13087120237458398363142659)
                ·
                  refine ⟨19630680356187597544713989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13087120237458398363142659 19630680356187597544713989)
                  ·
                    refine ⟨3680752566785174539633873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19630680356187597544713989 3680752566785174539633873)
                    ·
                      refine ⟨2760564425088880904725405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680752566785174539633873 2760564425088880904725405)
                      ·
                        rfl

theorem cell23_5376180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5376180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376180 prefixEnd_5376180 := by exact prefixLift 5376180
  have htrace : WordTrace (prefixWord ++ tailWord_5376180) baseStart_5376180 baseEnd_5376180 := by
    simpa [prefixWord, tailWord_5376180, baseEnd_5376180] using wordTrace_append hprefix tailTrace_5376180
  have hstable : (prefixWord ++ tailWord_5376180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376180).length < 2 ^ (prefixWord ++ tailWord_5376180).sum := by decide
  have hdescent : baseEnd_5376180 < baseStart_5376180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376185 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5376185 : Nat := 118140960795 + 5376185 * 2 ^ 59
def prefixEnd_5376185 : Nat := 4983230072969 + 3 ^ 40 * 5376185 * 2
def baseEnd_5376185 : Nat := 2760566992492153385162881

theorem tailTrace_5376185 : CollatzResearch.WordTrace tailWord_5376185 prefixEnd_5376185 2760566992492153385162881 := by
  unfold tailWord_5376185
  simp only [CollatzResearch.WordTrace]
  refine ⟨196085576028007399143122009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130723717352004932762081339 196085576028007399143122009)
  ·
    refine ⟨147064182021005549357341507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196085576028007399143122009 147064182021005549357341507)
    ·
      refine ⟨220596273031508324036012261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147064182021005549357341507 220596273031508324036012261)
      ·
        refine ⟨41361801193407810756752299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220596273031508324036012261 41361801193407810756752299)
        ·
          refine ⟨62042701790111716135128449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41361801193407810756752299 62042701790111716135128449)
          ·
            refine ⟨46532026342583787101346337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62042701790111716135128449 46532026342583787101346337)
            ·
              refine ⟨34899019756937840326009753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46532026342583787101346337 34899019756937840326009753)
              ·
                refine ⟨26174264817703380244507315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34899019756937840326009753 26174264817703380244507315)
                ·
                  refine ⟨39261397226555070366760973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26174264817703380244507315 39261397226555070366760973)
                  ·
                    refine ⟨14723023959958151387535365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39261397226555070366760973 14723023959958151387535365)
                    ·
                      refine ⟨2760566992492153385162881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14723023959958151387535365 2760566992492153385162881)
                      ·
                        rfl

theorem cell23_5376185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5376185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376185 prefixEnd_5376185 := by exact prefixLift 5376185
  have htrace : WordTrace (prefixWord ++ tailWord_5376185) baseStart_5376185 baseEnd_5376185 := by
    simpa [prefixWord, tailWord_5376185, baseEnd_5376185] using wordTrace_append hprefix tailTrace_5376185
  have hstable : (prefixWord ++ tailWord_5376185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376185).length < 2 ^ (prefixWord ++ tailWord_5376185).sum := by decide
  have hdescent : baseEnd_5376185 < baseStart_5376185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376202 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_5376202 : Nat := 118140960795 + 5376202 * 2 ^ 59
def prefixEnd_5376202 : Nat := 4983230072969 + 3 ^ 40 * 5376202 * 2
def baseEnd_5376202 : Nat := 2760575721663279818650303

theorem tailTrace_5376202 : CollatzResearch.WordTrace tailWord_5376202 prefixEnd_5376202 2760575721663279818650303 := by
  unfold tailWord_5376202
  simp only [CollatzResearch.WordTrace]
  refine ⟨49021549017236452761622715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130724130712630540697660573 49021549017236452761622715)
  ·
    refine ⟨73532323525854679142434073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49021549017236452761622715 73532323525854679142434073)
    ·
      refine ⟨55149242644391009356825555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73532323525854679142434073 55149242644391009356825555)
      ·
        refine ⟨82723863966586514035238333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55149242644391009356825555 82723863966586514035238333)
        ·
          refine ⟨31021448987469942763214375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82723863966586514035238333 31021448987469942763214375)
          ·
            refine ⟨46532173481204914144821563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31021448987469942763214375 46532173481204914144821563)
            ·
              refine ⟨69798260221807371217232345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46532173481204914144821563 69798260221807371217232345)
              ·
                refine ⟨52348695166355528412924259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69798260221807371217232345 52348695166355528412924259)
                ·
                  refine ⟨78523042749533292619386389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52348695166355528412924259 78523042749533292619386389)
                  ·
                    refine ⟨3680767628884373091533737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78523042749533292619386389 3680767628884373091533737)
                    ·
                      refine ⟨2760575721663279818650303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680767628884373091533737 2760575721663279818650303)
                      ·
                        rfl

theorem cell23_5376202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_5376202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376202 prefixEnd_5376202 := by exact prefixLift 5376202
  have htrace : WordTrace (prefixWord ++ tailWord_5376202) baseStart_5376202 baseEnd_5376202 := by
    simpa [prefixWord, tailWord_5376202, baseEnd_5376202] using wordTrace_append hprefix tailTrace_5376202
  have hstable : (prefixWord ++ tailWord_5376202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376202).length < 2 ^ (prefixWord ++ tailWord_5376202).sum := by decide
  have hdescent : baseEnd_5376202 < baseStart_5376202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376225 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 8]
def baseStart_5376225 : Nat := 118140960795 + 5376225 * 2 ^ 59
def prefixEnd_5376225 : Nat := 4983230072969 + 3 ^ 40 * 5376225 * 2
def baseEnd_5376225 : Nat := 306731947968703692073633

theorem tailTrace_5376225 : CollatzResearch.WordTrace tailWord_5376225 prefixEnd_5376225 306731947968703692073633 := by
  unfold tailWord_5376225
  simp only [CollatzResearch.WordTrace]
  refine ⟨196087034947862485974578129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130724689965241657316385419 196087034947862485974578129)
  ·
    refine ⟨147065276210896864480933597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196087034947862485974578129 147065276210896864480933597)
    ·
      refine ⟨55149478579086324180350099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147065276210896864480933597 55149478579086324180350099)
      ·
        refine ⟨82724217868629486270525149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55149478579086324180350099 82724217868629486270525149)
        ·
          refine ⟨31021581700736057351446931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82724217868629486270525149 31021581700736057351446931)
          ·
            refine ⟨46532372551104086027170397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31021581700736057351446931 46532372551104086027170397)
            ·
              refine ⟨17449639706664032260188899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46532372551104086027170397 17449639706664032260188899)
              ·
                refine ⟨26174459559996048390283349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17449639706664032260188899 26174459559996048390283349)
                ·
                  refine ⟨306731947968703692073633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26174459559996048390283349 306731947968703692073633)
                  ·
                    rfl

theorem cell23_5376225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_5376225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376225 prefixEnd_5376225 := by exact prefixLift 5376225
  have htrace : WordTrace (prefixWord ++ tailWord_5376225) baseStart_5376225 baseEnd_5376225 := by
    simpa [prefixWord, tailWord_5376225, baseEnd_5376225] using wordTrace_append hprefix tailTrace_5376225
  have hstable : (prefixWord ++ tailWord_5376225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376225).length < 2 ^ (prefixWord ++ tailWord_5376225).sum := by decide
  have hdescent : baseEnd_5376225 < baseStart_5376225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376229 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_5376229 : Nat := 118140960795 + 5376229 * 2 ^ 59
def prefixEnd_5376229 : Nat := 4983230072969 + 3 ^ 40 * 5376229 * 2
def baseEnd_5376229 : Nat := 920196528546983737670893

theorem tailTrace_5376229 : CollatzResearch.WordTrace tailWord_5376229 prefixEnd_5376229 920196528546983737670893 := by
  unfold tailWord_5376229
  simp only [CollatzResearch.WordTrace]
  refine ⟨196087180839847994657723741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130724787226565329771815827 196087180839847994657723741)
  ·
    refine ⟨73532692814942997996646403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196087180839847994657723741 73532692814942997996646403)
    ·
      refine ⟨110299039222414496994969605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73532692814942997996646403 110299039222414496994969605)
      ·
        refine ⟨20681069854202718186556801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110299039222414496994969605 20681069854202718186556801)
        ·
          refine ⟨15510802390652038639917601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20681069854202718186556801 15510802390652038639917601)
          ·
            refine ⟨11633101792989028979938201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15510802390652038639917601 11633101792989028979938201)
            ·
              refine ⟨8724826344741771734953651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11633101792989028979938201 8724826344741771734953651)
              ·
                refine ⟨13087239517112657602430477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8724826344741771734953651 13087239517112657602430477)
                ·
                  refine ⟨4907714818917246600911429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13087239517112657602430477 4907714818917246600911429)
                  ·
                    refine ⟨920196528546983737670893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4907714818917246600911429 920196528546983737670893)
                    ·
                      rfl

theorem cell23_5376229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_5376229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376229 prefixEnd_5376229 := by exact prefixLift 5376229
  have htrace : WordTrace (prefixWord ++ tailWord_5376229) baseStart_5376229 baseEnd_5376229 := by
    simpa [prefixWord, tailWord_5376229, baseEnd_5376229] using wordTrace_append hprefix tailTrace_5376229
  have hstable : (prefixWord ++ tailWord_5376229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376229).length < 2 ^ (prefixWord ++ tailWord_5376229).sum := by decide
  have hdescent : baseEnd_5376229 < baseStart_5376229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376279 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 4, 3, 2]
def baseStart_5376279 : Nat := 118140960795 + 5376279 * 2 ^ 59
def prefixEnd_5376279 : Nat := 4983230072969 + 3 ^ 40 * 5376279 * 2
def baseEnd_5376279 : Nat := 2760615259673676017387449

theorem tailTrace_5376279 : CollatzResearch.WordTrace tailWord_5376279 prefixEnd_5376279 2760615259673676017387449 := by
  unfold tailWord_5376279
  simp only [CollatzResearch.WordTrace]
  refine ⟨196089004489666853197043891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130726002993111235464695927 196089004489666853197043891)
  ·
    refine ⟨294133506734500279795565837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196089004489666853197043891 294133506734500279795565837)
    ·
      refine ⟨110300065025437604923337189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294133506734500279795565837 110300065025437604923337189)
      ·
        refine ⟨20681262192269550923125723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110300065025437604923337189 20681262192269550923125723)
        ·
          refine ⟨31021893288404326384688585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20681262192269550923125723 31021893288404326384688585)
          ·
            refine ⟨23266419966303244788516439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31021893288404326384688585 23266419966303244788516439)
            ·
              refine ⟨34899629949454867182774659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23266419966303244788516439 34899629949454867182774659)
              ·
                refine ⟨52349444924182300774161989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34899629949454867182774659 52349444924182300774161989)
                ·
                  refine ⟨9815520923284181395155373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52349444924182300774161989 9815520923284181395155373)
                  ·
                    refine ⟨3680820346231568023183265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9815520923284181395155373 3680820346231568023183265)
                    ·
                      refine ⟨2760615259673676017387449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680820346231568023183265 2760615259673676017387449)
                      ·
                        rfl

theorem cell23_5376279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_5376279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376279 prefixEnd_5376279 := by exact prefixLift 5376279
  have htrace : WordTrace (prefixWord ++ tailWord_5376279) baseStart_5376279 baseEnd_5376279 := by
    simpa [prefixWord, tailWord_5376279, baseEnd_5376279] using wordTrace_append hprefix tailTrace_5376279
  have hstable : (prefixWord ++ tailWord_5376279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376279).length < 2 ^ (prefixWord ++ tailWord_5376279).sum := by decide
  have hdescent : baseEnd_5376279 < baseStart_5376279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376306 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_5376306 : Nat := 118140960795 + 5376306 * 2 ^ 59
def prefixEnd_5376306 : Nat := 4983230072969 + 3 ^ 40 * 5376306 * 2
def baseEnd_5376306 : Nat := 920209707883782470583275

theorem tailTrace_5376306 : CollatzResearch.WordTrace tailWord_5376306 prefixEnd_5376306 920209707883782470583275 := by
  unfold tailWord_5376306
  simp only [CollatzResearch.WordTrace]
  refine ⟨49022497315142259202069193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130726659507046024538851181 49022497315142259202069193)
  ·
    refine ⟨36766872986356694401551895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49022497315142259202069193 36766872986356694401551895)
    ·
      refine ⟨55150309479535041602327843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36766872986356694401551895 55150309479535041602327843)
      ·
        refine ⟨82725464219302562403491765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55150309479535041602327843 82725464219302562403491765)
        ·
          refine ⟨7755512270559615225327353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82725464219302562403491765 7755512270559615225327353)
          ·
            refine ⟨5816634202919711418995515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7755512270559615225327353 5816634202919711418995515)
            ·
              refine ⟨8724951304379567128493273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816634202919711418995515 8724951304379567128493273)
              ·
                refine ⟨6543713478284675346369955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8724951304379567128493273 6543713478284675346369955)
                ·
                  refine ⟨9815570217427013019554933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6543713478284675346369955 9815570217427013019554933)
                  ·
                    refine ⟨920209707883782470583275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9815570217427013019554933 920209707883782470583275)
                    ·
                      rfl

theorem cell23_5376306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_5376306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376306 prefixEnd_5376306 := by exact prefixLift 5376306
  have htrace : WordTrace (prefixWord ++ tailWord_5376306) baseStart_5376306 baseEnd_5376306 := by
    simpa [prefixWord, tailWord_5376306, baseEnd_5376306] using wordTrace_append hprefix tailTrace_5376306
  have hstable : (prefixWord ++ tailWord_5376306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376306).length < 2 ^ (prefixWord ++ tailWord_5376306).sum := by decide
  have hdescent : baseEnd_5376306 < baseStart_5376306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376335 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_5376335 : Nat := 118140960795 + 5376335 * 2 ^ 59
def prefixEnd_5376335 : Nat := 4983230072969 + 3 ^ 40 * 5376335 * 2
def baseEnd_5376335 : Nat := 2760644014590327798287191

theorem tailTrace_5376335 : CollatzResearch.WordTrace tailWord_5376335 prefixEnd_5376335 2760644014590327798287191 := by
  unfold tailWord_5376335
  simp only [CollatzResearch.WordTrace]
  refine ⟨196091046977463974761082459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130727364651642649840721639 196091046977463974761082459)
  ·
    refine ⟨294136570466195962141623689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196091046977463974761082459 294136570466195962141623689)
    ·
      refine ⟨220602427849646971606217767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294136570466195962141623689 220602427849646971606217767)
      ·
        refine ⟨330903641774470457409326651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220602427849646971606217767 330903641774470457409326651)
        ·
          refine ⟨496355462661705686113989977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330903641774470457409326651 496355462661705686113989977)
          ·
            refine ⟨372266596996279264585492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496355462661705686113989977 372266596996279264585492483)
            ·
              refine ⟨558399895494418896878238725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372266596996279264585492483 558399895494418896878238725)
              ·
                refine ⟨104699980405203543164669761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 558399895494418896878238725 104699980405203543164669761)
                ·
                  refine ⟨78524985303902657373502321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104699980405203543164669761 78524985303902657373502321)
                  ·
                    refine ⟨58893738977926993030126741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78524985303902657373502321 58893738977926993030126741)
                    ·
                      refine ⟨2760644014590327798287191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58893738977926993030126741 2760644014590327798287191)
                      ·
                        rfl

theorem cell23_5376335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_5376335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376335 prefixEnd_5376335 := by exact prefixLift 5376335
  have htrace : WordTrace (prefixWord ++ tailWord_5376335) baseStart_5376335 baseEnd_5376335 := by
    simpa [prefixWord, tailWord_5376335, baseEnd_5376335] using wordTrace_append hprefix tailTrace_5376335
  have hstable : (prefixWord ++ tailWord_5376335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376335).length < 2 ^ (prefixWord ++ tailWord_5376335).sum := by decide
  have hdescent : baseEnd_5376335 < baseStart_5376335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376343 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 1, 2, 2]
def baseStart_5376343 : Nat := 118140960795 + 5376343 * 2 ^ 59
def prefixEnd_5376343 : Nat := 4983230072969 + 3 ^ 40 * 5376343 * 2
def baseEnd_5376343 : Nat := 2760648122435563766987155

theorem tailTrace_5376343 : CollatzResearch.WordTrace tailWord_5376343 prefixEnd_5376343 2760648122435563766987155 := by
  unfold tailWord_5376343
  simp only [CollatzResearch.WordTrace]
  refine ⟨196091338761434992127373683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130727559174289994751582455 196091338761434992127373683)
  ·
    refine ⟨294137008142152488191060525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196091338761434992127373683 294137008142152488191060525)
    ·
      refine ⟨110301378053307183071647697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294137008142152488191060525 110301378053307183071647697)
      ·
        refine ⟨82726033539980387303735773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110301378053307183071647697 82726033539980387303735773)
        ·
          refine ⟨31022262577492645238900915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82726033539980387303735773 31022262577492645238900915)
          ·
            refine ⟨46533393866238967858351373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31022262577492645238900915 46533393866238967858351373)
            ·
              refine ⟨17450022699839612946881765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46533393866238967858351373 17450022699839612946881765)
              ·
                refine ⟨3271879256219927427540331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17450022699839612946881765 3271879256219927427540331)
                ·
                  refine ⟨4907818884329891141310497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3271879256219927427540331 4907818884329891141310497)
                  ·
                    refine ⟨3680864163247418355982873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4907818884329891141310497 3680864163247418355982873)
                    ·
                      refine ⟨2760648122435563766987155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680864163247418355982873 2760648122435563766987155)
                      ·
                        rfl

theorem cell23_5376343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_5376343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376343 prefixEnd_5376343 := by exact prefixLift 5376343
  have htrace : WordTrace (prefixWord ++ tailWord_5376343) baseStart_5376343 baseEnd_5376343 := by
    simpa [prefixWord, tailWord_5376343, baseEnd_5376343] using wordTrace_append hprefix tailTrace_5376343
  have hstable : (prefixWord ++ tailWord_5376343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376343).length < 2 ^ (prefixWord ++ tailWord_5376343).sum := by decide
  have hdescent : baseEnd_5376343 < baseStart_5376343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376359 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_5376359 : Nat := 118140960795 + 5376359 * 2 ^ 59
def prefixEnd_5376359 : Nat := 4983230072969 + 3 ^ 40 * 5376359 * 2
def baseEnd_5376359 : Nat := 2760656338126035704387081

theorem tailTrace_5376359 : CollatzResearch.WordTrace tailWord_5376359 prefixEnd_5376359 2760656338126035704387081 := by
  unfold tailWord_5376359
  simp only [CollatzResearch.WordTrace]
  refine ⟨196091922329377026859956131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130727948219584684573304087 196091922329377026859956131)
  ·
    refine ⟨294137883494065540289934197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196091922329377026859956131 294137883494065540289934197)
    ·
      refine ⟨27575426577568644402181331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 294137883494065540289934197 27575426577568644402181331)
      ·
        refine ⟨41363139866352966603271997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27575426577568644402181331 41363139866352966603271997)
        ·
          refine ⟨15511177449882362476226999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41363139866352966603271997 15511177449882362476226999)
          ·
            refine ⟨23266766174823543714340499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15511177449882362476226999 23266766174823543714340499)
            ·
              refine ⟨34900149262235315571510749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23266766174823543714340499 34900149262235315571510749)
              ·
                refine ⟨13087555973338243339316531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34900149262235315571510749 13087555973338243339316531)
                ·
                  refine ⟨19631333960007365008974797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13087555973338243339316531 19631333960007365008974797)
                  ·
                    refine ⟨7361750235002761878365549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19631333960007365008974797 7361750235002761878365549)
                    ·
                      refine ⟨2760656338126035704387081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7361750235002761878365549 2760656338126035704387081)
                      ·
                        rfl

theorem cell23_5376359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_5376359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376359 prefixEnd_5376359 := by exact prefixLift 5376359
  have htrace : WordTrace (prefixWord ++ tailWord_5376359) baseStart_5376359 baseEnd_5376359 := by
    simpa [prefixWord, tailWord_5376359, baseEnd_5376359] using wordTrace_append hprefix tailTrace_5376359
  have hstable : (prefixWord ++ tailWord_5376359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376359).length < 2 ^ (prefixWord ++ tailWord_5376359).sum := by decide
  have hdescent : baseEnd_5376359 < baseStart_5376359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376392 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_5376392 : Nat := 118140960795 + 5376392 * 2 ^ 59
def prefixEnd_5376392 : Nat := 4983230072969 + 3 ^ 40 * 5376392 * 2
def baseEnd_5376392 : Nat := 920224427662544691758143

theorem tailTrace_5376392 : CollatzResearch.WordTrace tailWord_5376392 prefixEnd_5376392 920224427662544691758143 := by
  unfold tailWord_5376392
  simp only [CollatzResearch.WordTrace]
  refine ⟨98046562969128736747953715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130728750625504982330604953 98046562969128736747953715)
  ·
    refine ⟨147069844453693105121930573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98046562969128736747953715 147069844453693105121930573)
    ·
      refine ⟨55151191670134914420723965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147069844453693105121930573 55151191670134914420723965)
      ·
        refine ⟨20681696876300592907771487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55151191670134914420723965 20681696876300592907771487)
        ·
          refine ⟨31022545314450889361657231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20681696876300592907771487 31022545314450889361657231)
          ·
            refine ⟨46533817971676334042485847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31022545314450889361657231 46533817971676334042485847)
            ·
              refine ⟨69800726957514501063728771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46533817971676334042485847 69800726957514501063728771)
              ·
                refine ⟨104701090436271751595593157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69800726957514501063728771 104701090436271751595593157)
                ·
                  refine ⟨19631454456800953424173717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104701090436271751595593157 19631454456800953424173717)
                  ·
                    refine ⟨920224427662544691758143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19631454456800953424173717 920224427662544691758143)
                    ·
                      rfl

theorem cell23_5376392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_5376392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376392 prefixEnd_5376392 := by exact prefixLift 5376392
  have htrace : WordTrace (prefixWord ++ tailWord_5376392) baseStart_5376392 baseEnd_5376392 := by
    simpa [prefixWord, tailWord_5376392, baseEnd_5376392] using wordTrace_append hprefix tailTrace_5376392
  have hstable : (prefixWord ++ tailWord_5376392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376392).length < 2 ^ (prefixWord ++ tailWord_5376392).sum := by decide
  have hdescent : baseEnd_5376392 < baseStart_5376392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376393 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 3]
def baseStart_5376393 : Nat := 118140960795 + 5376393 * 2 ^ 59
def prefixEnd_5376393 : Nat := 4983230072969 + 3 ^ 40 * 5376393 * 2
def baseEnd_5376393 : Nat := 2760673796468288571361925

theorem tailTrace_5376393 : CollatzResearch.WordTrace tailWord_5376393 prefixEnd_5376393 2760673796468288571361925 := by
  unfold tailWord_5376393
  simp only [CollatzResearch.WordTrace]
  refine ⟨196093162411253850666693833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130728774940835900444462555 196093162411253850666693833)
  ·
    refine ⟨147069871808440388000020375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196093162411253850666693833 147069871808440388000020375)
    ·
      refine ⟨220604807712660582000030563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147069871808440388000020375 220604807712660582000030563)
      ·
        refine ⟨330907211568990873000045845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220604807712660582000030563 330907211568990873000045845)
        ·
          refine ⟨15511275542296447171877149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 330907211568990873000045845 15511275542296447171877149)
          ·
            refine ⟨5816728328361167689453931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15511275542296447171877149 5816728328361167689453931)
            ·
              refine ⟨8725092492541751534180897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5816728328361167689453931 8725092492541751534180897)
              ·
                refine ⟨6543819369406313650635673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8725092492541751534180897 6543819369406313650635673)
                ·
                  refine ⟨4907864527054735237976755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6543819369406313650635673 4907864527054735237976755)
                  ·
                    refine ⟨7361796790582102856965133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4907864527054735237976755 7361796790582102856965133)
                    ·
                      refine ⟨2760673796468288571361925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7361796790582102856965133 2760673796468288571361925)
                      ·
                        rfl

theorem cell23_5376393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_5376393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376393 prefixEnd_5376393 := by exact prefixLift 5376393
  have htrace : WordTrace (prefixWord ++ tailWord_5376393) baseStart_5376393 baseEnd_5376393 := by
    simpa [prefixWord, tailWord_5376393, baseEnd_5376393] using wordTrace_append hprefix tailTrace_5376393
  have hstable : (prefixWord ++ tailWord_5376393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376393).length < 2 ^ (prefixWord ++ tailWord_5376393).sum := by decide
  have hdescent : baseEnd_5376393 < baseStart_5376393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376416 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 1, 4, 2]
def baseStart_5376416 : Nat := 118140960795 + 5376416 * 2 ^ 59
def prefixEnd_5376416 : Nat := 4983230072969 + 3 ^ 40 * 5376416 * 2
def baseEnd_5376416 : Nat := 2760685606523341981374319

theorem tailTrace_5376416 : CollatzResearch.WordTrace tailWord_5376416 prefixEnd_5376416 2760685606523341981374319 := by
  unfold tailWord_5376416
  simp only [CollatzResearch.WordTrace]
  refine ⟨98047000645085262797390551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130729334193447017063187401 98047000645085262797390551)
  ·
    refine ⟨147070500967627894196085827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98047000645085262797390551 147070500967627894196085827)
    ·
      refine ⟨220605751451441841294128741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147070500967627894196085827 220605751451441841294128741)
      ·
        refine ⟨41363578397145345242649139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220605751451441841294128741 41363578397145345242649139)
        ·
          refine ⟨62045367595718017863973709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41363578397145345242649139 62045367595718017863973709)
          ·
            refine ⟨23267012848394256698990141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62045367595718017863973709 23267012848394256698990141)
            ·
              refine ⟨8725129818147846262121303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23267012848394256698990141 8725129818147846262121303)
              ·
                refine ⟨13087694727221769393181955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8725129818147846262121303 13087694727221769393181955)
                ·
                  refine ⟨19631542090832654089772933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13087694727221769393181955 19631542090832654089772933)
                  ·
                    refine ⟨3680914142031122641832425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19631542090832654089772933 3680914142031122641832425)
                    ·
                      refine ⟨2760685606523341981374319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680914142031122641832425 2760685606523341981374319)
                      ·
                        rfl

theorem cell23_5376416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_5376416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376416 prefixEnd_5376416 := by exact prefixLift 5376416
  have htrace : WordTrace (prefixWord ++ tailWord_5376416) baseStart_5376416 baseEnd_5376416 := by
    simpa [prefixWord, tailWord_5376416, baseEnd_5376416] using wordTrace_append hprefix tailTrace_5376416
  have hstable : (prefixWord ++ tailWord_5376416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376416).length < 2 ^ (prefixWord ++ tailWord_5376416).sum := by decide
  have hdescent : baseEnd_5376416 < baseStart_5376416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376459 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 2, 5, 2]
def baseStart_5376459 : Nat := 118140960795 + 5376459 * 2 ^ 59
def prefixEnd_5376459 : Nat := 4983230072969 + 3 ^ 40 * 5376459 * 2
def baseEnd_5376459 : Nat := 2760707686191485313136621

theorem tailTrace_5376459 : CollatzResearch.WordTrace tailWord_5376459 prefixEnd_5376459 2760707686191485313136621 := by
  unfold tailWord_5376459
  simp only [CollatzResearch.WordTrace]
  refine ⟨196095569629014743938596431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130730379752676495959064287 196095569629014743938596431)
  ·
    refine ⟨294143354443522115907894647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196095569629014743938596431 294143354443522115907894647)
    ·
      refine ⟨441215031665283173861841971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294143354443522115907894647 441215031665283173861841971)
      ·
        refine ⟨661822547497924760792762957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441215031665283173861841971 661822547497924760792762957)
        ·
          refine ⟨248183455311721785297286109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 661822547497924760792762957 248183455311721785297286109)
          ·
            refine ⟨93068795741895669486482291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248183455311721785297286109 93068795741895669486482291)
            ·
              refine ⟨139603193612843504229723437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93068795741895669486482291 139603193612843504229723437)
              ·
                refine ⟨52351197604816314086146289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139603193612843504229723437 52351197604816314086146289)
                ·
                  refine ⟨39263398203612235564609717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52351197604816314086146289 39263398203612235564609717)
                  ·
                    refine ⟨3680943581588647084182161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39263398203612235564609717 3680943581588647084182161)
                    ·
                      refine ⟨2760707686191485313136621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680943581588647084182161 2760707686191485313136621)
                      ·
                        rfl

theorem cell23_5376459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 5, 2].length) (baseStart_5376459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376459 prefixEnd_5376459 := by exact prefixLift 5376459
  have htrace : WordTrace (prefixWord ++ tailWord_5376459) baseStart_5376459 baseEnd_5376459 := by
    simpa [prefixWord, tailWord_5376459, baseEnd_5376459] using wordTrace_append hprefix tailTrace_5376459
  have hstable : (prefixWord ++ tailWord_5376459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376459).length < 2 ^ (prefixWord ++ tailWord_5376459).sum := by decide
  have hdescent : baseEnd_5376459 < baseStart_5376459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376489 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 6, 2]
def baseStart_5376489 : Nat := 118140960795 + 5376489 * 2 ^ 59
def prefixEnd_5376489 : Nat := 4983230072969 + 3 ^ 40 * 5376489 * 2
def baseEnd_5376489 : Nat := 2760723090611120195761483

theorem tailTrace_5376489 : CollatzResearch.WordTrace tailWord_5376489 prefixEnd_5376489 2760723090611120195761483 := by
  unfold tailWord_5376489
  simp only [CollatzResearch.WordTrace]
  refine ⟨196096663818906059062188521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130731109212604039374792347 196096663818906059062188521)
  ·
    refine ⟨147072497864179544296641391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196096663818906059062188521 147072497864179544296641391)
    ·
      refine ⟨220608746796269316444962087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147072497864179544296641391 220608746796269316444962087)
      ·
        refine ⟨330913120194403974667443131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220608746796269316444962087 330913120194403974667443131)
        ·
          refine ⟨496369680291605962001164697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330913120194403974667443131 496369680291605962001164697)
          ·
            refine ⟨372277260218704471500873523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496369680291605962001164697 372277260218704471500873523)
            ·
              refine ⟨558415890328056707251310285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372277260218704471500873523 558415890328056707251310285)
              ·
                refine ⟨209405958873021265219241357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558415890328056707251310285 209405958873021265219241357)
                ·
                  refine ⟨78527234577382974457215509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209405958873021265219241357 78527234577382974457215509)
                  ·
                    refine ⟨3680964120814826927681977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78527234577382974457215509 3680964120814826927681977)
                    ·
                      refine ⟨2760723090611120195761483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3680964120814826927681977 2760723090611120195761483)
                      ·
                        rfl

theorem cell23_5376489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 6, 2].length) (baseStart_5376489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376489 prefixEnd_5376489 := by exact prefixLift 5376489
  have htrace : WordTrace (prefixWord ++ tailWord_5376489) baseStart_5376489 baseEnd_5376489 := by
    simpa [prefixWord, tailWord_5376489, baseEnd_5376489] using wordTrace_append hprefix tailTrace_5376489
  have hstable : (prefixWord ++ tailWord_5376489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376489).length < 2 ^ (prefixWord ++ tailWord_5376489).sum := by decide
  have hdescent : baseEnd_5376489 < baseStart_5376489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376566 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5376566 : Nat := 118140960795 + 5376566 * 2 ^ 59
def prefixEnd_5376566 : Nat := 4983230072969 + 3 ^ 40 * 5376566 * 2
def baseEnd_5376566 : Nat := 2760762628621516394498629

theorem tailTrace_5376566 : CollatzResearch.WordTrace tailWord_5376566 prefixEnd_5376566 2760762628621516394498629 := by
  unfold tailWord_5376566
  simp only [CollatzResearch.WordTrace]
  refine ⟨12256217014976693825796347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130732981493084734141827701 12256217014976693825796347)
  ·
    refine ⟨18384325522465040738694521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12256217014976693825796347 18384325522465040738694521)
    ·
      refine ⟨13788244141848780554020891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18384325522465040738694521 13788244141848780554020891)
      ·
        refine ⟨20682366212773170831031337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13788244141848780554020891 20682366212773170831031337)
        ·
          refine ⟨15511774659579878123273503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20682366212773170831031337 15511774659579878123273503)
          ·
            refine ⟨23267661989369817184910255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15511774659579878123273503 23267661989369817184910255)
            ·
              refine ⟨34901492984054725777365383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23267661989369817184910255 34901492984054725777365383)
              ·
                refine ⟨52352239476082088666048075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34901492984054725777365383 52352239476082088666048075)
                ·
                  refine ⟨78528359214123132999072113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52352239476082088666048075 78528359214123132999072113)
                  ·
                    refine ⟨58896269410592349749304085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78528359214123132999072113 58896269410592349749304085)
                    ·
                      refine ⟨2760762628621516394498629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58896269410592349749304085 2760762628621516394498629)
                      ·
                        rfl

theorem cell23_5376566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5376566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376566 prefixEnd_5376566 := by exact prefixLift 5376566
  have htrace : WordTrace (prefixWord ++ tailWord_5376566) baseStart_5376566 baseEnd_5376566 := by
    simpa [prefixWord, tailWord_5376566, baseEnd_5376566] using wordTrace_append hprefix tailTrace_5376566
  have hstable : (prefixWord ++ tailWord_5376566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376566).length < 2 ^ (prefixWord ++ tailWord_5376566).sum := by decide
  have hdescent : baseEnd_5376566 < baseStart_5376566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376573 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_5376573 : Nat := 118140960795 + 5376573 * 2 ^ 59
def prefixEnd_5376573 : Nat := 4983230072969 + 3 ^ 40 * 5376573 * 2
def baseEnd_5376573 : Nat := 2760766222986097867111097

theorem tailTrace_5376573 : CollatzResearch.WordTrace tailWord_5376573 prefixEnd_5376573 2760766222986097867111097 := by
  unfold tailWord_5376573
  simp only [CollatzResearch.WordTrace]
  refine ⟨196099727550601741408246373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130733151700401160938830915 196099727550601741408246373)
  ·
    refine ⟨36768698915737826514046195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196099727550601741408246373 36768698915737826514046195)
    ·
      refine ⟨55153048373606739771069293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36768698915737826514046195 55153048373606739771069293)
      ·
        refine ⟨20682393140102527414150985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55153048373606739771069293 20682393140102527414150985)
        ·
          refine ⟨15511794855076895560613239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20682393140102527414150985 15511794855076895560613239)
          ·
            refine ⟨23267692282615343340919859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15511794855076895560613239 23267692282615343340919859)
            ·
              refine ⟨34901538423923015011379789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23267692282615343340919859 34901538423923015011379789)
              ·
                refine ⟨13088076908971130629267421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34901538423923015011379789 13088076908971130629267421)
                ·
                  refine ⟨4908028840864173985975283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13088076908971130629267421 4908028840864173985975283)
                  ·
                    refine ⟨7362043261296260978962925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4908028840864173985975283 7362043261296260978962925)
                    ·
                      refine ⟨2760766222986097867111097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7362043261296260978962925 2760766222986097867111097)
                      ·
                        rfl

theorem cell23_5376573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_5376573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376573 prefixEnd_5376573 := by exact prefixLift 5376573
  have htrace : WordTrace (prefixWord ++ tailWord_5376573) baseStart_5376573 baseEnd_5376573 := by
    simpa [prefixWord, tailWord_5376573, baseEnd_5376573] using wordTrace_append hprefix tailTrace_5376573
  have hstable : (prefixWord ++ tailWord_5376573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376573).length < 2 ^ (prefixWord ++ tailWord_5376573).sum := by decide
  have hdescent : baseEnd_5376573 < baseStart_5376573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376579 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 4]
def baseStart_5376579 : Nat := 118140960795 + 5376579 * 2 ^ 59
def prefixEnd_5376579 : Nat := 4983230072969 + 3 ^ 40 * 5376579 * 2
def baseEnd_5376579 : Nat := 2760769303870024843636069

theorem tailTrace_5376579 : CollatzResearch.WordTrace tailWord_5376579 prefixEnd_5376579 2760769303870024843636069 := by
  unfold tailWord_5376579
  simp only [CollatzResearch.WordTrace]
  refine ⟨196099946388580004432964791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130733297592386669621976527 196099946388580004432964791)
  ·
    refine ⟨294149919582870006649447187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196099946388580004432964791 294149919582870006649447187)
    ·
      refine ⟨441224879374305009974170781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294149919582870006649447187 441224879374305009974170781)
      ·
        refine ⟨165459329765364378740314043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441224879374305009974170781 165459329765364378740314043)
        ·
          refine ⟨248188994648046568110471065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165459329765364378740314043 248188994648046568110471065)
          ·
            refine ⟨186141745986034926082853299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248188994648046568110471065 186141745986034926082853299)
            ·
              refine ⟨279212618979052389124279949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186141745986034926082853299 279212618979052389124279949)
              ·
                refine ⟨104704732117144645921604981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279212618979052389124279949 104704732117144645921604981)
                ·
                  refine ⟨9816068635982310555150467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104704732117144645921604981 9816068635982310555150467)
                  ·
                    refine ⟨14724102953973465832725701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9816068635982310555150467 14724102953973465832725701)
                    ·
                      refine ⟨2760769303870024843636069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14724102953973465832725701 2760769303870024843636069)
                      ·
                        rfl

theorem cell23_5376579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_5376579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376579 prefixEnd_5376579 := by exact prefixLift 5376579
  have htrace : WordTrace (prefixWord ++ tailWord_5376579) baseStart_5376579 baseEnd_5376579 := by
    simpa [prefixWord, tailWord_5376579, baseEnd_5376579] using wordTrace_append hprefix tailTrace_5376579
  have hstable : (prefixWord ++ tailWord_5376579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376579).length < 2 ^ (prefixWord ++ tailWord_5376579).sum := by decide
  have hdescent : baseEnd_5376579 < baseStart_5376579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376599 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_5376599 : Nat := 118140960795 + 5376599 * 2 ^ 59
def prefixEnd_5376599 : Nat := 4983230072969 + 3 ^ 40 * 5376599 * 2
def baseEnd_5376599 : Nat := 2760779573483114765385977

theorem tailTrace_5376599 : CollatzResearch.WordTrace tailWord_5376599 prefixEnd_5376599 2760779573483114765385977 := by
  unfold tailWord_5376599
  simp only [CollatzResearch.WordTrace]
  refine ⟨196100675848507547848692851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130733783899005031899128567 196100675848507547848692851)
  ·
    refine ⟨294151013772761321773039277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196100675848507547848692851 294151013772761321773039277)
    ·
      refine ⟨110306630164785495664889729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294151013772761321773039277 110306630164785495664889729)
      ·
        refine ⟨82729972623589121748667297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110306630164785495664889729 82729972623589121748667297)
        ·
          refine ⟨62047479467691841311500473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82729972623589121748667297 62047479467691841311500473)
          ·
            refine ⟨46535609600768880983625355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62047479467691841311500473 46535609600768880983625355)
            ·
              refine ⟨69803414401153321475438033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46535609600768880983625355 69803414401153321475438033)
              ·
                refine ⟨52352560800864991106578525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69803414401153321475438033 52352560800864991106578525)
                ·
                  refine ⟨19632210300324371664966947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52352560800864991106578525 19632210300324371664966947)
                  ·
                    refine ⟨29448315450486557497450421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19632210300324371664966947 29448315450486557497450421)
                    ·
                      refine ⟨2760779573483114765385977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29448315450486557497450421 2760779573483114765385977)
                      ·
                        rfl

theorem cell23_5376599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_5376599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376599 prefixEnd_5376599 := by exact prefixLift 5376599
  have htrace : WordTrace (prefixWord ++ tailWord_5376599) baseStart_5376599 baseEnd_5376599 := by
    simpa [prefixWord, tailWord_5376599, baseEnd_5376599] using wordTrace_append hprefix tailTrace_5376599
  have hstable : (prefixWord ++ tailWord_5376599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376599).length < 2 ^ (prefixWord ++ tailWord_5376599).sum := by decide
  have hdescent : baseEnd_5376599 < baseStart_5376599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376640 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 2, 4]
def baseStart_5376640 : Nat := 118140960795 + 5376640 * 2 ^ 59
def prefixEnd_5376640 : Nat := 4983230072969 + 3 ^ 40 * 5376640 * 2
def baseEnd_5376640 : Nat := 920266875396649701657763

theorem tailTrace_5376640 : CollatzResearch.WordTrace tailWord_5376640 prefixEnd_5376640 920266875396649701657763 := by
  unfold tailWord_5376640
  simp only [CollatzResearch.WordTrace]
  refine ⟨98051085620679505925467687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130734780827572674567290249 98051085620679505925467687)
  ·
    refine ⟨147076628431019258888201531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98051085620679505925467687 147076628431019258888201531)
    ·
      refine ⟨220614942646528888332302297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147076628431019258888201531 220614942646528888332302297)
      ·
        refine ⟨165461206984896666249226723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220614942646528888332302297 165461206984896666249226723)
        ·
          refine ⟨248191810477344999373840085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165461206984896666249226723 248191810477344999373840085)
          ·
            refine ⟨5816995558062773422824377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248191810477344999373840085 5816995558062773422824377)
            ·
              refine ⟨4362746668547080067118283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5816995558062773422824377 4362746668547080067118283)
              ·
                refine ⟨6544120002820620100677425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4362746668547080067118283 6544120002820620100677425)
                ·
                  refine ⟨4908090002115465075508069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6544120002820620100677425 4908090002115465075508069)
                  ·
                    refine ⟨920266875396649701657763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4908090002115465075508069 920266875396649701657763)
                    ·
                      rfl

theorem cell23_5376640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 2, 4].length) (baseStart_5376640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376640 prefixEnd_5376640 := by exact prefixLift 5376640
  have htrace : WordTrace (prefixWord ++ tailWord_5376640) baseStart_5376640 baseEnd_5376640 := by
    simpa [prefixWord, tailWord_5376640, baseEnd_5376640] using wordTrace_append hprefix tailTrace_5376640
  have hstable : (prefixWord ++ tailWord_5376640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376640).length < 2 ^ (prefixWord ++ tailWord_5376640).sum := by decide
  have hdescent : baseEnd_5376640 < baseStart_5376640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376703 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 1, 4, 2]
def baseStart_5376703 : Nat := 118140960795 + 5376703 * 2 ^ 59
def prefixEnd_5376703 : Nat := 4983230072969 + 3 ^ 40 * 5376703 * 2
def baseEnd_5376703 : Nat := 2760832975471182358485499

theorem tailTrace_5376703 : CollatzResearch.WordTrace tailWord_5376703 prefixEnd_5376703 2760832975471182358485499 := by
  unfold tailWord_5376703
  simp only [CollatzResearch.WordTrace]
  refine ⟨196104469040130773610478763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130736312693420515740319175 196104469040130773610478763)
  ·
    refine ⟨294156703560196160415718145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196104469040130773610478763 294156703560196160415718145)
    ·
      refine ⟨220617527670147120311788609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294156703560196160415718145 220617527670147120311788609)
      ·
        refine ⟨165463145752610340233841457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220617527670147120311788609 165463145752610340233841457)
        ·
          refine ⟨124097359314457755175381093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165463145752610340233841457 124097359314457755175381093)
          ·
            refine ⟨23268254871460829095383955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124097359314457755175381093 23268254871460829095383955)
            ·
              refine ⟨34902382307191243643075933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23268254871460829095383955 34902382307191243643075933)
              ·
                refine ⟨13088393365196716366153475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34902382307191243643075933 13088393365196716366153475)
                ·
                  refine ⟨19632590047795074549230213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13088393365196716366153475 19632590047795074549230213)
                  ·
                    refine ⟨3681110633961576477980665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19632590047795074549230213 3681110633961576477980665)
                    ·
                      refine ⟨2760832975471182358485499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681110633961576477980665 2760832975471182358485499)
                      ·
                        rfl

theorem cell23_5376703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_5376703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376703 prefixEnd_5376703 := by exact prefixLift 5376703
  have htrace : WordTrace (prefixWord ++ tailWord_5376703) baseStart_5376703 baseEnd_5376703 := by
    simpa [prefixWord, tailWord_5376703, baseEnd_5376703] using wordTrace_append hprefix tailTrace_5376703
  have hstable : (prefixWord ++ tailWord_5376703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376703).length < 2 ^ (prefixWord ++ tailWord_5376703).sum := by decide
  have hdescent : baseEnd_5376703 < baseStart_5376703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376719 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_5376719 : Nat := 118140960795 + 5376719 * 2 ^ 59
def prefixEnd_5376719 : Nat := 4983230072969 + 3 ^ 40 * 5376719 * 2
def baseEnd_5376719 : Nat := 2760841191161654295885425

theorem tailTrace_5376719 : CollatzResearch.WordTrace tailWord_5376719 prefixEnd_5376719 2760841191161654295885425 := by
  unfold tailWord_5376719
  simp only [CollatzResearch.WordTrace]
  refine ⟨196105052608072808343061211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130736701738715205562040807 196105052608072808343061211)
  ·
    refine ⟨294157578912109212514591817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196105052608072808343061211 294157578912109212514591817)
    ·
      refine ⟨220618184184081909385943863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294157578912109212514591817 220618184184081909385943863)
      ·
        refine ⟨330927276276122864078915795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220618184184081909385943863 330927276276122864078915795)
        ·
          refine ⟨496390914414184296118373693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330927276276122864078915795 496390914414184296118373693)
          ·
            refine ⟨186146592905319111044390135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496390914414184296118373693 186146592905319111044390135)
            ·
              refine ⟨279219889357978666566585203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186146592905319111044390135 279219889357978666566585203)
              ·
                refine ⟨418829834036967999849877805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279219889357978666566585203 418829834036967999849877805)
                ·
                  refine ⟨157061187763862999943704177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 418829834036967999849877805 157061187763862999943704177)
                  ·
                    refine ⟨117795890822897249957778133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157061187763862999943704177 117795890822897249957778133)
                    ·
                      refine ⟨2760841191161654295885425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117795890822897249957778133 2760841191161654295885425)
                      ·
                        rfl

theorem cell23_5376719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_5376719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376719 prefixEnd_5376719 := by exact prefixLift 5376719
  have htrace : WordTrace (prefixWord ++ tailWord_5376719) baseStart_5376719 baseEnd_5376719 := by
    simpa [prefixWord, tailWord_5376719, baseEnd_5376719] using wordTrace_append hprefix tailTrace_5376719
  have hstable : (prefixWord ++ tailWord_5376719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376719).length < 2 ^ (prefixWord ++ tailWord_5376719).sum := by decide
  have hdescent : baseEnd_5376719 < baseStart_5376719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376737 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_5376737 : Nat := 118140960795 + 5376737 * 2 ^ 59
def prefixEnd_5376737 : Nat := 4983230072969 + 3 ^ 40 * 5376737 * 2
def baseEnd_5376737 : Nat := 2760850433813435225460343

theorem tailTrace_5376737 : CollatzResearch.WordTrace tailWord_5376737 prefixEnd_5376737 2760850433813435225460343 := by
  unfold tailWord_5376737
  simp only [CollatzResearch.WordTrace]
  refine ⟨196105709122007597417216465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130737139414671731611477643 196105709122007597417216465)
  ·
    refine ⟨147079281841505698062912349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196105709122007597417216465 147079281841505698062912349)
    ·
      refine ⟨55154730690564636773592131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147079281841505698062912349 55154730690564636773592131)
      ·
        refine ⟨82732096035846955160388197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55154730690564636773592131 82732096035846955160388197)
        ·
          refine ⟨15512268006721304092572787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82732096035846955160388197 15512268006721304092572787)
          ·
            refine ⟨23268402010081956138859181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15512268006721304092572787 23268402010081956138859181)
            ·
              refine ⟨8725650753780733552072193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23268402010081956138859181 8725650753780733552072193)
              ·
                refine ⟨6544238065335550164054145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8725650753780733552072193 6544238065335550164054145)
                ·
                  refine ⟨4908178549001662623040609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6544238065335550164054145 4908178549001662623040609)
                  ·
                    refine ⟨3681133911751246967280457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908178549001662623040609 3681133911751246967280457)
                    ·
                      refine ⟨2760850433813435225460343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681133911751246967280457 2760850433813435225460343)
                      ·
                        rfl

theorem cell23_5376737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_5376737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376737 prefixEnd_5376737 := by exact prefixLift 5376737
  have htrace : WordTrace (prefixWord ++ tailWord_5376737) baseStart_5376737 baseEnd_5376737 := by
    simpa [prefixWord, tailWord_5376737, baseEnd_5376737] using wordTrace_append hprefix tailTrace_5376737
  have hstable : (prefixWord ++ tailWord_5376737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376737).length < 2 ^ (prefixWord ++ tailWord_5376737).sum := by decide
  have hdescent : baseEnd_5376737 < baseStart_5376737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376754 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_5376754 : Nat := 118140960795 + 5376754 * 2 ^ 59
def prefixEnd_5376754 : Nat := 4983230072969 + 3 ^ 40 * 5376754 * 2
def baseEnd_5376754 : Nat := 2760859162984561658947765

theorem tailTrace_5376754 : CollatzResearch.WordTrace tailWord_5376754 prefixEnd_5376754 2760859162984561658947765 := by
  unfold tailWord_5376754
  simp only [CollatzResearch.WordTrace]
  refine ⟨49026582290736502330146329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130737552775297339547056877 49026582290736502330146329)
  ·
    refine ⟨36769936718052376747609747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49026582290736502330146329 36769936718052376747609747)
    ·
      refine ⟨55154905077078565121414621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36769936718052376747609747 55154905077078565121414621)
      ·
        refine ⟨20683089403904461920530483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55154905077078565121414621 20683089403904461920530483)
        ·
          refine ⟨31024634105856692880795725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20683089403904461920530483 31024634105856692880795725)
          ·
            refine ⟨11634237789696259830298397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31024634105856692880795725 11634237789696259830298397)
            ·
              refine ⟨4362839171136097436361899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11634237789696259830298397 4362839171136097436361899)
              ·
                refine ⟨6544258756704146154542849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4362839171136097436361899 6544258756704146154542849)
                ·
                  refine ⟨4908194067528109615907137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6544258756704146154542849 4908194067528109615907137)
                  ·
                    refine ⟨3681145550646082211930353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908194067528109615907137 3681145550646082211930353)
                    ·
                      refine ⟨2760859162984561658947765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681145550646082211930353 2760859162984561658947765)
                      ·
                        rfl

theorem cell23_5376754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_5376754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376754 prefixEnd_5376754 := by exact prefixLift 5376754
  have htrace : WordTrace (prefixWord ++ tailWord_5376754) baseStart_5376754 baseEnd_5376754 := by
    simpa [prefixWord, tailWord_5376754, baseEnd_5376754] using wordTrace_append hprefix tailTrace_5376754
  have hstable : (prefixWord ++ tailWord_5376754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376754).length < 2 ^ (prefixWord ++ tailWord_5376754).sum := by decide
  have hdescent : baseEnd_5376754 < baseStart_5376754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376793 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 2, 4, 2]
def baseStart_5376793 : Nat := 118140960795 + 5376793 * 2 ^ 59
def prefixEnd_5376793 : Nat := 4983230072969 + 3 ^ 40 * 5376793 * 2
def baseEnd_5376793 : Nat := 2760879188730087006360085

theorem tailTrace_5376793 : CollatzResearch.WordTrace tailWord_5376793 prefixEnd_5376793 2760879188730087006360085 := by
  unfold tailWord_5376793
  simp only [CollatzResearch.WordTrace]
  refine ⟨196107751609804718981255033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130738501073203145987503355 196107751609804718981255033)
  ·
    refine ⟨147080813707353539235941275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196107751609804718981255033 147080813707353539235941275)
    ·
      refine ⟨220621220561030308853911913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147080813707353539235941275 220621220561030308853911913)
      ·
        refine ⟨165465915420772731640433935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220621220561030308853911913 165465915420772731640433935)
        ·
          refine ⟨248198873131159097460650903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165465915420772731640433935 248198873131159097460650903)
          ·
            refine ⟨372298309696738646190976355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248198873131159097460650903 372298309696738646190976355)
            ·
              refine ⟨558447464545107969286464533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372298309696738646190976355 558447464545107969286464533)
              ·
                refine ⟨26177224900551936060303025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 558447464545107969286464533 26177224900551936060303025)
                ·
                  refine ⟨19632918675413952045227269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26177224900551936060303025 19632918675413952045227269)
                  ·
                    refine ⟨3681172251640116008480113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19632918675413952045227269 3681172251640116008480113)
                    ·
                      refine ⟨2760879188730087006360085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681172251640116008480113 2760879188730087006360085)
                      ·
                        rfl

theorem cell23_5376793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_5376793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376793 prefixEnd_5376793 := by exact prefixLift 5376793
  have htrace : WordTrace (prefixWord ++ tailWord_5376793) baseStart_5376793 baseEnd_5376793 := by
    simpa [prefixWord, tailWord_5376793, baseEnd_5376793] using wordTrace_append hprefix tailTrace_5376793
  have hstable : (prefixWord ++ tailWord_5376793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376793).length < 2 ^ (prefixWord ++ tailWord_5376793).sum := by decide
  have hdescent : baseEnd_5376793 < baseStart_5376793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376856 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5376856 : Nat := 118140960795 + 5376856 * 2 ^ 59
def prefixEnd_5376856 : Nat := 4983230072969 + 3 ^ 40 * 5376856 * 2
def baseEnd_5376856 : Nat := 2760911538011320259872295

theorem tailTrace_5376856 : CollatzResearch.WordTrace tailWord_5376856 prefixEnd_5376856 2760911538011320259872295 := by
  unfold tailWord_5376856
  simp only [CollatzResearch.WordTrace]
  refine ⟨98055024704288240370399211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130740032939050987160532281 98055024704288240370399211)
  ·
    refine ⟨147082537056432360555598817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98055024704288240370399211 147082537056432360555598817)
    ·
      refine ⟨110311902792324270416699113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147082537056432360555598817 110311902792324270416699113)
      ·
        refine ⟨82733927094243202812524335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110311902792324270416699113 82733927094243202812524335)
        ·
          refine ⟨124100890641364804218786503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82733927094243202812524335 124100890641364804218786503)
          ·
            refine ⟨186151335962047206328179755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124100890641364804218786503 186151335962047206328179755)
            ·
              refine ⟨279227003943070809492269633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186151335962047206328179755 279227003943070809492269633)
              ·
                refine ⟨209420252957303107119202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279227003943070809492269633 209420252957303107119202225)
                ·
                  refine ⟨157065189717977330339401669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209420252957303107119202225 157065189717977330339401669)
                  ·
                    refine ⟨29449723072120749438637813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157065189717977330339401669 29449723072120749438637813)
                    ·
                      refine ⟨2760911538011320259872295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29449723072120749438637813 2760911538011320259872295)
                      ·
                        rfl

theorem cell23_5376856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5376856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376856 prefixEnd_5376856 := by exact prefixLift 5376856
  have htrace : WordTrace (prefixWord ++ tailWord_5376856) baseStart_5376856 baseEnd_5376856 := by
    simpa [prefixWord, tailWord_5376856, baseEnd_5376856] using wordTrace_append hprefix tailTrace_5376856
  have hstable : (prefixWord ++ tailWord_5376856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376856).length < 2 ^ (prefixWord ++ tailWord_5376856).sum := by decide
  have hdescent : baseEnd_5376856 < baseStart_5376856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376883 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 4]
def baseStart_5376883 : Nat := 118140960795 + 5376883 * 2 ^ 59
def prefixEnd_5376883 : Nat := 4983230072969 + 3 ^ 40 * 5376883 * 2
def baseEnd_5376883 : Nat := 2760925401988991654234671

theorem tailTrace_5376883 : CollatzResearch.WordTrace tailWord_5376883 prefixEnd_5376883 2760925401988991654234671 := by
  unfold tailWord_5376883
  simp only [CollatzResearch.WordTrace]
  refine ⟨196111034179478664352031303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130740689452985776234687535 196111034179478664352031303)
  ·
    refine ⟨294166551269217996528046955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196111034179478664352031303 294166551269217996528046955)
    ·
      refine ⟨441249826903826994792070433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294166551269217996528046955 441249826903826994792070433)
      ·
        refine ⟨330937370177870246094052825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441249826903826994792070433 330937370177870246094052825)
        ·
          refine ⟨248203027633402684570539619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330937370177870246094052825 248203027633402684570539619)
          ·
            refine ⟨372304541450104026855809429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248203027633402684570539619 372304541450104026855809429)
            ·
              refine ⟨17451775380473626258866067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 372304541450104026855809429 17451775380473626258866067)
              ·
                refine ⟨26177663070710439388299101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17451775380473626258866067 26177663070710439388299101)
                ·
                  refine ⟨9816623651516414770612163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26177663070710439388299101 9816623651516414770612163)
                  ·
                    refine ⟨14724935477274622155918245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9816623651516414770612163 14724935477274622155918245)
                    ·
                      refine ⟨2760925401988991654234671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14724935477274622155918245 2760925401988991654234671)
                      ·
                        rfl

theorem cell23_5376883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_5376883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376883 prefixEnd_5376883 := by exact prefixLift 5376883
  have htrace : WordTrace (prefixWord ++ tailWord_5376883) baseStart_5376883 baseEnd_5376883 := by
    simpa [prefixWord, tailWord_5376883, baseEnd_5376883] using wordTrace_append hprefix tailTrace_5376883
  have hstable : (prefixWord ++ tailWord_5376883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376883).length < 2 ^ (prefixWord ++ tailWord_5376883).sum := by decide
  have hdescent : baseEnd_5376883 < baseStart_5376883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376893 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 1, 6]
def baseStart_5376893 : Nat := 118140960795 + 5376893 * 2 ^ 59
def prefixEnd_5376893 : Nat := 4983230072969 + 3 ^ 40 * 5376893 * 2
def baseEnd_5376893 : Nat := 920310178931845538369875

theorem tailTrace_5376893 : CollatzResearch.WordTrace tailWord_5376893 prefixEnd_5376893 920310178931845538369875 := by
  unfold tailWord_5376893
  simp only [CollatzResearch.WordTrace]
  refine ⟨196111398909442436059895333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130740932606294957373263555 196111398909442436059895333)
  ·
    refine ⟨36770887295520456761230375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196111398909442436059895333 36770887295520456761230375)
    ·
      refine ⟨55156330943280685141845563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36770887295520456761230375 55156330943280685141845563)
      ·
        refine ⟨82734496414921027712768345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55156330943280685141845563 82734496414921027712768345)
        ·
          refine ⟨62050872311190770784576259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82734496414921027712768345 62050872311190770784576259)
          ·
            refine ⟨93076308466786156176864389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62050872311190770784576259 93076308466786156176864389)
            ·
              refine ⟨17451807837522404283162073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93076308466786156176864389 17451807837522404283162073)
              ·
                refine ⟨13088855878141803212371555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17451807837522404283162073 13088855878141803212371555)
                ·
                  refine ⟨19633283817212704818557333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13088855878141803212371555 19633283817212704818557333)
                  ·
                    refine ⟨920310178931845538369875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19633283817212704818557333 920310178931845538369875)
                    ·
                      rfl

theorem cell23_5376893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_5376893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376893 prefixEnd_5376893 := by exact prefixLift 5376893
  have htrace : WordTrace (prefixWord ++ tailWord_5376893) baseStart_5376893 baseEnd_5376893 := by
    simpa [prefixWord, tailWord_5376893, baseEnd_5376893] using wordTrace_append hprefix tailTrace_5376893
  have hstable : (prefixWord ++ tailWord_5376893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376893).length < 2 ^ (prefixWord ++ tailWord_5376893).sum := by decide
  have hdescent : baseEnd_5376893 < baseStart_5376893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376917 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_5376917 : Nat := 118140960795 + 5376917 * 2 ^ 59
def prefixEnd_5376917 : Nat := 4983230072969 + 3 ^ 40 * 5376917 * 2
def baseEnd_5376917 : Nat := 2760942860331244521209515

theorem tailTrace_5376917 : CollatzResearch.WordTrace tailWord_5376917 prefixEnd_5376917 2760942860331244521209515 := by
  unfold tailWord_5376917
  simp only [CollatzResearch.WordTrace]
  refine ⟨196112274261355488158769005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130741516174236992105846003 196112274261355488158769005)
  ·
    refine ⟨73542102848008308059538377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196112274261355488158769005 73542102848008308059538377)
    ·
      refine ⟨55156577136006231044653783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73542102848008308059538377 55156577136006231044653783)
      ·
        refine ⟨82734865704009346566980675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55156577136006231044653783 82734865704009346566980675)
        ·
          refine ⟨124102298556014019850471013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82734865704009346566980675 124102298556014019850471013)
          ·
            refine ⟨23269180979252628721963315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124102298556014019850471013 23269180979252628721963315)
            ·
              refine ⟨34903771468878943082944973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23269180979252628721963315 34903771468878943082944973)
              ·
                refine ⟨13088914300829603656104365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34903771468878943082944973 13088914300829603656104365)
                ·
                  refine ⟨4908342862811101371039137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13088914300829603656104365 4908342862811101371039137)
                  ·
                    refine ⟨3681257147108326028279353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908342862811101371039137 3681257147108326028279353)
                    ·
                      refine ⟨2760942860331244521209515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681257147108326028279353 2760942860331244521209515)
                      ·
                        rfl

theorem cell23_5376917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_5376917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376917 prefixEnd_5376917 := by exact prefixLift 5376917
  have htrace : WordTrace (prefixWord ++ tailWord_5376917) baseStart_5376917 baseEnd_5376917 := by
    simpa [prefixWord, tailWord_5376917, baseEnd_5376917] using wordTrace_append hprefix tailTrace_5376917
  have hstable : (prefixWord ++ tailWord_5376917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376917).length < 2 ^ (prefixWord ++ tailWord_5376917).sum := by decide
  have hdescent : baseEnd_5376917 < baseStart_5376917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376930 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5376930 : Nat := 118140960795 + 5376930 * 2 ^ 59
def prefixEnd_5376930 : Nat := 4983230072969 + 3 ^ 40 * 5376930 * 2
def baseEnd_5376930 : Nat := 2760949535579752970346955

theorem tailTrace_5376930 : CollatzResearch.WordTrace tailWord_5376930 prefixEnd_5376930 2760949535579752970346955 := by
  unfold tailWord_5376930
  simp only [CollatzResearch.WordTrace]
  refine ⟨49028187102577097844748061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130741832273538927585994829 49028187102577097844748061)
  ·
    refine ⟨18385570163466411691780523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49028187102577097844748061 18385570163466411691780523)
    ·
      refine ⟨27578355245199617537670785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18385570163466411691780523 27578355245199617537670785)
      ·
        refine ⟨20683766433899713153253089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27578355245199617537670785 20683766433899713153253089)
        ·
          refine ⟨15512824825424784864939817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20683766433899713153253089 15512824825424784864939817)
          ·
            refine ⟨11634618619068588648704863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15512824825424784864939817 11634618619068588648704863)
            ·
              refine ⟨17451927928602882973057295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11634618619068588648704863 17451927928602882973057295)
              ·
                refine ⟨26177891892904324459585943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17451927928602882973057295 26177891892904324459585943)
                ·
                  refine ⟨39266837839356486689378915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26177891892904324459585943 39266837839356486689378915)
                  ·
                    refine ⟨58900256759034730034068373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39266837839356486689378915 58900256759034730034068373)
                    ·
                      refine ⟨2760949535579752970346955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58900256759034730034068373 2760949535579752970346955)
                      ·
                        rfl

theorem cell23_5376930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5376930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376930 prefixEnd_5376930 := by exact prefixLift 5376930
  have htrace : WordTrace (prefixWord ++ tailWord_5376930) baseStart_5376930 baseEnd_5376930 := by
    simpa [prefixWord, tailWord_5376930, baseEnd_5376930] using wordTrace_append hprefix tailTrace_5376930
  have hstable : (prefixWord ++ tailWord_5376930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376930).length < 2 ^ (prefixWord ++ tailWord_5376930).sum := by decide
  have hdescent : baseEnd_5376930 < baseStart_5376930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376968 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_5376968 : Nat := 118140960795 + 5376968 * 2 ^ 59
def prefixEnd_5376968 : Nat := 4983230072969 + 3 ^ 40 * 5376968 * 2
def baseEnd_5376968 : Nat := 2760969047844623821671781

theorem tailTrace_5376968 : CollatzResearch.WordTrace tailWord_5376968 prefixEnd_5376968 2760969047844623821671781 := by
  unfold tailWord_5376968
  simp only [CollatzResearch.WordTrace]
  refine ⟨98057067192085361934437779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130742756256113815912583705 98057067192085361934437779)
  ·
    refine ⟨147085600788128042901656669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98057067192085361934437779 147085600788128042901656669)
    ·
      refine ⟨55157100295548016088121251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147085600788128042901656669 55157100295548016088121251)
      ·
        refine ⟨82735650443322024132181877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55157100295548016088121251 82735650443322024132181877)
        ·
          refine ⟨7756467229061439762392051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82735650443322024132181877 7756467229061439762392051)
          ·
            refine ⟨11634700843592159643588077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7756467229061439762392051 11634700843592159643588077)
            ·
              refine ⟨4363012816347059866345529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11634700843592159643588077 4363012816347059866345529)
              ·
                refine ⟨3272259612260294899759147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4363012816347059866345529 3272259612260294899759147)
                ·
                  refine ⟨4908389418390442349638721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272259612260294899759147 4908389418390442349638721)
                  ·
                    refine ⟨3681292063792831762229041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908389418390442349638721 3681292063792831762229041)
                    ·
                      refine ⟨2760969047844623821671781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681292063792831762229041 2760969047844623821671781)
                      ·
                        rfl

theorem cell23_5376968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_5376968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376968 prefixEnd_5376968 := by exact prefixLift 5376968
  have htrace : WordTrace (prefixWord ++ tailWord_5376968) baseStart_5376968 baseEnd_5376968 := by
    simpa [prefixWord, tailWord_5376968, baseEnd_5376968] using wordTrace_append hprefix tailTrace_5376968
  have hstable : (prefixWord ++ tailWord_5376968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376968).length < 2 ^ (prefixWord ++ tailWord_5376968).sum := by decide
  have hdescent : baseEnd_5376968 < baseStart_5376968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5376984 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 2, 1, 3]
def baseStart_5376984 : Nat := 118140960795 + 5376984 * 2 ^ 59
def prefixEnd_5376984 : Nat := 4983230072969 + 3 ^ 40 * 5376984 * 2
def baseEnd_5376984 : Nat := 2760977263535095759071707

theorem tailTrace_5376984 : CollatzResearch.WordTrace tailWord_5376984 prefixEnd_5376984 2760977263535095759071707 := by
  unfold tailWord_5376984
  simp only [CollatzResearch.WordTrace]
  refine ⟨98057358976056379300729003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130743145301408505734305337 98057358976056379300729003)
  ·
    refine ⟨147086038464084568951093505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98057358976056379300729003 147086038464084568951093505)
    ·
      refine ⟨110314528848063426713320129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147086038464084568951093505 110314528848063426713320129)
      ·
        refine ⟨82735896636047570034990097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110314528848063426713320129 82735896636047570034990097)
        ·
          refine ⟨62051922477035677526242573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82735896636047570034990097 62051922477035677526242573)
          ·
            refine ⟨23269470928888379072340965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62051922477035677526242573 23269470928888379072340965)
            ·
              refine ⟨4363025799166571076063931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23269470928888379072340965 4363025799166571076063931)
              ·
                refine ⟨6544538698749856614095897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363025799166571076063931 6544538698749856614095897)
                ·
                  refine ⟨4908404024062392460571923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6544538698749856614095897 4908404024062392460571923)
                  ·
                    refine ⟨7362606036093588690857885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4908404024062392460571923 7362606036093588690857885)
                    ·
                      refine ⟨2760977263535095759071707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7362606036093588690857885 2760977263535095759071707)
                      ·
                        rfl

theorem cell23_5376984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_5376984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5376984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5376984 prefixEnd_5376984 := by exact prefixLift 5376984
  have htrace : WordTrace (prefixWord ++ tailWord_5376984) baseStart_5376984 baseEnd_5376984 := by
    simpa [prefixWord, tailWord_5376984, baseEnd_5376984] using wordTrace_append hprefix tailTrace_5376984
  have hstable : (prefixWord ++ tailWord_5376984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5376984).length < 2 ^ (prefixWord ++ tailWord_5376984).sum := by decide
  have hdescent : baseEnd_5376984 < baseStart_5376984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5376984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377003 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4]
def baseStart_5377003 : Nat := 118140960795 + 5377003 * 2 ^ 59
def prefixEnd_5377003 : Nat := 4983230072969 + 3 ^ 40 * 5377003 * 2
def baseEnd_5377003 : Nat := 2760987019667531184734119

theorem tailTrace_5377003 : CollatzResearch.WordTrace tailWord_5377003 prefixEnd_5377003 2760987019667531184734119 := by
  unfold tailWord_5377003
  simp only [CollatzResearch.WordTrace]
  refine ⟨196115410939043924846399663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130743607292695949897599775 196115410939043924846399663)
  ·
    refine ⟨294173116408565887269599495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196115410939043924846399663 294173116408565887269599495)
    ·
      refine ⟨441259674612848830904399243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294173116408565887269599495 441259674612848830904399243)
      ·
        refine ⟨661889511919273246356598865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441259674612848830904399243 661889511919273246356598865)
        ·
          refine ⟨496417133939454934767449149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661889511919273246356598865 496417133939454934767449149)
          ·
            refine ⟨186156425227295600537793431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496417133939454934767449149 186156425227295600537793431)
            ·
              refine ⟨279234637840943400806690147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186156425227295600537793431 279234637840943400806690147)
              ·
                refine ⟨418851956761415101210035221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279234637840943400806690147 418851956761415101210035221)
                ·
                  refine ⟨19633685473191332869220401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 418851956761415101210035221 19633685473191332869220401)
                  ·
                    refine ⟨14725264104893499651915301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19633685473191332869220401 14725264104893499651915301)
                    ·
                      refine ⟨2760987019667531184734119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14725264104893499651915301 2760987019667531184734119)
                      ·
                        rfl

theorem cell23_5377003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_5377003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377003 prefixEnd_5377003 := by exact prefixLift 5377003
  have htrace : WordTrace (prefixWord ++ tailWord_5377003) baseStart_5377003 baseEnd_5377003 := by
    simpa [prefixWord, tailWord_5377003, baseEnd_5377003] using wordTrace_append hprefix tailTrace_5377003
  have hstable : (prefixWord ++ tailWord_5377003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377003).length < 2 ^ (prefixWord ++ tailWord_5377003).sum := by decide
  have hdescent : baseEnd_5377003 < baseStart_5377003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377007 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 1, 4, 2]
def baseStart_5377007 : Nat := 118140960795 + 5377007 * 2 ^ 59
def prefixEnd_5377007 : Nat := 4983230072969 + 3 ^ 40 * 5377007 * 2
def baseEnd_5377007 : Nat := 2760989073590149169084101

theorem tailTrace_5377007 : CollatzResearch.WordTrace tailWord_5377007 prefixEnd_5377007 2760989073590149169084101 := by
  unfold tailWord_5377007
  simp only [CollatzResearch.WordTrace]
  refine ⟨196115556831029433529545275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130743704554019622353030183 196115556831029433529545275)
  ·
    refine ⟨294173335246544150294317913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196115556831029433529545275 294173335246544150294317913)
    ·
      refine ⟨220630001434908112720738435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294173335246544150294317913 220630001434908112720738435)
      ·
        refine ⟨330945002152362169081107653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220630001434908112720738435 330945002152362169081107653)
        ·
          refine ⟨62052187903567906702707685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330945002152362169081107653 62052187903567906702707685)
          ·
            refine ⟨11634785231918982506757691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62052187903567906702707685 11634785231918982506757691)
            ·
              refine ⟨17452177847878473760136537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11634785231918982506757691 17452177847878473760136537)
              ·
                refine ⟨13089133385908855320102403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17452177847878473760136537 13089133385908855320102403)
                ·
                  refine ⟨19633700078863282980153605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13089133385908855320102403 19633700078863282980153605)
                  ·
                    refine ⟨3681318764786865558778801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19633700078863282980153605 3681318764786865558778801)
                    ·
                      refine ⟨2760989073590149169084101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681318764786865558778801 2760989073590149169084101)
                      ·
                        rfl

theorem cell23_5377007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 4, 2].length) (baseStart_5377007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377007 prefixEnd_5377007 := by exact prefixLift 5377007
  have htrace : WordTrace (prefixWord ++ tailWord_5377007) baseStart_5377007 baseEnd_5377007 := by
    simpa [prefixWord, tailWord_5377007, baseEnd_5377007] using wordTrace_append hprefix tailTrace_5377007
  have hstable : (prefixWord ++ tailWord_5377007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377007).length < 2 ^ (prefixWord ++ tailWord_5377007).sum := by decide
  have hdescent : baseEnd_5377007 < baseStart_5377007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377043 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 1, 7]
def baseStart_5377043 : Nat := 118140960795 + 5377043 * 2 ^ 59
def prefixEnd_5377043 : Nat := 4983230072969 + 3 ^ 40 * 5377043 * 2
def baseEnd_5377043 : Nat := 920335852964570342744645

theorem tailTrace_5377043 : CollatzResearch.WordTrace tailWord_5377043 prefixEnd_5377043 920335852964570342744645 := by
  unfold tailWord_5377043
  simp only [CollatzResearch.WordTrace]
  refine ⟨196116869858899011677855783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130744579905932674451903855 196116869858899011677855783)
  ·
    refine ⟨294175304788348517516783675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196116869858899011677855783 294175304788348517516783675)
    ·
      refine ⟨441262957182522776275175513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294175304788348517516783675 441262957182522776275175513)
      ·
        refine ⟨330947217886892082206381635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441262957182522776275175513 330947217886892082206381635)
        ·
          refine ⟨496420826830338123309572453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330947217886892082206381635 496420826830338123309572453)
          ·
            refine ⟨93078905030688398120544835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 496420826830338123309572453 93078905030688398120544835)
            ·
              refine ⟨139618357546032597180817253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93078905030688398120544835 139618357546032597180817253)
              ·
                refine ⟨26178442039881111971403235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139618357546032597180817253 26178442039881111971403235)
                ·
                  refine ⟨39267663059821667957104853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26178442039881111971403235 39267663059821667957104853)
                  ·
                    refine ⟨920335852964570342744645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39267663059821667957104853 920335852964570342744645)
                    ·
                      rfl

theorem cell23_5377043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 7].length) (baseStart_5377043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377043 prefixEnd_5377043 := by exact prefixLift 5377043
  have htrace : WordTrace (prefixWord ++ tailWord_5377043) baseStart_5377043 baseEnd_5377043 := by
    simpa [prefixWord, tailWord_5377043, baseEnd_5377043] using wordTrace_append hprefix tailTrace_5377043
  have hstable : (prefixWord ++ tailWord_5377043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377043).length < 2 ^ (prefixWord ++ tailWord_5377043).sum := by decide
  have hdescent : baseEnd_5377043 < baseStart_5377043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377103 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 12]
def baseStart_5377103 : Nat := 118140960795 + 5377103 * 2 ^ 59
def prefixEnd_5377103 : Nat := 4983230072969 + 3 ^ 40 * 5377103 * 2
def baseEnd_5377103 : Nat := 306782040859220088164851

theorem tailTrace_5377103 : CollatzResearch.WordTrace tailWord_5377103 prefixEnd_5377103 306782040859220088164851 := by
  unfold tailWord_5377103
  simp only [CollatzResearch.WordTrace]
  refine ⟨196119058238681641925039963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130746038825787761283359975 196119058238681641925039963)
  ·
    refine ⟨294178587358022462887559945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196119058238681641925039963 294178587358022462887559945)
    ·
      refine ⟨220633940518516847165669959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294178587358022462887559945 220633940518516847165669959)
      ·
        refine ⟨330950910777775270748504939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220633940518516847165669959 330950910777775270748504939)
        ·
          refine ⟨496426366166662906122757409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330950910777775270748504939 496426366166662906122757409)
          ·
            refine ⟨372319774624997179592068057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496426366166662906122757409 372319774624997179592068057)
            ·
              refine ⟨279239830968747884694051043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372319774624997179592068057 279239830968747884694051043)
              ·
                refine ⟨418859746453121827041076565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279239830968747884694051043 418859746453121827041076565)
                ·
                  refine ⟨306782040859220088164851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 418859746453121827041076565 306782040859220088164851)
                  ·
                    rfl

theorem cell23_5377103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 12].length) (baseStart_5377103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377103 prefixEnd_5377103 := by exact prefixLift 5377103
  have htrace : WordTrace (prefixWord ++ tailWord_5377103) baseStart_5377103 baseEnd_5377103 := by
    simpa [prefixWord, tailWord_5377103, baseEnd_5377103] using wordTrace_append hprefix tailTrace_5377103
  have hstable : (prefixWord ++ tailWord_5377103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377103).length < 2 ^ (prefixWord ++ tailWord_5377103).sum := by decide
  have hdescent : baseEnd_5377103 < baseStart_5377103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377134 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_5377134 : Nat := 118140960795 + 5377134 * 2 ^ 59
def prefixEnd_5377134 : Nat := 4983230072969 + 3 ^ 40 * 5377134 * 2
def baseEnd_5377134 : Nat := 2761054285633270172196017

theorem tailTrace_5377134 : CollatzResearch.WordTrace tailWord_5377134 prefixEnd_5377134 2761054285633270172196017 := by
  unfold tailWord_5377134
  simp only [CollatzResearch.WordTrace]
  refine ⟨24515023612696166777427307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130746792601046222812945637 24515023612696166777427307)
  ·
    refine ⟨36772535419044250166140961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24515023612696166777427307 36772535419044250166140961)
    ·
      refine ⟨27579401564283187624605721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36772535419044250166140961 27579401564283187624605721)
      ·
        refine ⟨20684551173212390718454291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27579401564283187624605721 20684551173212390718454291)
        ·
          refine ⟨31026826759818586077681437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20684551173212390718454291 31026826759818586077681437)
          ·
            refine ⟨11635060034931969779130539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31026826759818586077681437 11635060034931969779130539)
            ·
              refine ⟨17452590052397954668695809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11635060034931969779130539 17452590052397954668695809)
              ·
                refine ⟨13089442539298466001521857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17452590052397954668695809 13089442539298466001521857)
                ·
                  refine ⟨9817081904473849501141393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13089442539298466001521857 9817081904473849501141393)
                  ·
                    refine ⟨7362811428355387125856045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9817081904473849501141393 7362811428355387125856045)
                    ·
                      refine ⟨2761054285633270172196017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7362811428355387125856045 2761054285633270172196017)
                      ·
                        rfl

theorem cell23_5377134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_5377134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377134 prefixEnd_5377134 := by exact prefixLift 5377134
  have htrace : WordTrace (prefixWord ++ tailWord_5377134) baseStart_5377134 baseEnd_5377134 := by
    simpa [prefixWord, tailWord_5377134, baseEnd_5377134] using wordTrace_append hprefix tailTrace_5377134
  have hstable : (prefixWord ++ tailWord_5377134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377134).length < 2 ^ (prefixWord ++ tailWord_5377134).sum := by decide
  have hdescent : baseEnd_5377134 < baseStart_5377134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377181 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_5377181 : Nat := 118140960795 + 5377181 * 2 ^ 59
def prefixEnd_5377181 : Nat := 4983230072969 + 3 ^ 40 * 5377181 * 2
def baseEnd_5377181 : Nat := 2761078419224031488308301

theorem tailTrace_5377181 : CollatzResearch.WordTrace tailWord_5377181 prefixEnd_5377181 2761078419224031488308301 := by
  unfold tailWord_5377181
  simp only [CollatzResearch.WordTrace]
  refine ⟨196121903132399061246379397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130747935421599374164252931 196121903132399061246379397)
  ·
    refine ⟨36772856837324823983696137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196121903132399061246379397 36772856837324823983696137)
    ·
      refine ⟨27579642627993617987772103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36772856837324823983696137 27579642627993617987772103)
      ·
        refine ⟨41369463941990426981658155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27579642627993617987772103 41369463941990426981658155)
        ·
          refine ⟨62054195912985640472487233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41369463941990426981658155 62054195912985640472487233)
          ·
            refine ⟨46540646934739230354365425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62054195912985640472487233 46540646934739230354365425)
            ·
              refine ⟨34905485201054422765774069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46540646934739230354365425 34905485201054422765774069)
              ·
                refine ⟨3272389237598852134291319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34905485201054422765774069 3272389237598852134291319)
                ·
                  refine ⟨4908583856398278201436979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272389237598852134291319 4908583856398278201436979)
                  ·
                    refine ⟨7362875784597417302155469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4908583856398278201436979 7362875784597417302155469)
                    ·
                      refine ⟨2761078419224031488308301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7362875784597417302155469 2761078419224031488308301)
                      ·
                        rfl

theorem cell23_5377181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_5377181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377181 prefixEnd_5377181 := by exact prefixLift 5377181
  have htrace : WordTrace (prefixWord ++ tailWord_5377181) baseStart_5377181 baseEnd_5377181 := by
    simpa [prefixWord, tailWord_5377181, baseEnd_5377181] using wordTrace_append hprefix tailTrace_5377181
  have hstable : (prefixWord ++ tailWord_5377181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377181).length < 2 ^ (prefixWord ++ tailWord_5377181).sum := by decide
  have hdescent : baseEnd_5377181 < baseStart_5377181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377184 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 1, 5]
def baseStart_5377184 : Nat := 118140960795 + 5377184 * 2 ^ 59
def prefixEnd_5377184 : Nat := 4983230072969 + 3 ^ 40 * 5377184 * 2
def baseEnd_5377184 : Nat := 920359986555331658856929

theorem tailTrace_5377184 : CollatzResearch.WordTrace tailWord_5377184 prefixEnd_5377184 920359986555331658856929 := by
  unfold tailWord_5377184
  simp only [CollatzResearch.WordTrace]
  refine ⟨98061006275694096379369303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130748008367592128505825737 98061006275694096379369303)
  ·
    refine ⟨147091509413541144569053955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98061006275694096379369303 147091509413541144569053955)
    ·
      refine ⟨220637264120311716853580933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147091509413541144569053955 220637264120311716853580933)
      ·
        refine ⟨41369487022558446910046425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220637264120311716853580933 41369487022558446910046425)
        ·
          refine ⟨31027115266918835182534819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41369487022558446910046425 31027115266918835182534819)
          ·
            refine ⟨46540672900378252773802229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31027115266918835182534819 46540672900378252773802229)
            ·
              refine ⟨4363188084410461197543959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46540672900378252773802229 4363188084410461197543959)
              ·
                refine ⟨6544782126615691796315939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363188084410461197543959 6544782126615691796315939)
                ·
                  refine ⟨9817173189923537694473909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6544782126615691796315939 9817173189923537694473909)
                  ·
                    refine ⟨920359986555331658856929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9817173189923537694473909 920359986555331658856929)
                    ·
                      rfl

theorem cell23_5377184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 1, 5].length) (baseStart_5377184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377184 prefixEnd_5377184 := by exact prefixLift 5377184
  have htrace : WordTrace (prefixWord ++ tailWord_5377184) baseStart_5377184 baseEnd_5377184 := by
    simpa [prefixWord, tailWord_5377184, baseEnd_5377184] using wordTrace_append hprefix tailTrace_5377184
  have hstable : (prefixWord ++ tailWord_5377184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377184).length < 2 ^ (prefixWord ++ tailWord_5377184).sum := by decide
  have hdescent : baseEnd_5377184 < baseStart_5377184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377187 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 4]
def baseStart_5377187 : Nat := 118140960795 + 5377187 * 2 ^ 59
def prefixEnd_5377187 : Nat := 4983230072969 + 3 ^ 40 * 5377187 * 2
def baseEnd_5377187 : Nat := 2761081500107958464833273

theorem tailTrace_5377187 : CollatzResearch.WordTrace tailWord_5377187 prefixEnd_5377187 2761081500107958464833273 := by
  unfold tailWord_5377187
  simp only [CollatzResearch.WordTrace]
  refine ⟨196122121970377324271097815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130748081313584882847398543 196122121970377324271097815)
  ·
    refine ⟨294183182955565986406646723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196122121970377324271097815 294183182955565986406646723)
    ·
      refine ⟨441274774433348979609970085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294183182955565986406646723 441274774433348979609970085)
      ·
        refine ⟨82739020206252933676869391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441274774433348979609970085 82739020206252933676869391)
        ·
          refine ⟨124108530309379400515304087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82739020206252933676869391 124108530309379400515304087)
          ·
            refine ⟨186162795464069100772956131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124108530309379400515304087 186162795464069100772956131)
            ·
              refine ⟨279244193196103651159434197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186162795464069100772956131 279244193196103651159434197)
              ·
                refine ⟨6544785778033679324049239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 279244193196103651159434197 6544785778033679324049239)
                ·
                  refine ⟨9817178667050518986073859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6544785778033679324049239 9817178667050518986073859)
                  ·
                    refine ⟨14725768000575778479110789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9817178667050518986073859 14725768000575778479110789)
                    ·
                      refine ⟨2761081500107958464833273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14725768000575778479110789 2761081500107958464833273)
                      ·
                        rfl

theorem cell23_5377187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_5377187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377187 prefixEnd_5377187 := by exact prefixLift 5377187
  have htrace : WordTrace (prefixWord ++ tailWord_5377187) baseStart_5377187 baseEnd_5377187 := by
    simpa [prefixWord, tailWord_5377187, baseEnd_5377187] using wordTrace_append hprefix tailTrace_5377187
  have hstable : (prefixWord ++ tailWord_5377187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377187).length < 2 ^ (prefixWord ++ tailWord_5377187).sum := by decide
  have hdescent : baseEnd_5377187 < baseStart_5377187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377191 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_5377191 : Nat := 118140960795 + 5377191 * 2 ^ 59
def prefixEnd_5377191 : Nat := 4983230072969 + 3 ^ 40 * 5377191 * 2
def baseEnd_5377191 : Nat := 2761083554030576449183255

theorem tailTrace_5377191 : CollatzResearch.WordTrace tailWord_5377191 prefixEnd_5377191 2761083554030576449183255 := by
  unfold tailWord_5377191
  simp only [CollatzResearch.WordTrace]
  refine ⟨196122267862362832954243427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130748178574908555302828951 196122267862362832954243427)
  ·
    refine ⟨294183401793544249431365141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196122267862362832954243427 294183401793544249431365141)
    ·
      refine ⟨13789846959072386692095241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 294183401793544249431365141 13789846959072386692095241)
      ·
        refine ⟨10342385219304290019071431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13789846959072386692095241 10342385219304290019071431)
        ·
          refine ⟨15513577828956435028607147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10342385219304290019071431 15513577828956435028607147)
          ·
            refine ⟨23270366743434652542910721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15513577828956435028607147 23270366743434652542910721)
            ·
              refine ⟨17452775057575989407183041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23270366743434652542910721 17452775057575989407183041)
              ·
                refine ⟨13089581293181992055387281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17452775057575989407183041 13089581293181992055387281)
                ·
                  refine ⟨9817185969886494041540461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13089581293181992055387281 9817185969886494041540461)
                  ·
                    refine ⟨3681444738707435265577673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9817185969886494041540461 3681444738707435265577673)
                    ·
                      refine ⟨2761083554030576449183255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681444738707435265577673 2761083554030576449183255)
                      ·
                        rfl

theorem cell23_5377191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_5377191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377191 prefixEnd_5377191 := by exact prefixLift 5377191
  have htrace : WordTrace (prefixWord ++ tailWord_5377191) baseStart_5377191 baseEnd_5377191 := by
    simpa [prefixWord, tailWord_5377191, baseEnd_5377191] using wordTrace_append hprefix tailTrace_5377191
  have hstable : (prefixWord ++ tailWord_5377191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377191).length < 2 ^ (prefixWord ++ tailWord_5377191).sum := by decide
  have hdescent : baseEnd_5377191 < baseStart_5377191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377207 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_5377207 : Nat := 118140960795 + 5377207 * 2 ^ 59
def prefixEnd_5377207 : Nat := 4983230072969 + 3 ^ 40 * 5377207 * 2
def baseEnd_5377207 : Nat := 2761091769721048386583181

theorem tailTrace_5377207 : CollatzResearch.WordTrace tailWord_5377207 prefixEnd_5377207 2761091769721048386583181 := by
  unfold tailWord_5377207
  simp only [CollatzResearch.WordTrace]
  refine ⟨196122851430304867686825875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130748567620203245124550583 196122851430304867686825875)
  ·
    refine ⟨294184277145457301530238813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196122851430304867686825875 294184277145457301530238813)
    ·
      refine ⟨110319103929546488073839555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294184277145457301530238813 110319103929546488073839555)
      ·
        refine ⟨165478655894319732110759333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110319103929546488073839555 165478655894319732110759333)
        ·
          refine ⟨31027247980184949770767375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165478655894319732110759333 31027247980184949770767375)
          ·
            refine ⟨46540871970277424656151063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31027247980184949770767375 46540871970277424656151063)
            ·
              refine ⟨69811307955416136984226595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46540871970277424656151063 69811307955416136984226595)
              ·
                refine ⟨104716961933124205476339893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69811307955416136984226595 104716961933124205476339893)
                ·
                  refine ⟨9817215181230394263406865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104716961933124205476339893 9817215181230394263406865)
                  ·
                    refine ⟨7362911385922795697555149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9817215181230394263406865 7362911385922795697555149)
                    ·
                      refine ⟨2761091769721048386583181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7362911385922795697555149 2761091769721048386583181)
                      ·
                        rfl

theorem cell23_5377207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_5377207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377207 prefixEnd_5377207 := by exact prefixLift 5377207
  have htrace : WordTrace (prefixWord ++ tailWord_5377207) baseStart_5377207 baseEnd_5377207 := by
    simpa [prefixWord, tailWord_5377207, baseEnd_5377207] using wordTrace_append hprefix tailTrace_5377207
  have hstable : (prefixWord ++ tailWord_5377207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377207).length < 2 ^ (prefixWord ++ tailWord_5377207).sum := by decide
  have hdescent : baseEnd_5377207 < baseStart_5377207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377214 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_5377214 : Nat := 118140960795 + 5377214 * 2 ^ 59
def prefixEnd_5377214 : Nat := 4983230072969 + 3 ^ 40 * 5377214 * 2
def baseEnd_5377214 : Nat := 920365121361876619731883

theorem tailTrace_5377214 : CollatzResearch.WordTrace tailWord_5377214 prefixEnd_5377214 920365121361876619731883 := by
  unfold tailWord_5377214
  simp only [CollatzResearch.WordTrace]
  refine ⟨24515388342659938485291337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130748737827519671921553797 24515388342659938485291337)
  ·
    refine ⟨18386541256994953863968503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24515388342659938485291337 18386541256994953863968503)
    ·
      refine ⟨27579811885492430795952755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18386541256994953863968503 27579811885492430795952755)
      ·
        refine ⟨41369717828238646193929133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27579811885492430795952755 41369717828238646193929133)
        ·
          refine ⟨15513644185589492322723425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41369717828238646193929133 15513644185589492322723425)
          ·
            refine ⟨11635233139192119242042569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15513644185589492322723425 11635233139192119242042569)
            ·
              refine ⟨8726424854394089431531927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11635233139192119242042569 8726424854394089431531927)
              ·
                refine ⟨13089637281591134147297891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8726424854394089431531927 13089637281591134147297891)
                ·
                  refine ⟨19634455922386701220946837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13089637281591134147297891 19634455922386701220946837)
                  ·
                    refine ⟨920365121361876619731883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19634455922386701220946837 920365121361876619731883)
                    ·
                      rfl

theorem cell23_5377214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_5377214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377214 prefixEnd_5377214 := by exact prefixLift 5377214
  have htrace : WordTrace (prefixWord ++ tailWord_5377214) baseStart_5377214 baseEnd_5377214 := by
    simpa [prefixWord, tailWord_5377214, baseEnd_5377214] using wordTrace_append hprefix tailTrace_5377214
  have hstable : (prefixWord ++ tailWord_5377214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377214).length < 2 ^ (prefixWord ++ tailWord_5377214).sum := by decide
  have hdescent : baseEnd_5377214 < baseStart_5377214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377238 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5377238 : Nat := 118140960795 + 5377238 * 2 ^ 59
def prefixEnd_5377238 : Nat := 4983230072969 + 3 ^ 40 * 5377238 * 2
def baseEnd_5377238 : Nat := 2761107687621337765295539

theorem tailTrace_5377238 : CollatzResearch.WordTrace tailWord_5377238 prefixEnd_5377238 2761107687621337765295539 := by
  unfold tailWord_5377238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257748880824534998825273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130749321395461706654136245 12257748880824534998825273)
  ·
    refine ⟨9193311660618401249118955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12257748880824534998825273 9193311660618401249118955)
    ·
      refine ⟨13789967490927601873678433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9193311660618401249118955 13789967490927601873678433)
      ·
        refine ⟨10342475618195701405258825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13789967490927601873678433 10342475618195701405258825)
        ·
          refine ⟨7756856713646776053944119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10342475618195701405258825 7756856713646776053944119)
          ·
            refine ⟨11635285070470164080916179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7756856713646776053944119 11635285070470164080916179)
            ·
              refine ⟨17452927605705246121374269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11635285070470164080916179 17452927605705246121374269)
              ·
                refine ⟨6544847852139467295515351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17452927605705246121374269 6544847852139467295515351)
                ·
                  refine ⟨9817271778209200943273027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6544847852139467295515351 9817271778209200943273027)
                  ·
                    refine ⟨14725907667313801414909541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9817271778209200943273027 14725907667313801414909541)
                    ·
                      refine ⟨2761107687621337765295539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14725907667313801414909541 2761107687621337765295539)
                      ·
                        rfl

theorem cell23_5377238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5377238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377238 prefixEnd_5377238 := by exact prefixLift 5377238
  have htrace : WordTrace (prefixWord ++ tailWord_5377238) baseStart_5377238 baseEnd_5377238 := by
    simpa [prefixWord, tailWord_5377238, baseEnd_5377238] using wordTrace_append hprefix tailTrace_5377238
  have hstable : (prefixWord ++ tailWord_5377238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377238).length < 2 ^ (prefixWord ++ tailWord_5377238).sum := by decide
  have hdescent : baseEnd_5377238 < baseStart_5377238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377268 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5377268 : Nat := 118140960795 + 5377268 * 2 ^ 59
def prefixEnd_5377268 : Nat := 4983230072969 + 3 ^ 40 * 5377268 * 2
def baseEnd_5377268 : Nat := 2761123092040972647920401

theorem tailTrace_5377268 : CollatzResearch.WordTrace tailWord_5377268 prefixEnd_5377268 2761123092040972647920401 := by
  unfold tailWord_5377268
  simp only [CollatzResearch.WordTrace]
  refine ⟨98062538141541937552398229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130750050855389250069864305 98062538141541937552398229)
  ·
    refine ⟨4596681475384778322768667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98062538141541937552398229 4596681475384778322768667)
    ·
      refine ⟨6895022213077167484153001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596681475384778322768667 6895022213077167484153001)
      ·
        refine ⟨5171266659807875613114751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6895022213077167484153001 5171266659807875613114751)
        ·
          refine ⟨7756899989711813419672127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5171266659807875613114751 7756899989711813419672127)
          ·
            refine ⟨11635349984567720129508191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7756899989711813419672127 11635349984567720129508191)
            ·
              refine ⟨17453024976851580194262287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11635349984567720129508191 17453024976851580194262287)
              ·
                refine ⟨26179537465277370291393431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17453024976851580194262287 26179537465277370291393431)
                ·
                  refine ⟨39269306197916055437090147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26179537465277370291393431 39269306197916055437090147)
                  ·
                    refine ⟨58903959296874083155635221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39269306197916055437090147 58903959296874083155635221)
                    ·
                      refine ⟨2761123092040972647920401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58903959296874083155635221 2761123092040972647920401)
                      ·
                        rfl

theorem cell23_5377268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5377268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377268 prefixEnd_5377268 := by exact prefixLift 5377268
  have htrace : WordTrace (prefixWord ++ tailWord_5377268) baseStart_5377268 baseEnd_5377268 := by
    simpa [prefixWord, tailWord_5377268, baseEnd_5377268] using wordTrace_append hprefix tailTrace_5377268
  have hstable : (prefixWord ++ tailWord_5377268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377268).length < 2 ^ (prefixWord ++ tailWord_5377268).sum := by decide
  have hdescent : baseEnd_5377268 < baseStart_5377268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377281 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_5377281 : Nat := 118140960795 + 5377281 * 2 ^ 59
def prefixEnd_5377281 : Nat := 4983230072969 + 3 ^ 40 * 5377281 * 2
def baseEnd_5377281 : Nat := 2761129767289481097057841

theorem tailTrace_5377281 : CollatzResearch.WordTrace tailWord_5377281 prefixEnd_5377281 2761129767289481097057841 := by
  unfold tailWord_5377281
  simp only [CollatzResearch.WordTrace]
  refine ⟨196125550432036778325019697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130750366954691185550013131 196125550432036778325019697)
  ·
    refine ⟨147094162824027583743764773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196125550432036778325019697 147094162824027583743764773)
    ·
      refine ⟨27580155529505171951955895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147094162824027583743764773 27580155529505171951955895)
      ·
        refine ⟨41370233294257757927933843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27580155529505171951955895 41370233294257757927933843)
        ·
          refine ⟨62055349941386636891900765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41370233294257757927933843 62055349941386636891900765)
          ·
            refine ⟨23270756228019988834462787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62055349941386636891900765 23270756228019988834462787)
            ·
              refine ⟨34906134342029983251694181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23270756228019988834462787 34906134342029983251694181)
              ·
                refine ⟨6544900189130621859692659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34906134342029983251694181 6544900189130621859692659)
                ·
                  refine ⟨9817350283695932789538989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6544900189130621859692659 9817350283695932789538989)
                  ·
                    refine ⟨3681506356385974796077121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9817350283695932789538989 3681506356385974796077121)
                    ·
                      refine ⟨2761129767289481097057841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681506356385974796077121 2761129767289481097057841)
                      ·
                        rfl

theorem cell23_5377281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_5377281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377281 prefixEnd_5377281 := by exact prefixLift 5377281
  have htrace : WordTrace (prefixWord ++ tailWord_5377281) baseStart_5377281 baseEnd_5377281 := by
    simpa [prefixWord, tailWord_5377281, baseEnd_5377281] using wordTrace_append hprefix tailTrace_5377281
  have hstable : (prefixWord ++ tailWord_5377281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377281).length < 2 ^ (prefixWord ++ tailWord_5377281).sum := by decide
  have hdescent : baseEnd_5377281 < baseStart_5377281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377297 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_5377297 : Nat := 118140960795 + 5377297 * 2 ^ 59
def prefixEnd_5377297 : Nat := 4983230072969 + 3 ^ 40 * 5377297 * 2
def baseEnd_5377297 : Nat := 2761137982979953034457767

theorem tailTrace_5377297 : CollatzResearch.WordTrace tailWord_5377297 prefixEnd_5377297 2761137982979953034457767 := by
  unfold tailWord_5377297
  simp only [CollatzResearch.WordTrace]
  refine ⟨196126133999978813057602145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130750755999985875371734763 196126133999978813057602145)
  ·
    refine ⟨147094600499984109793201609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196126133999978813057602145 147094600499984109793201609)
    ·
      refine ⟨110320950374988082344901207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147094600499984109793201609 110320950374988082344901207)
      ·
        refine ⟨165481425562482123517351811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110320950374988082344901207 165481425562482123517351811)
        ·
          refine ⟨248222138343723185276027717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165481425562482123517351811 248222138343723185276027717)
          ·
            refine ⟨46541650939448097239255197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248222138343723185276027717 46541650939448097239255197)
            ·
              refine ⟨17453119102293036464720699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46541650939448097239255197 17453119102293036464720699)
              ·
                refine ⟨26179678653439554697081049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17453119102293036464720699 26179678653439554697081049)
                ·
                  refine ⟨19634758990079666022810787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26179678653439554697081049 19634758990079666022810787)
                  ·
                    refine ⟨29452138485119499034216181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19634758990079666022810787 29452138485119499034216181)
                    ·
                      refine ⟨2761137982979953034457767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29452138485119499034216181 2761137982979953034457767)
                      ·
                        rfl

theorem cell23_5377297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_5377297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377297 prefixEnd_5377297 := by exact prefixLift 5377297
  have htrace : WordTrace (prefixWord ++ tailWord_5377297) baseStart_5377297 baseEnd_5377297 := by
    simpa [prefixWord, tailWord_5377297, baseEnd_5377297] using wordTrace_append hprefix tailTrace_5377297
  have hstable : (prefixWord ++ tailWord_5377297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377297).length < 2 ^ (prefixWord ++ tailWord_5377297).sum := by decide
  have hdescent : baseEnd_5377297 < baseStart_5377297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377327 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_5377327 : Nat := 118140960795 + 5377327 * 2 ^ 59
def prefixEnd_5377327 : Nat := 4983230072969 + 3 ^ 40 * 5377327 * 2
def baseEnd_5377327 : Nat := 2761153387399587917082629

theorem tailTrace_5377327 : CollatzResearch.WordTrace tailWord_5377327 prefixEnd_5377327 2761153387399587917082629 := by
  unfold tailWord_5377327
  simp only [CollatzResearch.WordTrace]
  refine ⟨196127228189870128181194235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130751485459913418787462823 196127228189870128181194235)
  ·
    refine ⟨294190842284805192271791353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196127228189870128181194235 294190842284805192271791353)
    ·
      refine ⟨220643131713603894203843515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294190842284805192271791353 220643131713603894203843515)
      ·
        refine ⟨330964697570405841305765273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220643131713603894203843515 330964697570405841305765273)
        ·
          refine ⟨248223523177804380979323955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330964697570405841305765273 248223523177804380979323955)
          ·
            refine ⟨372335284766706571468985933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248223523177804380979323955 372335284766706571468985933)
            ·
              refine ⟨139625731787514964300869725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372335284766706571468985933 139625731787514964300869725)
              ·
                refine ⟨52359649420318111612826147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139625731787514964300869725 52359649420318111612826147)
                ·
                  refine ⟨78539474130477167419239221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52359649420318111612826147 78539474130477167419239221)
                  ·
                    refine ⟨7363075699732234445553677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78539474130477167419239221 7363075699732234445553677)
                    ·
                      refine ⟨2761153387399587917082629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7363075699732234445553677 2761153387399587917082629)
                      ·
                        rfl

theorem cell23_5377327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_5377327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377327 prefixEnd_5377327 := by exact prefixLift 5377327
  have htrace : WordTrace (prefixWord ++ tailWord_5377327) baseStart_5377327 baseEnd_5377327 := by
    simpa [prefixWord, tailWord_5377327, baseEnd_5377327] using wordTrace_append hprefix tailTrace_5377327
  have hstable : (prefixWord ++ tailWord_5377327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377327).length < 2 ^ (prefixWord ++ tailWord_5377327).sum := by decide
  have hdescent : baseEnd_5377327 < baseStart_5377327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377354 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_5377354 : Nat := 118140960795 + 5377354 * 2 ^ 59
def prefixEnd_5377354 : Nat := 4983230072969 + 3 ^ 40 * 5377354 * 2
def baseEnd_5377354 : Nat := 2761167251377259311445005

theorem tailTrace_5377354 : CollatzResearch.WordTrace tailWord_5377354 prefixEnd_5377354 2761167251377259311445005 := by
  unfold tailWord_5377354
  simp only [CollatzResearch.WordTrace]
  refine ⟨49032053240193077948106779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130752141973848207861618077 49032053240193077948106779)
  ·
    refine ⟨73548079860289616922160169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49032053240193077948106779 73548079860289616922160169)
    ·
      refine ⟨55161059895217212691620127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73548079860289616922160169 55161059895217212691620127)
      ·
        refine ⟨82741589842825819037430191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55161059895217212691620127 82741589842825819037430191)
        ·
          refine ⟨124112384764238728556145287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82741589842825819037430191 124112384764238728556145287)
          ·
            refine ⟨186168577146358092834217931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124112384764238728556145287 186168577146358092834217931)
            ·
              refine ⟨279252865719537139251326897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186168577146358092834217931 279252865719537139251326897)
              ·
                refine ⟨209439649289652854438495173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279252865719537139251326897 209439649289652854438495173)
                ·
                  refine ⟨39269934241809910207217845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209439649289652854438495173 39269934241809910207217845)
                  ·
                    refine ⟨3681556335169679081926673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39269934241809910207217845 3681556335169679081926673)
                    ·
                      refine ⟨2761167251377259311445005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681556335169679081926673 2761167251377259311445005)
                      ·
                        rfl

theorem cell23_5377354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_5377354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377354 prefixEnd_5377354 := by exact prefixLift 5377354
  have htrace : WordTrace (prefixWord ++ tailWord_5377354) baseStart_5377354 baseEnd_5377354 := by
    simpa [prefixWord, tailWord_5377354, baseEnd_5377354] using wordTrace_append hprefix tailTrace_5377354
  have hstable : (prefixWord ++ tailWord_5377354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377354).length < 2 ^ (prefixWord ++ tailWord_5377354).sum := by decide
  have hdescent : baseEnd_5377354 < baseStart_5377354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377364 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_5377364 : Nat := 118140960795 + 5377364 * 2 ^ 59
def prefixEnd_5377364 : Nat := 4983230072969 + 3 ^ 40 * 5377364 * 2
def baseEnd_5377364 : Nat := 920390795394601424106653

theorem tailTrace_5377364 : CollatzResearch.WordTrace tailWord_5377364 prefixEnd_5377364 920390795394601424106653 := by
  unfold tailWord_5377364
  simp only [CollatzResearch.WordTrace]
  refine ⟨98064288845368041750145573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130752385127157389000194097 98064288845368041750145573)
  ·
    refine ⟨18387054158506507828152295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98064288845368041750145573 18387054158506507828152295)
    ·
      refine ⟨27580581237759761742228443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18387054158506507828152295 27580581237759761742228443)
      ·
        refine ⟨41370871856639642613342665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27580581237759761742228443 41370871856639642613342665)
        ·
          refine ⟨31028153892479731960006999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41370871856639642613342665 31028153892479731960006999)
          ·
            refine ⟨46542230838719597940010499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31028153892479731960006999 46542230838719597940010499)
            ·
              refine ⟨69813346258079396910015749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46542230838719597940010499 69813346258079396910015749)
              ·
                refine ⟨13090002423389886920627953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69813346258079396910015749 13090002423389886920627953)
                ·
                  refine ⟨9817501817542415190470965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13090002423389886920627953 9817501817542415190470965)
                  ·
                    refine ⟨920390795394601424106653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9817501817542415190470965 920390795394601424106653)
                    ·
                      rfl

theorem cell23_5377364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_5377364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377364 prefixEnd_5377364 := by exact prefixLift 5377364
  have htrace : WordTrace (prefixWord ++ tailWord_5377364) baseStart_5377364 baseEnd_5377364 := by
    simpa [prefixWord, tailWord_5377364, baseEnd_5377364] using wordTrace_append hprefix tailTrace_5377364
  have hstable : (prefixWord ++ tailWord_5377364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377364).length < 2 ^ (prefixWord ++ tailWord_5377364).sum := by decide
  have hdescent : baseEnd_5377364 < baseStart_5377364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377404 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_5377404 : Nat := 118140960795 + 5377404 * 2 ^ 59
def prefixEnd_5377404 : Nat := 4983230072969 + 3 ^ 40 * 5377404 * 2
def baseEnd_5377404 : Nat := 2761192925409984115819775

theorem tailTrace_5377404 : CollatzResearch.WordTrace tailWord_5377404 prefixEnd_5377404 2761192925409984115819775 := by
  unfold tailWord_5377404
  simp only [CollatzResearch.WordTrace]
  refine ⟨98065018305295585165873633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130753357740394113554498177 98065018305295585165873633)
  ·
    refine ⟨73548763728971688874405225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98065018305295585165873633 73548763728971688874405225)
    ·
      refine ⟨55161572796728766655803919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73548763728971688874405225 55161572796728766655803919)
      ·
        refine ⟨82742359195093149983705879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55161572796728766655803919 82742359195093149983705879)
        ·
          refine ⟨124113538792639724975558819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82742359195093149983705879 124113538792639724975558819)
          ·
            refine ⟨186170308188959587463338229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124113538792639724975558819 186170308188959587463338229)
            ·
              refine ⟨17453466392714961324687959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186170308188959587463338229 17453466392714961324687959)
              ·
                refine ⟨26180199589072441987031939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17453466392714961324687959 26180199589072441987031939)
                ·
                  refine ⟨39270299383608662980547909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26180199589072441987031939 39270299383608662980547909)
                  ·
                    refine ⟨7363181134426624308852733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39270299383608662980547909 7363181134426624308852733)
                    ·
                      refine ⟨2761192925409984115819775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7363181134426624308852733 2761192925409984115819775)
                      ·
                        rfl

theorem cell23_5377404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_5377404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377404 prefixEnd_5377404 := by exact prefixLift 5377404
  have htrace : WordTrace (prefixWord ++ tailWord_5377404) baseStart_5377404 baseEnd_5377404 := by
    simpa [prefixWord, tailWord_5377404, baseEnd_5377404] using wordTrace_append hprefix tailTrace_5377404
  have hstable : (prefixWord ++ tailWord_5377404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377404).length < 2 ^ (prefixWord ++ tailWord_5377404).sum := by decide
  have hdescent : baseEnd_5377404 < baseStart_5377404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377428 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5377428 : Nat := 118140960795 + 5377428 * 2 ^ 59
def prefixEnd_5377428 : Nat := 4983230072969 + 3 ^ 40 * 5377428 * 2
def baseEnd_5377428 : Nat := 920401749648564007306555

theorem tailTrace_5377428 : CollatzResearch.WordTrace tailWord_5377428 prefixEnd_5377428 920401749648564007306555 := by
  unfold tailWord_5377428
  simp only [CollatzResearch.WordTrace]
  refine ⟨98065455981252111215310469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130753941308336148287080625 98065455981252111215310469)
  ·
    refine ⟨18387272996484770852870713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98065455981252111215310469 18387272996484770852870713)
    ·
      refine ⟨13790454747363578139653035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18387272996484770852870713 13790454747363578139653035)
      ·
        refine ⟨20685682121045367209479553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13790454747363578139653035 20685682121045367209479553)
        ·
          refine ⟨15514261590784025407109665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20685682121045367209479553 15514261590784025407109665)
          ·
            refine ⟨11635696193088019055332249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15514261590784025407109665 11635696193088019055332249)
            ·
              refine ⟨8726772144816014291499187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11635696193088019055332249 8726772144816014291499187)
              ·
                refine ⟨13090158217224021437248781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8726772144816014291499187 13090158217224021437248781)
                ·
                  refine ⟨4908809331459008038968293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13090158217224021437248781 4908809331459008038968293)
                  ·
                    refine ⟨920401749648564007306555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4908809331459008038968293 920401749648564007306555)
                    ·
                      rfl

theorem cell23_5377428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5377428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377428 prefixEnd_5377428 := by exact prefixLift 5377428
  have htrace : WordTrace (prefixWord ++ tailWord_5377428) baseStart_5377428 baseEnd_5377428 := by
    simpa [prefixWord, tailWord_5377428, baseEnd_5377428] using wordTrace_append hprefix tailTrace_5377428
  have hstable : (prefixWord ++ tailWord_5377428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377428).length < 2 ^ (prefixWord ++ tailWord_5377428).sum := by decide
  have hdescent : baseEnd_5377428 < baseStart_5377428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377508 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_5377508 : Nat := 118140960795 + 5377508 * 2 ^ 59
def prefixEnd_5377508 : Nat := 4983230072969 + 3 ^ 40 * 5377508 * 2
def baseEnd_5377508 : Nat := 2761246327398051708919297

theorem tailTrace_5377508 : CollatzResearch.WordTrace tailWord_5377508 prefixEnd_5377508 2761246327398051708919297 := by
  unfold tailWord_5377508
  simp only [CollatzResearch.WordTrace]
  refine ⟨98066914901107198046766589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130755886534809597395688785 98066914901107198046766589)
  ·
    refine ⟨36775093087915199267537471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98066914901107198046766589 36775093087915199267537471)
    ·
      refine ⟨55162639631872798901306207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36775093087915199267537471 55162639631872798901306207)
      ·
        refine ⟨82743959447809198351959311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55162639631872798901306207 82743959447809198351959311)
        ·
          refine ⟨124115939171713797527938967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82743959447809198351959311 124115939171713797527938967)
          ·
            refine ⟨186173908757570696291908451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124115939171713797527938967 186173908757570696291908451)
            ·
              refine ⟨279260863136356044437862677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186173908757570696291908451 279260863136356044437862677)
              ·
                refine ⟨13090352959516689583024813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279260863136356044437862677 13090352959516689583024813)
                ·
                  refine ⟨4908882359818758593634305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13090352959516689583024813 4908882359818758593634305)
                  ·
                    refine ⟨3681661769864068945225729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4908882359818758593634305 3681661769864068945225729)
                    ·
                      refine ⟨2761246327398051708919297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681661769864068945225729 2761246327398051708919297)
                      ·
                        rfl

theorem cell23_5377508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_5377508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377508 prefixEnd_5377508 := by exact prefixLift 5377508
  have htrace : WordTrace (prefixWord ++ tailWord_5377508) baseStart_5377508 baseEnd_5377508 := by
    simpa [prefixWord, tailWord_5377508, baseEnd_5377508] using wordTrace_append hprefix tailTrace_5377508
  have hstable : (prefixWord ++ tailWord_5377508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377508).length < 2 ^ (prefixWord ++ tailWord_5377508).sum := by decide
  have hdescent : baseEnd_5377508 < baseStart_5377508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377521 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_5377521 : Nat := 118140960795 + 5377521 * 2 ^ 59
def prefixEnd_5377521 : Nat := 4983230072969 + 3 ^ 40 * 5377521 * 2
def baseEnd_5377521 : Nat := 2761253002646560158056737

theorem tailTrace_5377521 : CollatzResearch.WordTrace tailWord_5377521 prefixEnd_5377521 2761253002646560158056737 := by
  unfold tailWord_5377521
  simp only [CollatzResearch.WordTrace]
  refine ⟨196134303951167299313756417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130756202634111532875837611 196134303951167299313756417)
  ·
    refine ⟨147100727963375474485317313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196134303951167299313756417 147100727963375474485317313)
    ·
      refine ⟨110325545972531605863987985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147100727963375474485317313 110325545972531605863987985)
      ·
        refine ⟨82744159479398704397990989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110325545972531605863987985 82744159479398704397990989)
        ·
          refine ⟨31029059804774514149246621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82744159479398704397990989 31029059804774514149246621)
          ·
            refine ⟨11635897426790442805967483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31029059804774514149246621 11635897426790442805967483)
            ·
              refine ⟨17453846140185664208951225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11635897426790442805967483 17453846140185664208951225)
              ·
                refine ⟨13090384605139248156713419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17453846140185664208951225 13090384605139248156713419)
                ·
                  refine ⟨19635576907708872235070129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13090384605139248156713419 19635576907708872235070129)
                  ·
                    refine ⟨14726682680781654176302597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19635576907708872235070129 14726682680781654176302597)
                    ·
                      refine ⟨2761253002646560158056737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14726682680781654176302597 2761253002646560158056737)
                      ·
                        rfl

theorem cell23_5377521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_5377521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377521 prefixEnd_5377521 := by exact prefixLift 5377521
  have htrace : WordTrace (prefixWord ++ tailWord_5377521) baseStart_5377521 baseEnd_5377521 := by
    simpa [prefixWord, tailWord_5377521, baseEnd_5377521] using wordTrace_append hprefix tailTrace_5377521
  have hstable : (prefixWord ++ tailWord_5377521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377521).length < 2 ^ (prefixWord ++ tailWord_5377521).sum := by decide
  have hdescent : baseEnd_5377521 < baseStart_5377521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377544 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_5377544 : Nat := 118140960795 + 5377544 * 2 ^ 59
def prefixEnd_5377544 : Nat := 4983230072969 + 3 ^ 40 * 5377544 * 2
def baseEnd_5377544 : Nat := 920421604233871189356377

theorem tailTrace_5377544 : CollatzResearch.WordTrace tailWord_5377544 prefixEnd_5377544 920421604233871189356377 := by
  unfold tailWord_5377544
  simp only [CollatzResearch.WordTrace]
  refine ⟨98067571415041987120921843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130756761886722649494562457 98067571415041987120921843)
  ·
    refine ⟨147101357122562980681382765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98067571415041987120921843 147101357122562980681382765)
    ·
      refine ⟨55163008920961117755518537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147101357122562980681382765 55163008920961117755518537)
      ·
        refine ⟨41372256690720838316638903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55163008920961117755518537 41372256690720838316638903)
        ·
          refine ⟨62058385036081257474958355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41372256690720838316638903 62058385036081257474958355)
          ·
            refine ⟨93087577554121886212437533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62058385036081257474958355 93087577554121886212437533)
            ·
              refine ⟨34907841582795707329664075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93087577554121886212437533 34907841582795707329664075)
              ·
                refine ⟨52361762374193560994496113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34907841582795707329664075 52361762374193560994496113)
                ·
                  refine ⟨39271321780645170745872085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52361762374193560994496113 39271321780645170745872085)
                  ·
                    refine ⟨920421604233871189356377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39271321780645170745872085 920421604233871189356377)
                    ·
                      rfl

theorem cell23_5377544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_5377544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377544 prefixEnd_5377544 := by exact prefixLift 5377544
  have htrace : WordTrace (prefixWord ++ tailWord_5377544) baseStart_5377544 baseEnd_5377544 := by
    simpa [prefixWord, tailWord_5377544, baseEnd_5377544] using wordTrace_append hprefix tailTrace_5377544
  have hstable : (prefixWord ++ tailWord_5377544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377544).length < 2 ^ (prefixWord ++ tailWord_5377544).sum := by decide
  have hdescent : baseEnd_5377544 < baseStart_5377544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377548 : List Nat := [2, 2, 1, 2, 6, 1, 1, 8]
def baseStart_5377548 : Nat := 118140960795 + 5377548 * 2 ^ 59
def prefixEnd_5377548 : Nat := 4983230072969 + 3 ^ 40 * 5377548 * 2
def baseEnd_5377548 : Nat := 102269143208304872311819

theorem tailTrace_5377548 : CollatzResearch.WordTrace tailWord_5377548 prefixEnd_5377548 102269143208304872311819 := by
  unfold tailWord_5377548
  simp only [CollatzResearch.WordTrace]
  refine ⟨98067644361034741462494649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130756859148046321949992865 98067644361034741462494649)
  ·
    refine ⟨73550733270776056096870987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98067644361034741462494649 73550733270776056096870987)
    ·
      refine ⟨110326099906164084145306481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73550733270776056096870987 110326099906164084145306481)
      ·
        refine ⟨82744574929623063108979861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110326099906164084145306481 82744574929623063108979861)
        ·
          refine ⟨3878651949826081083233431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82744574929623063108979861 3878651949826081083233431)
          ·
            refine ⟨5817977924739121624850147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878651949826081083233431 5817977924739121624850147)
            ·
              refine ⟨8726966887108682437275221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5817977924739121624850147 8726966887108682437275221)
              ·
                refine ⟨102269143208304872311819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8726966887108682437275221 102269143208304872311819)
                ·
                  rfl

theorem cell23_5377548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 8].length) (baseStart_5377548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377548 prefixEnd_5377548 := by exact prefixLift 5377548
  have htrace : WordTrace (prefixWord ++ tailWord_5377548) baseStart_5377548 baseEnd_5377548 := by
    simpa [prefixWord, tailWord_5377548, baseEnd_5377548] using wordTrace_append hprefix tailTrace_5377548
  have hstable : (prefixWord ++ tailWord_5377548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377548).length < 2 ^ (prefixWord ++ tailWord_5377548).sum := by decide
  have hdescent : baseEnd_5377548 < baseStart_5377548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377584 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_5377584 : Nat := 118140960795 + 5377584 * 2 ^ 59
def prefixEnd_5377584 : Nat := 4983230072969 + 3 ^ 40 * 5377584 * 2
def baseEnd_5377584 : Nat := 2761285351927793411568947

theorem tailTrace_5377584 : CollatzResearch.WordTrace tailWord_5377584 prefixEnd_5377584 2761285351927793411568947 := by
  unfold tailWord_5377584
  simp only [CollatzResearch.WordTrace]
  refine ⟨98068300874969530536649903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130757734499959374048866537 98068300874969530536649903)
  ·
    refine ⟨147102451312454295804974855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98068300874969530536649903 147102451312454295804974855)
    ·
      refine ⟨220653676968681443707462283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147102451312454295804974855 220653676968681443707462283)
      ·
        refine ⟨330980515453022165561193425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220653676968681443707462283 330980515453022165561193425)
        ·
          refine ⟨248235386589766624170895069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330980515453022165561193425 248235386589766624170895069)
          ·
            refine ⟨93088269971162484064085651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248235386589766624170895069 93088269971162484064085651)
            ·
              refine ⟨139632404956743726096128477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93088269971162484064085651 139632404956743726096128477)
              ·
                refine ⟨52362151858778897286048179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139632404956743726096128477 52362151858778897286048179)
                ·
                  refine ⟨78543227788168345929072269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52362151858778897286048179 78543227788168345929072269)
                  ·
                    refine ⟨29453710420563129723402101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78543227788168345929072269 29453710420563129723402101)
                    ·
                      refine ⟨2761285351927793411568947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29453710420563129723402101 2761285351927793411568947)
                      ·
                        rfl

theorem cell23_5377584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_5377584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377584 prefixEnd_5377584 := by exact prefixLift 5377584
  have htrace : WordTrace (prefixWord ++ tailWord_5377584) baseStart_5377584 baseEnd_5377584 := by
    simpa [prefixWord, tailWord_5377584, baseEnd_5377584] using wordTrace_append hprefix tailTrace_5377584
  have hstable : (prefixWord ++ tailWord_5377584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377584).length < 2 ^ (prefixWord ++ tailWord_5377584).sum := by decide
  have hdescent : baseEnd_5377584 < baseStart_5377584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377661 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_5377661 : Nat := 118140960795 + 5377661 * 2 ^ 59
def prefixEnd_5377661 : Nat := 4983230072969 + 3 ^ 40 * 5377661 * 2
def baseEnd_5377661 : Nat := 2761324889938189610306093

theorem tailTrace_5377661 : CollatzResearch.WordTrace tailWord_5377661 prefixEnd_5377661 2761324889938189610306093 := by
  unfold tailWord_5377661
  simp only [CollatzResearch.WordTrace]
  refine ⟨196139410170660103223852837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130759606780440068815901891 196139410170660103223852837)
  ·
    refine ⟨36776139406998769354472407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196139410170660103223852837 36776139406998769354472407)
    ·
      refine ⟨55164209110498154031708611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36776139406998769354472407 55164209110498154031708611)
      ·
        refine ⟨82746313665747231047562917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55164209110498154031708611 82746313665747231047562917)
        ·
          refine ⟨15514933812327605821418047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82746313665747231047562917 15514933812327605821418047)
          ·
            refine ⟨23272400718491408732127071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15514933812327605821418047 23272400718491408732127071)
            ·
              refine ⟨34908601077737113098190607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23272400718491408732127071 34908601077737113098190607)
              ·
                refine ⟨52362901616605669647285911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34908601077737113098190607 52362901616605669647285911)
                ·
                  refine ⟨78544352424908504470928867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52362901616605669647285911 78544352424908504470928867)
                  ·
                    refine ⟨117816528637362756706393301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78544352424908504470928867 117816528637362756706393301)
                    ·
                      refine ⟨2761324889938189610306093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117816528637362756706393301 2761324889938189610306093)
                      ·
                        rfl

theorem cell23_5377661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_5377661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377661 prefixEnd_5377661 := by exact prefixLift 5377661
  have htrace : WordTrace (prefixWord ++ tailWord_5377661) baseStart_5377661 baseEnd_5377661 := by
    simpa [prefixWord, tailWord_5377661, baseEnd_5377661] using wordTrace_append hprefix tailTrace_5377661
  have hstable : (prefixWord ++ tailWord_5377661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377661).length < 2 ^ (prefixWord ++ tailWord_5377661).sum := by decide
  have hdescent : baseEnd_5377661 < baseStart_5377661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377688 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5377688 : Nat := 118140960795 + 5377688 * 2 ^ 59
def prefixEnd_5377688 : Nat := 4983230072969 + 3 ^ 40 * 5377688 * 2
def baseEnd_5377688 : Nat := 2761338753915861004668469

theorem tailTrace_5377688 : CollatzResearch.WordTrace tailWord_5377688 prefixEnd_5377688 2761338753915861004668469 := by
  unfold tailWord_5377688
  simp only [CollatzResearch.WordTrace]
  refine ⟨98070197470781143417542859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130760263294374857890057145 98070197470781143417542859)
  ·
    refine ⟨147105296206171715126314289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98070197470781143417542859 147105296206171715126314289)
    ·
      refine ⟨110328972154628786344735717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147105296206171715126314289 110328972154628786344735717)
      ·
        refine ⟨20686682278992897439637947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110328972154628786344735717 20686682278992897439637947)
        ·
          refine ⟨31030023418489346159456921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20686682278992897439637947 31030023418489346159456921)
          ·
            refine ⟨23272517563867009619592691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31030023418489346159456921 23272517563867009619592691)
            ·
              refine ⟨34908776345800514429389037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23272517563867009619592691 34908776345800514429389037)
              ·
                refine ⟨13090791129675192911020889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34908776345800514429389037 13090791129675192911020889)
                ·
                  refine ⟨9818093347256394683265667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13090791129675192911020889 9818093347256394683265667)
                  ·
                    refine ⟨14727140020884592024898501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9818093347256394683265667 14727140020884592024898501)
                    ·
                      refine ⟨2761338753915861004668469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14727140020884592024898501 2761338753915861004668469)
                      ·
                        rfl

theorem cell23_5377688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5377688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377688 prefixEnd_5377688 := by exact prefixLift 5377688
  have htrace : WordTrace (prefixWord ++ tailWord_5377688) baseStart_5377688 baseEnd_5377688 := by
    simpa [prefixWord, tailWord_5377688, baseEnd_5377688] using wordTrace_append hprefix tailTrace_5377688
  have hstable : (prefixWord ++ tailWord_5377688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377688).length < 2 ^ (prefixWord ++ tailWord_5377688).sum := by decide
  have hdescent : baseEnd_5377688 < baseStart_5377688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377715 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 1, 4]
def baseStart_5377715 : Nat := 118140960795 + 5377715 * 2 ^ 59
def prefixEnd_5377715 : Nat := 4983230072969 + 3 ^ 40 * 5377715 * 2
def baseEnd_5377715 : Nat := 920450872631177466343615

theorem tailTrace_5377715 : CollatzResearch.WordTrace tailWord_5377715 prefixEnd_5377715 920450872631177466343615 := by
  unfold tailWord_5377715
  simp only [CollatzResearch.WordTrace]
  refine ⟨196141379712464470446318599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130760919808309646964212399 196141379712464470446318599)
  ·
    refine ⟨294212069568696705669477899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196141379712464470446318599 294212069568696705669477899)
    ·
      refine ⟨441318104353045058504216849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294212069568696705669477899 441318104353045058504216849)
      ·
        refine ⟨330988578264783793878162637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441318104353045058504216849 330988578264783793878162637)
        ·
          refine ⟨124120716849293922704310989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330988578264783793878162637 124120716849293922704310989)
          ·
            refine ⟨46545268818485221014116621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124120716849293922704310989 46545268818485221014116621)
            ·
              refine ⟨17454475806931957880293733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46545268818485221014116621 17454475806931957880293733)
              ·
                refine ⟨3272714213799742102555075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17454475806931957880293733 3272714213799742102555075)
                ·
                  refine ⟨4909071320699613153832613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272714213799742102555075 4909071320699613153832613)
                  ·
                    refine ⟨920450872631177466343615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909071320699613153832613 920450872631177466343615)
                    ·
                      rfl

theorem cell23_5377715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 1, 4].length) (baseStart_5377715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377715 prefixEnd_5377715 := by exact prefixLift 5377715
  have htrace : WordTrace (prefixWord ++ tailWord_5377715) baseStart_5377715 baseEnd_5377715 := by
    simpa [prefixWord, tailWord_5377715, baseEnd_5377715] using wordTrace_append hprefix tailTrace_5377715
  have hstable : (prefixWord ++ tailWord_5377715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377715).length < 2 ^ (prefixWord ++ tailWord_5377715).sum := by decide
  have hdescent : baseEnd_5377715 < baseStart_5377715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377765 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5377765 : Nat := 118140960795 + 5377765 * 2 ^ 59
def prefixEnd_5377765 : Nat := 4983230072969 + 3 ^ 40 * 5377765 * 2
def baseEnd_5377765 : Nat := 2761378291926257203405615

theorem tailTrace_5377765 : CollatzResearch.WordTrace tailWord_5377765 prefixEnd_5377765 2761378291926257203405615 := by
  unfold tailWord_5377765
  simp only [CollatzResearch.WordTrace]
  refine ⟨196143203362283328985638749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130762135574855552657092499 196143203362283328985638749)
  ·
    refine ⟨73553701260856248369614531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196143203362283328985638749 73553701260856248369614531)
    ·
      refine ⟨110330551891284372554421797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73553701260856248369614531 110330551891284372554421797)
      ·
        refine ⟨20686978479615819853954087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110330551891284372554421797 20686978479615819853954087)
        ·
          refine ⟨31030467719423729780931131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20686978479615819853954087 31030467719423729780931131)
          ·
            refine ⟨46545701579135594671396697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31030467719423729780931131 46545701579135594671396697)
            ·
              refine ⟨34909276184351696003547523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46545701579135594671396697 34909276184351696003547523)
              ·
                refine ⟨52363914276527544005321285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34909276184351696003547523 52363914276527544005321285)
                ·
                  refine ⟨9818233926848914500997741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52363914276527544005321285 9818233926848914500997741)
                  ·
                    refine ⟨3681837722568342937874153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9818233926848914500997741 3681837722568342937874153)
                    ·
                      refine ⟨2761378291926257203405615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681837722568342937874153 2761378291926257203405615)
                      ·
                        rfl

theorem cell23_5377765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5377765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377765 prefixEnd_5377765 := by exact prefixLift 5377765
  have htrace : WordTrace (prefixWord ++ tailWord_5377765) baseStart_5377765 baseEnd_5377765 := by
    simpa [prefixWord, tailWord_5377765, baseEnd_5377765] using wordTrace_append hprefix tailTrace_5377765
  have hstable : (prefixWord ++ tailWord_5377765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377765).length < 2 ^ (prefixWord ++ tailWord_5377765).sum := by decide
  have hdescent : baseEnd_5377765 < baseStart_5377765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377771 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 3, 6]
def baseStart_5377771 : Nat := 118140960795 + 5377771 * 2 ^ 59
def prefixEnd_5377771 : Nat := 4983230072969 + 3 ^ 40 * 5377771 * 2
def baseEnd_5377771 : Nat := 920460457603394726643529

theorem tailTrace_5377771 : CollatzResearch.WordTrace tailWord_5377771 prefixEnd_5377771 920460457603394726643529 := by
  unfold tailWord_5377771
  simp only [CollatzResearch.WordTrace]
  refine ⟨196143422200261592010357167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130762281466841061340238111 196143422200261592010357167)
  ·
    refine ⟨294215133300392388015535751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196143422200261592010357167 294215133300392388015535751)
    ·
      refine ⟨441322699950588582023303627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294215133300392388015535751 441322699950588582023303627)
      ·
        refine ⟨661984049925882873034955441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441322699950588582023303627 661984049925882873034955441)
        ·
          refine ⟨496488037444412154776216581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661984049925882873034955441 496488037444412154776216581)
          ·
            refine ⟨93091507020827279020540609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 496488037444412154776216581 93091507020827279020540609)
            ·
              refine ⟨69818630265620459265405457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93091507020827279020540609 69818630265620459265405457)
              ·
                refine ⟨52363972699215344449054093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69818630265620459265405457 52363972699215344449054093)
                ·
                  refine ⟨19636489762205754168395285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52363972699215344449054093 19636489762205754168395285)
                  ·
                    refine ⟨920460457603394726643529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19636489762205754168395285 920460457603394726643529)
                    ·
                      rfl

theorem cell23_5377771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_5377771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377771 prefixEnd_5377771 := by exact prefixLift 5377771
  have htrace : WordTrace (prefixWord ++ tailWord_5377771) baseStart_5377771 baseEnd_5377771 := by
    simpa [prefixWord, tailWord_5377771, baseEnd_5377771] using wordTrace_append hprefix tailTrace_5377771
  have hstable : (prefixWord ++ tailWord_5377771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377771).length < 2 ^ (prefixWord ++ tailWord_5377771).sum := by decide
  have hdescent : baseEnd_5377771 < baseStart_5377771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377772 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 1, 1, 3]
def baseStart_5377772 : Nat := 118140960795 + 5377772 * 2 ^ 59
def prefixEnd_5377772 : Nat := 4983230072969 + 3 ^ 40 * 5377772 * 2
def baseEnd_5377772 : Nat := 2761381886290838676018083

theorem tailTrace_5377772 : CollatzResearch.WordTrace tailWord_5377772 prefixEnd_5377772 2761381886290838676018083 := by
  unfold tailWord_5377772
  simp only [CollatzResearch.WordTrace]
  refine ⟨98071729336628984590571785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130762305782171979454095713 98071729336628984590571785)
  ·
    refine ⟨73553797002471738442928839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98071729336628984590571785 73553797002471738442928839)
    ·
      refine ⟨110330695503707607664393259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73553797002471738442928839 110330695503707607664393259)
      ·
        refine ⟨165496043255561411496589889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110330695503707607664393259 165496043255561411496589889)
        ·
          refine ⟨124122032441671058622442417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165496043255561411496589889 124122032441671058622442417)
          ·
            refine ⟨93091524331253293966831813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124122032441671058622442417 93091524331253293966831813)
            ·
              refine ⟨17454660812109992618780965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93091524331253293966831813 17454660812109992618780965)
              ·
                refine ⟨3272748902270623616021431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17454660812109992618780965 3272748902270623616021431)
                ·
                  refine ⟨4909123353405935424032147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3272748902270623616021431 4909123353405935424032147)
                  ·
                    refine ⟨7363685030108903136048221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4909123353405935424032147 7363685030108903136048221)
                    ·
                      refine ⟨2761381886290838676018083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7363685030108903136048221 2761381886290838676018083)
                      ·
                        rfl

theorem cell23_5377772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_5377772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377772 prefixEnd_5377772 := by exact prefixLift 5377772
  have htrace : WordTrace (prefixWord ++ tailWord_5377772) baseStart_5377772 baseEnd_5377772 := by
    simpa [prefixWord, tailWord_5377772, baseEnd_5377772] using wordTrace_append hprefix tailTrace_5377772
  have hstable : (prefixWord ++ tailWord_5377772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377772).length < 2 ^ (prefixWord ++ tailWord_5377772).sum := by decide
  have hdescent : baseEnd_5377772 < baseStart_5377772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377815 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_5377815 : Nat := 118140960795 + 5377815 * 2 ^ 59
def prefixEnd_5377815 : Nat := 4983230072969 + 3 ^ 40 * 5377815 * 2
def baseEnd_5377815 : Nat := 2761403965958982007780385

theorem tailTrace_5377815 : CollatzResearch.WordTrace tailWord_5377815 prefixEnd_5377815 2761403965958982007780385 := by
  unfold tailWord_5377815
  simp only [CollatzResearch.WordTrace]
  refine ⟨196145027012102187524958899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130763351341401458349972599 196145027012102187524958899)
  ·
    refine ⟨294217540518153281287438349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196145027012102187524958899 294217540518153281287438349)
    ·
      refine ⟨110331577694307480482789381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294217540518153281287438349 110331577694307480482789381)
      ·
        refine ⟨20687170817682652590523009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110331577694307480482789381 20687170817682652590523009)
        ·
          refine ⟨15515378113261989442892257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20687170817682652590523009 15515378113261989442892257)
          ·
            refine ⟨11636533584946492082169193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15515378113261989442892257 11636533584946492082169193)
            ·
              refine ⟨8727400188709869061626895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11636533584946492082169193 8727400188709869061626895)
              ·
                refine ⟨13091100283064803592440343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8727400188709869061626895 13091100283064803592440343)
                ·
                  refine ⟨19636650424597205388660515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13091100283064803592440343 19636650424597205388660515)
                  ·
                    refine ⟨29454975636895808082990773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19636650424597205388660515 29454975636895808082990773)
                    ·
                      refine ⟨2761403965958982007780385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29454975636895808082990773 2761403965958982007780385)
                      ·
                        rfl

theorem cell23_5377815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_5377815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377815 prefixEnd_5377815 := by exact prefixLift 5377815
  have htrace : WordTrace (prefixWord ++ tailWord_5377815) baseStart_5377815 baseEnd_5377815 := by
    simpa [prefixWord, tailWord_5377815, baseEnd_5377815] using wordTrace_append hprefix tailTrace_5377815
  have hstable : (prefixWord ++ tailWord_5377815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377815).length < 2 ^ (prefixWord ++ tailWord_5377815).sum := by decide
  have hdescent : baseEnd_5377815 < baseStart_5377815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377818 : List Nat := [3, 1, 1, 3, 2, 4, 9]
def baseStart_5377818 : Nat := 118140960795 + 5377818 * 2 ^ 59
def prefixEnd_5377818 : Nat := 4983230072969 + 3 ^ 40 * 5377818 * 2
def baseEnd_5377818 : Nat := 34091426004949944395591

theorem tailTrace_5377818 : CollatzResearch.WordTrace tailWord_5377818 prefixEnd_5377818 34091426004949944395591 := by
  unfold tailWord_5377818
  simp only [CollatzResearch.WordTrace]
  refine ⟨49036284107772829759329527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130763424287394212691545405 49036284107772829759329527)
  ·
    refine ⟨73554426161659244638994291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49036284107772829759329527 73554426161659244638994291)
    ·
      refine ⟨110331639242488866958491437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73554426161659244638994291 110331639242488866958491437)
      ·
        refine ⟨41374364715933325109434289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110331639242488866958491437 41374364715933325109434289)
        ·
          refine ⟨31030773536949993832075717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41374364715933325109434289 31030773536949993832075717)
          ·
            refine ⟨5818270038178123843514197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31030773536949993832075717 5818270038178123843514197)
            ·
              refine ⟨34091426004949944395591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5818270038178123843514197 34091426004949944395591)
              ·
                rfl

theorem cell23_5377818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 9].length) (baseStart_5377818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377818 prefixEnd_5377818 := by exact prefixLift 5377818
  have htrace : WordTrace (prefixWord ++ tailWord_5377818) baseStart_5377818 baseEnd_5377818 := by
    simpa [prefixWord, tailWord_5377818, baseEnd_5377818] using wordTrace_append hprefix tailTrace_5377818
  have hstable : (prefixWord ++ tailWord_5377818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377818).length < 2 ^ (prefixWord ++ tailWord_5377818).sum := by decide
  have hdescent : baseEnd_5377818 < baseStart_5377818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377829 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 3, 2, 2]
def baseStart_5377829 : Nat := 118140960795 + 5377829 * 2 ^ 59
def prefixEnd_5377829 : Nat := 4983230072969 + 3 ^ 40 * 5377829 * 2
def baseEnd_5377829 : Nat := 2761411154688144953005321

theorem tailTrace_5377829 : CollatzResearch.WordTrace tailWord_5377829 prefixEnd_5377829 2761411154688144953005321 := by
  unfold tailWord_5377829
  simp only [CollatzResearch.WordTrace]
  refine ⟨196145537634051467915968541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130763691756034311943979027 196145537634051467915968541)
  ·
    refine ⟨73554576612769300468488203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196145537634051467915968541 73554576612769300468488203)
    ·
      refine ⟨110331864919153950702732305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73554576612769300468488203 110331864919153950702732305)
      ·
        refine ⟨82748898689365463027049229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110331864919153950702732305 82748898689365463027049229)
        ·
          refine ⟨31030837008512048635143461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82748898689365463027049229 31030837008512048635143461)
          ·
            refine ⟨5818281939096009119089399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31030837008512048635143461 5818281939096009119089399)
            ·
              refine ⟨8727422908644013678634099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5818281939096009119089399 8727422908644013678634099)
              ·
                refine ⟨13091134362966020517951149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8727422908644013678634099 13091134362966020517951149)
                ·
                  refine ⟨4909175386112257694231681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13091134362966020517951149 4909175386112257694231681)
                  ·
                    refine ⟨3681881539584193270673761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4909175386112257694231681 3681881539584193270673761)
                    ·
                      refine ⟨2761411154688144953005321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681881539584193270673761 2761411154688144953005321)
                      ·
                        rfl

theorem cell23_5377829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_5377829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377829 prefixEnd_5377829 := by exact prefixLift 5377829
  have htrace : WordTrace (prefixWord ++ tailWord_5377829) baseStart_5377829 baseEnd_5377829 := by
    simpa [prefixWord, tailWord_5377829, baseEnd_5377829] using wordTrace_append hprefix tailTrace_5377829
  have hstable : (prefixWord ++ tailWord_5377829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377829).length < 2 ^ (prefixWord ++ tailWord_5377829).sum := by decide
  have hdescent : baseEnd_5377829 < baseStart_5377829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377879 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_5377879 : Nat := 118140960795 + 5377879 * 2 ^ 59
def prefixEnd_5377879 : Nat := 4983230072969 + 3 ^ 40 * 5377879 * 2
def baseEnd_5377879 : Nat := 2761436828720869757380091

theorem tailTrace_5377879 : CollatzResearch.WordTrace tailWord_5377879 prefixEnd_5377879 2761436828720869757380091 := by
  unfold tailWord_5377879
  simp only [CollatzResearch.WordTrace]
  refine ⟨196147361283870326455288691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130764907522580217636859127 196147361283870326455288691)
  ·
    refine ⟨294221041925805489682933037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196147361283870326455288691 294221041925805489682933037)
    ·
      refine ⟨110332890722177058631099889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294221041925805489682933037 110332890722177058631099889)
      ·
        refine ⟨82749668041632793973324917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110332890722177058631099889 82749668041632793973324917)
        ·
          refine ⟨7757781378903074434999211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82749668041632793973324917 7757781378903074434999211)
          ·
            refine ⟨11636672068354611652498817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7757781378903074434999211 11636672068354611652498817)
            ·
              refine ⟨8727504051265958739374113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11636672068354611652498817 8727504051265958739374113)
              ·
                refine ⟨6545628038449469054530585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8727504051265958739374113 6545628038449469054530585)
                ·
                  refine ⟨4909221028837101790897939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6545628038449469054530585 4909221028837101790897939)
                  ·
                    refine ⟨7363831543255652686346909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4909221028837101790897939 7363831543255652686346909)
                    ·
                      refine ⟨2761436828720869757380091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7363831543255652686346909 2761436828720869757380091)
                      ·
                        rfl

theorem cell23_5377879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_5377879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377879 prefixEnd_5377879 := by exact prefixLift 5377879
  have htrace : WordTrace (prefixWord ++ tailWord_5377879) baseStart_5377879 baseEnd_5377879 := by
    simpa [prefixWord, tailWord_5377879, baseEnd_5377879] using wordTrace_append hprefix tailTrace_5377879
  have hstable : (prefixWord ++ tailWord_5377879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377879).length < 2 ^ (prefixWord ++ tailWord_5377879).sum := by decide
  have hdescent : baseEnd_5377879 < baseStart_5377879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377945 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 7, 2]
def baseStart_5377945 : Nat := 118140960795 + 5377945 * 2 ^ 59
def prefixEnd_5377945 : Nat := 4983230072969 + 3 ^ 40 * 5377945 * 2
def baseEnd_5377945 : Nat := 2761470718444066499154787

theorem tailTrace_5377945 : CollatzResearch.WordTrace tailWord_5377945 prefixEnd_5377945 2761470718444066499154787 := by
  unfold tailWord_5377945
  simp only [CollatzResearch.WordTrace]
  refine ⟨196149768501631219727191289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130766512334420813151460859 196149768501631219727191289)
  ·
    refine ⟨147112326376223414795393467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196149768501631219727191289 147112326376223414795393467)
    ·
      refine ⟨220668489564335122193090201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147112326376223414795393467 220668489564335122193090201)
      ·
        refine ⟨165501367173251341644817651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220668489564335122193090201 165501367173251341644817651)
        ·
          refine ⟨248252050759877012467226477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165501367173251341644817651 248252050759877012467226477)
          ·
            refine ⟨93094519034953879675209929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248252050759877012467226477 93094519034953879675209929)
            ·
              refine ⟨69820889276215409756407447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93094519034953879675209929 69820889276215409756407447)
              ·
                refine ⟨104731333914323114634611171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69820889276215409756407447 104731333914323114634611171)
                ·
                  refine ⟨157097000871484671951916757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104731333914323114634611171 157097000871484671951916757)
                  ·
                    refine ⟨3681960957925421998873049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 157097000871484671951916757 3681960957925421998873049)
                    ·
                      refine ⟨2761470718444066499154787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681960957925421998873049 2761470718444066499154787)
                      ·
                        rfl

theorem cell23_5377945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_5377945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377945 prefixEnd_5377945 := by exact prefixLift 5377945
  have htrace : WordTrace (prefixWord ++ tailWord_5377945) baseStart_5377945 baseEnd_5377945 := by
    simpa [prefixWord, tailWord_5377945, baseEnd_5377945] using wordTrace_append hprefix tailTrace_5377945
  have hstable : (prefixWord ++ tailWord_5377945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377945).length < 2 ^ (prefixWord ++ tailWord_5377945).sum := by decide
  have hdescent : baseEnd_5377945 < baseStart_5377945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377953 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5377953 : Nat := 118140960795 + 5377953 * 2 ^ 59
def prefixEnd_5377953 : Nat := 4983230072969 + 3 ^ 40 * 5377953 * 2
def baseEnd_5377953 : Nat := 2761474826289302467854751

theorem tailTrace_5377953 : CollatzResearch.WordTrace tailWord_5377953 prefixEnd_5377953 2761474826289302467854751 := by
  unfold tailWord_5377953
  simp only [CollatzResearch.WordTrace]
  refine ⟨196150060285602237093482513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130766706857068158062321675 196150060285602237093482513)
  ·
    refine ⟨147112545214201677820111885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196150060285602237093482513 147112545214201677820111885)
    ·
      refine ⟨55167204455325629182541957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147112545214201677820111885 55167204455325629182541957)
      ·
        refine ⟨10343850835373555471726617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55167204455325629182541957 10343850835373555471726617)
        ·
          refine ⟨7757888126530166603794963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10343850835373555471726617 7757888126530166603794963)
          ·
            refine ⟨11636832189795249905692445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7757888126530166603794963 11636832189795249905692445)
            ·
              refine ⟨4363812071173218714634667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11636832189795249905692445 4363812071173218714634667)
              ·
                refine ⟨6545718106759828071952001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363812071173218714634667 6545718106759828071952001)
                ·
                  refine ⟨4909288580069871053964001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6545718106759828071952001 4909288580069871053964001)
                  ·
                    refine ⟨3681966435052403290473001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4909288580069871053964001 3681966435052403290473001)
                    ·
                      refine ⟨2761474826289302467854751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3681966435052403290473001 2761474826289302467854751)
                      ·
                        rfl

theorem cell23_5377953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5377953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377953 prefixEnd_5377953 := by exact prefixLift 5377953
  have htrace : WordTrace (prefixWord ++ tailWord_5377953) baseStart_5377953 baseEnd_5377953 := by
    simpa [prefixWord, tailWord_5377953, baseEnd_5377953] using wordTrace_append hprefix tailTrace_5377953
  have hstable : (prefixWord ++ tailWord_5377953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377953).length < 2 ^ (prefixWord ++ tailWord_5377953).sum := by decide
  have hdescent : baseEnd_5377953 < baseStart_5377953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377975 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_5377975 : Nat := 118140960795 + 5377975 * 2 ^ 59
def prefixEnd_5377975 : Nat := 4983230072969 + 3 ^ 40 * 5377975 * 2
def baseEnd_5377975 : Nat := 2761486122863701381779649

theorem tailTrace_5377975 : CollatzResearch.WordTrace tailWord_5377975 prefixEnd_5377975 2761486122863701381779649 := by
  unfold tailWord_5377975
  simp only [CollatzResearch.WordTrace]
  refine ⟨196150862691522534850783379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130767241794348356567188919 196150862691522534850783379)
  ·
    refine ⟨294226294037283802276175069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196150862691522534850783379 294226294037283802276175069)
    ·
      refine ⟨110334860263981425853565651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294226294037283802276175069 110334860263981425853565651)
      ·
        refine ⟨165502290395972138780348477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110334860263981425853565651 165502290395972138780348477)
        ·
          refine ⟨62063358898489552042630679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165502290395972138780348477 62063358898489552042630679)
          ·
            refine ⟨93095038347734328063946019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62063358898489552042630679 93095038347734328063946019)
            ·
              refine ⟨139642557521601492095919029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93095038347734328063946019 139642557521601492095919029)
              ·
                refine ⟨13091489767650139883992409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139642557521601492095919029 13091489767650139883992409)
                ·
                  refine ⟨9818617325737604912994307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13091489767650139883992409 9818617325737604912994307)
                  ·
                    refine ⟨14727925988606407369491461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9818617325737604912994307 14727925988606407369491461)
                    ·
                      refine ⟨2761486122863701381779649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14727925988606407369491461 2761486122863701381779649)
                      ·
                        rfl

theorem cell23_5377975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_5377975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377975 prefixEnd_5377975 := by exact prefixLift 5377975
  have htrace : WordTrace (prefixWord ++ tailWord_5377975) baseStart_5377975 baseEnd_5377975 := by
    simpa [prefixWord, tailWord_5377975, baseEnd_5377975] using wordTrace_append hprefix tailTrace_5377975
  have hstable : (prefixWord ++ tailWord_5377975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377975).length < 2 ^ (prefixWord ++ tailWord_5377975).sum := by decide
  have hdescent : baseEnd_5377975 < baseStart_5377975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5377992 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_5377992 : Nat := 118140960795 + 5377992 * 2 ^ 59
def prefixEnd_5377992 : Nat := 4983230072969 + 3 ^ 40 * 5377992 * 2
def baseEnd_5377992 : Nat := 2761494852034827815267071

theorem tailTrace_5377992 : CollatzResearch.WordTrace tailWord_5377992 prefixEnd_5377992 2761494852034827815267071 := by
  unfold tailWord_5377992
  simp only [CollatzResearch.WordTrace]
  refine ⟨98075741366230473377076115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130767655154973964502768153 98075741366230473377076115)
  ·
    refine ⟨147113612049345710065614173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98075741366230473377076115 147113612049345710065614173)
    ·
      refine ⟨55167604518504641274605315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147113612049345710065614173 55167604518504641274605315)
      ·
        refine ⟨82751406777756961911907973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55167604518504641274605315 82751406777756961911907973)
        ·
          refine ⟨15515888770829430358482745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82751406777756961911907973 15515888770829430358482745)
          ·
            refine ⟨11636916578122072768862059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15515888770829430358482745 11636916578122072768862059)
            ·
              refine ⟨17455374867183109153293089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11636916578122072768862059 17455374867183109153293089)
              ·
                refine ⟨13091531150387331864969817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17455374867183109153293089 13091531150387331864969817)
                ·
                  refine ⟨9818648362790498898727363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13091531150387331864969817 9818648362790498898727363)
                  ·
                    refine ⟨14727972544185748348091045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9818648362790498898727363 14727972544185748348091045)
                    ·
                      refine ⟨2761494852034827815267071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14727972544185748348091045 2761494852034827815267071)
                      ·
                        rfl

theorem cell23_5377992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_5377992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5377992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5377992 prefixEnd_5377992 := by exact prefixLift 5377992
  have htrace : WordTrace (prefixWord ++ tailWord_5377992) baseStart_5377992 baseEnd_5377992 := by
    simpa [prefixWord, tailWord_5377992, baseEnd_5377992] using wordTrace_append hprefix tailTrace_5377992
  have hstable : (prefixWord ++ tailWord_5377992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5377992).length < 2 ^ (prefixWord ++ tailWord_5377992).sum := by decide
  have hdescent : baseEnd_5377992 < baseStart_5377992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5377992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378082 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_5378082 : Nat := 118140960795 + 5378082 * 2 ^ 59
def prefixEnd_5378082 : Nat := 4983230072969 + 3 ^ 40 * 5378082 * 2
def baseEnd_5378082 : Nat := 2761541065293732463141657

theorem tailTrace_5378082 : CollatzResearch.WordTrace tailWord_5378082 prefixEnd_5378082 2761541065293732463141657 := by
  unfold tailWord_5378082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49038691325533723031232125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130769843534756594749952333 49038691325533723031232125)
  ·
    refine ⟨18389509247075146136712047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49038691325533723031232125 18389509247075146136712047)
    ·
      refine ⟨27584263870612719205068071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18389509247075146136712047 27584263870612719205068071)
      ·
        refine ⟨41376395805919078807602107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27584263870612719205068071 41376395805919078807602107)
        ·
          refine ⟨62064593708878618211403161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41376395805919078807602107 62064593708878618211403161)
          ·
            refine ⟨46548445281658963658552371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62064593708878618211403161 46548445281658963658552371)
            ·
              refine ⟨69822667922488445487828557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46548445281658963658552371 69822667922488445487828557)
              ·
                refine ⟨26183500470933167057935709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69822667922488445487828557 26183500470933167057935709)
                ·
                  refine ⟨9818812676599937646725891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26183500470933167057935709 9818812676599937646725891)
                  ·
                    refine ⟨14728219014899906470088837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9818812676599937646725891 14728219014899906470088837)
                    ·
                      refine ⟨2761541065293732463141657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14728219014899906470088837 2761541065293732463141657)
                      ·
                        rfl

theorem cell23_5378082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_5378082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378082 prefixEnd_5378082 := by exact prefixLift 5378082
  have htrace : WordTrace (prefixWord ++ tailWord_5378082) baseStart_5378082 baseEnd_5378082 := by
    simpa [prefixWord, tailWord_5378082, baseEnd_5378082] using wordTrace_append hprefix tailTrace_5378082
  have hstable : (prefixWord ++ tailWord_5378082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378082).length < 2 ^ (prefixWord ++ tailWord_5378082).sum := by decide
  have hdescent : baseEnd_5378082 < baseStart_5378082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378095 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_5378095 : Nat := 118140960795 + 5378095 * 2 ^ 59
def prefixEnd_5378095 : Nat := 4983230072969 + 3 ^ 40 * 5378095 * 2
def baseEnd_5378095 : Nat := 2761547740542240912279097

theorem tailTrace_5378095 : CollatzResearch.WordTrace tailWord_5378095 prefixEnd_5378095 2761547740542240912279097 := by
  unfold tailWord_5378095
  simp only [CollatzResearch.WordTrace]
  refine ⟨196155239451087795345151739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130770159634058530230101159 196155239451087795345151739)
  ·
    refine ⟨294232859176631693017727609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196155239451087795345151739 294232859176631693017727609)
    ·
      refine ⟨220674644382473769763295707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294232859176631693017727609 220674644382473769763295707)
      ·
        refine ⟨331011966573710654644943561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220674644382473769763295707 331011966573710654644943561)
        ·
          refine ⟨248258974930282990983707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331011966573710654644943561 248258974930282990983707671)
          ·
            refine ⟨372388462395424486475561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248258974930282990983707671 372388462395424486475561507)
            ·
              refine ⟨558582693593136729713342261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372388462395424486475561507 558582693593136729713342261)
              ·
                refine ⟨52367127524356568410625837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 558582693593136729713342261 52367127524356568410625837)
                ·
                  refine ⟨19637672821633713153984689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52367127524356568410625837 19637672821633713153984689)
                  ·
                    refine ⟨14728254616225284865488517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19637672821633713153984689 14728254616225284865488517)
                    ·
                      refine ⟨2761547740542240912279097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14728254616225284865488517 2761547740542240912279097)
                      ·
                        rfl

theorem cell23_5378095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_5378095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378095 prefixEnd_5378095 := by exact prefixLift 5378095
  have htrace : WordTrace (prefixWord ++ tailWord_5378095) baseStart_5378095 baseEnd_5378095 := by
    simpa [prefixWord, tailWord_5378095, baseEnd_5378095] using wordTrace_append hprefix tailTrace_5378095
  have hstable : (prefixWord ++ tailWord_5378095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378095).length < 2 ^ (prefixWord ++ tailWord_5378095).sum := by decide
  have hdescent : baseEnd_5378095 < baseStart_5378095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378099 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 1, 1, 4]
def baseStart_5378099 : Nat := 118140960795 + 5378099 * 2 ^ 59
def prefixEnd_5378099 : Nat := 4983230072969 + 3 ^ 40 * 5378099 * 2
def baseEnd_5378099 : Nat := 2761549794464858896629079

theorem tailTrace_5378099 : CollatzResearch.WordTrace tailWord_5378099 prefixEnd_5378099 2761549794464858896629079 := by
  unfold tailWord_5378099
  simp only [CollatzResearch.WordTrace]
  refine ⟨196155385343073304028297351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130770256895382202685531567 196155385343073304028297351)
  ·
    refine ⟨294233078014609956042446027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196155385343073304028297351 294233078014609956042446027)
    ·
      refine ⟨441349617021914934063669041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294233078014609956042446027 441349617021914934063669041)
      ·
        refine ⟨331012212766436200547751781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441349617021914934063669041 331012212766436200547751781)
        ·
          refine ⟨62064789893706787602703459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331012212766436200547751781 62064789893706787602703459)
          ·
            refine ⟨93097184840560181404055189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62064789893706787602703459 93097184840560181404055189)
            ·
              refine ⟨4363930539401258503315087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93097184840560181404055189 4363930539401258503315087)
              ·
                refine ⟨6545895809101887754972631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363930539401258503315087 6545895809101887754972631)
                ·
                  refine ⟨9818843713652831632458947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6545895809101887754972631 9818843713652831632458947)
                  ·
                    refine ⟨14728265570479247448688421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9818843713652831632458947 14728265570479247448688421)
                    ·
                      refine ⟨2761549794464858896629079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14728265570479247448688421 2761549794464858896629079)
                      ·
                        rfl

theorem cell23_5378099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 1, 1, 4].length) (baseStart_5378099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378099 prefixEnd_5378099 := by exact prefixLift 5378099
  have htrace : WordTrace (prefixWord ++ tailWord_5378099) baseStart_5378099 baseEnd_5378099 := by
    simpa [prefixWord, tailWord_5378099, baseEnd_5378099] using wordTrace_append hprefix tailTrace_5378099
  have hstable : (prefixWord ++ tailWord_5378099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378099).length < 2 ^ (prefixWord ++ tailWord_5378099).sum := by decide
  have hdescent : baseEnd_5378099 < baseStart_5378099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378126 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_5378126 : Nat := 118140960795 + 5378126 * 2 ^ 59
def prefixEnd_5378126 : Nat := 4983230072969 + 3 ^ 40 * 5378126 * 2
def baseEnd_5378126 : Nat := 920521219480843430330485

theorem tailTrace_5378126 : CollatzResearch.WordTrace tailWord_5378126 prefixEnd_5378126 920521219480843430330485 := by
  unfold tailWord_5378126
  simp only [CollatzResearch.WordTrace]
  refine ⟨24519546264246935954941279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130770913409316991759686821 24519546264246935954941279)
  ·
    refine ⟨36779319396370403932411919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24519546264246935954941279 36779319396370403932411919)
    ·
      refine ⟨55168979094555605898617879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36779319396370403932411919 55168979094555605898617879)
      ·
        refine ⟨82753468641833408847926819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55168979094555605898617879 82753468641833408847926819)
        ·
          refine ⟨124130202962750113271890229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82753468641833408847926819 124130202962750113271890229)
          ·
            refine ⟨11637206527757823119239709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124130202962750113271890229 11637206527757823119239709)
            ·
              refine ⟨4363952447909183669714891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11637206527757823119239709 4363952447909183669714891)
              ·
                refine ⟨6545928671863775504572337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4363952447909183669714891 6545928671863775504572337)
                ·
                  refine ⟨4909446503897831628429253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6545928671863775504572337 4909446503897831628429253)
                  ·
                    refine ⟨920521219480843430330485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909446503897831628429253 920521219480843430330485)
                    ·
                      rfl

theorem cell23_5378126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_5378126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378126 prefixEnd_5378126 := by exact prefixLift 5378126
  have htrace : WordTrace (prefixWord ++ tailWord_5378126) baseStart_5378126 baseEnd_5378126 := by
    simpa [prefixWord, tailWord_5378126, baseEnd_5378126] using wordTrace_append hprefix tailTrace_5378126
  have hstable : (prefixWord ++ tailWord_5378126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378126).length < 2 ^ (prefixWord ++ tailWord_5378126).sum := by decide
  have hdescent : baseEnd_5378126 < baseStart_5378126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378135 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 2, 7]
def baseStart_5378135 : Nat := 118140960795 + 5378135 * 2 ^ 59
def prefixEnd_5378135 : Nat := 4983230072969 + 3 ^ 40 * 5378135 * 2
def baseEnd_5378135 : Nat := 920522759922806918592971

theorem tailTrace_5378135 : CollatzResearch.WordTrace tailWord_5378135 prefixEnd_5378135 920522759922806918592971 := by
  unfold tailWord_5378135
  simp only [CollatzResearch.WordTrace]
  refine ⟨196156698370942882176607859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130771132247295254784405239 196156698370942882176607859)
  ·
    refine ⟨294235047556414323264911789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196156698370942882176607859 294235047556414323264911789)
    ·
      refine ⟨110338142833655371224341921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294235047556414323264911789 110338142833655371224341921)
      ·
        refine ⟨82753607125241528418256441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110338142833655371224341921 82753607125241528418256441)
        ·
          refine ⟨62065205343931146313692331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82753607125241528418256441 62065205343931146313692331)
          ·
            refine ⟨93097808015896719470538497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62065205343931146313692331 93097808015896719470538497)
            ·
              refine ⟨69823356011922539602903873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93097808015896719470538497 69823356011922539602903873)
              ·
                refine ⟨52367517008941904702177905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69823356011922539602903873 52367517008941904702177905)
                ·
                  refine ⟨39275637756706428526633429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52367517008941904702177905 39275637756706428526633429)
                  ·
                    refine ⟨920522759922806918592971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39275637756706428526633429 920522759922806918592971)
                    ·
                      rfl

theorem cell23_5378135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_5378135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378135 prefixEnd_5378135 := by exact prefixLift 5378135
  have htrace : WordTrace (prefixWord ++ tailWord_5378135) baseStart_5378135 baseEnd_5378135 := by
    simpa [prefixWord, tailWord_5378135, baseEnd_5378135] using wordTrace_append hprefix tailTrace_5378135
  have hstable : (prefixWord ++ tailWord_5378135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378135).length < 2 ^ (prefixWord ++ tailWord_5378135).sum := by decide
  have hdescent : baseEnd_5378135 < baseStart_5378135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378149 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 3]
def baseStart_5378149 : Nat := 118140960795 + 5378149 * 2 ^ 59
def prefixEnd_5378149 : Nat := 4983230072969 + 3 ^ 40 * 5378149 * 2
def baseEnd_5378149 : Nat := 2761575468497583701003849

theorem tailTrace_5378149 : CollatzResearch.WordTrace tailWord_5378149 prefixEnd_5378149 2761575468497583701003849 := by
  unfold tailWord_5378149
  simp only [CollatzResearch.WordTrace]
  refine ⟨196157208992892162567617501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130771472661928108378411667 196157208992892162567617501)
  ·
    refine ⟨73558953372334560962856563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196157208992892162567617501 73558953372334560962856563)
    ·
      refine ⟨110338430058501841444284845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73558953372334560962856563 110338430058501841444284845)
      ·
        refine ⟨41376911271938190541606817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110338430058501841444284845 41376911271938190541606817)
        ·
          refine ⟨31032683453953642906205113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41376911271938190541606817 31032683453953642906205113)
          ·
            refine ⟨23274512590465232179653835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31032683453953642906205113 23274512590465232179653835)
            ·
              refine ⟨34911768885697848269480753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23274512590465232179653835 34911768885697848269480753)
              ·
                refine ⟨26183826664273386202110565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34911768885697848269480753 26183826664273386202110565)
                ·
                  refine ⟨4909467499551259912895731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26183826664273386202110565 4909467499551259912895731)
                  ·
                    refine ⟨7364201249326889869343597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4909467499551259912895731 7364201249326889869343597)
                    ·
                      refine ⟨2761575468497583701003849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7364201249326889869343597 2761575468497583701003849)
                      ·
                        rfl

theorem cell23_5378149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_5378149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378149 prefixEnd_5378149 := by exact prefixLift 5378149
  have htrace : WordTrace (prefixWord ++ tailWord_5378149) baseStart_5378149 baseEnd_5378149 := by
    simpa [prefixWord, tailWord_5378149, baseEnd_5378149] using wordTrace_append hprefix tailTrace_5378149
  have hstable : (prefixWord ++ tailWord_5378149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378149).length < 2 ^ (prefixWord ++ tailWord_5378149).sum := by decide
  have hdescent : baseEnd_5378149 < baseStart_5378149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378166 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5378166 : Nat := 118140960795 + 5378166 * 2 ^ 59
def prefixEnd_5378166 : Nat := 4983230072969 + 3 ^ 40 * 5378166 * 2
def baseEnd_5378166 : Nat := 2761584197668710134491271

theorem tailTrace_5378166 : CollatzResearch.WordTrace tailWord_5378166 prefixEnd_5378166 2761584197668710134491271 := by
  unfold tailWord_5378166
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259864314614410904436647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130771886022553716313990901 12259864314614410904436647)
  ·
    refine ⟨18389796471921616356654971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12259864314614410904436647 18389796471921616356654971)
    ·
      refine ⟨27584694707882424534982457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18389796471921616356654971 27584694707882424534982457)
      ·
        refine ⟨20688521030911818401236843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27584694707882424534982457 20688521030911818401236843)
        ·
          refine ⟨31032781546367727601855265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20688521030911818401236843 31032781546367727601855265)
          ·
            refine ⟨23274586159775795701391449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31032781546367727601855265 23274586159775795701391449)
            ·
              refine ⟨17455939619831846776043587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23274586159775795701391449 17455939619831846776043587)
              ·
                refine ⟨26183909429747770164065381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17455939619831846776043587 26183909429747770164065381)
                ·
                  refine ⟨4909483018077706905762259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26183909429747770164065381 4909483018077706905762259)
                  ·
                    refine ⟨7364224527116560358643389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4909483018077706905762259 7364224527116560358643389)
                    ·
                      refine ⟨2761584197668710134491271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7364224527116560358643389 2761584197668710134491271)
                      ·
                        rfl

theorem cell23_5378166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5378166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378166 prefixEnd_5378166 := by exact prefixLift 5378166
  have htrace : WordTrace (prefixWord ++ tailWord_5378166) baseStart_5378166 baseEnd_5378166 := by
    simpa [prefixWord, tailWord_5378166, baseEnd_5378166] using wordTrace_append hprefix tailTrace_5378166
  have hstable : (prefixWord ++ tailWord_5378166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378166).length < 2 ^ (prefixWord ++ tailWord_5378166).sum := by decide
  have hdescent : baseEnd_5378166 < baseStart_5378166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378195 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 9]
def baseStart_5378195 : Nat := 118140960795 + 5378195 * 2 ^ 59
def prefixEnd_5378195 : Nat := 4983230072969 + 3 ^ 40 * 5378195 * 2
def baseEnd_5378195 : Nat := 306844343178632280114293

theorem tailTrace_5378195 : CollatzResearch.WordTrace tailWord_5378195 prefixEnd_5378195 306844343178632280114293 := by
  unfold tailWord_5378195
  simp only [CollatzResearch.WordTrace]
  refine ⟨196158886750725512423792039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130772591167150341615861359 196158886750725512423792039)
  ·
    refine ⟨294238330126088268635688059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196158886750725512423792039 294238330126088268635688059)
    ·
      refine ⟨441357495189132402953532089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294238330126088268635688059 441357495189132402953532089)
      ·
        refine ⟨331018121391849302215149067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441357495189132402953532089 331018121391849302215149067)
        ·
          refine ⟨496527182087773953322723601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331018121391849302215149067 496527182087773953322723601)
          ·
            refine ⟨372395386565830464992042701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496527182087773953322723601 372395386565830464992042701)
            ·
              refine ⟨139648269962186424372016013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372395386565830464992042701 139648269962186424372016013)
              ·
                refine ⟨52368101235819909139506005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139648269962186424372016013 52368101235819909139506005)
                ·
                  refine ⟨306844343178632280114293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52368101235819909139506005 306844343178632280114293)
                  ·
                    rfl

theorem cell23_5378195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 9].length) (baseStart_5378195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378195 prefixEnd_5378195 := by exact prefixLift 5378195
  have htrace : WordTrace (prefixWord ++ tailWord_5378195) baseStart_5378195 baseEnd_5378195 := by
    simpa [prefixWord, tailWord_5378195, baseEnd_5378195] using wordTrace_append hprefix tailTrace_5378195
  have hstable : (prefixWord ++ tailWord_5378195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378195).length < 2 ^ (prefixWord ++ tailWord_5378195).sum := by decide
  have hdescent : baseEnd_5378195 < baseStart_5378195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378210 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_5378210 : Nat := 118140960795 + 5378210 * 2 ^ 59
def prefixEnd_5378210 : Nat := 4983230072969 + 3 ^ 40 * 5378210 * 2
def baseEnd_5378210 : Nat := 2761606790817507962341069

theorem tailTrace_5378210 : CollatzResearch.WordTrace tailWord_5378210 prefixEnd_5378210 2761606790817507962341069 := by
  unfold tailWord_5378210
  simp only [CollatzResearch.WordTrace]
  refine ⟨49039858461417792496397021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130772955897114113323725389 49039858461417792496397021)
  ·
    refine ⟨18389946923031672186148883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49039858461417792496397021 18389946923031672186148883)
    ·
      refine ⟨27584920384547508279223325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18389946923031672186148883 27584920384547508279223325)
      ·
        refine ⟨10344345144205315604708747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27584920384547508279223325 10344345144205315604708747)
        ·
          refine ⟨15516517716307973407063121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10344345144205315604708747 15516517716307973407063121)
          ·
            refine ⟨11637388287230980055297341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15516517716307973407063121 11637388287230980055297341)
            ·
              refine ⟨4364020607711617520736503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11637388287230980055297341 4364020607711617520736503)
              ·
                refine ⟨6546030911567426281104755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364020607711617520736503 6546030911567426281104755)
                ·
                  refine ⟨9819046367351139421657133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546030911567426281104755 9819046367351139421657133)
                  ·
                    refine ⟨3682142387756677283121425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9819046367351139421657133 3682142387756677283121425)
                    ·
                      refine ⟨2761606790817507962341069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682142387756677283121425 2761606790817507962341069)
                      ·
                        rfl

theorem cell23_5378210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_5378210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378210 prefixEnd_5378210 := by exact prefixLift 5378210
  have htrace : WordTrace (prefixWord ++ tailWord_5378210) baseStart_5378210 baseEnd_5378210 := by
    simpa [prefixWord, tailWord_5378210, baseEnd_5378210] using wordTrace_append hprefix tailTrace_5378210
  have hstable : (prefixWord ++ tailWord_5378210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378210).length < 2 ^ (prefixWord ++ tailWord_5378210).sum := by decide
  have hdescent : baseEnd_5378210 < baseStart_5378210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378289 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 3, 4]
def baseStart_5378289 : Nat := 118140960795 + 5378289 * 2 ^ 59
def prefixEnd_5378289 : Nat := 4983230072969 + 3 ^ 40 * 5378289 * 2
def baseEnd_5378289 : Nat := 920549118596404384417735

theorem tailTrace_5378289 : CollatzResearch.WordTrace tailWord_5378289 prefixEnd_5378289 920549118596404384417735 := by
  unfold tailWord_5378289
  simp only [CollatzResearch.WordTrace]
  refine ⟨196162315212384966477713921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130774876808256644318475947 196162315212384966477713921)
  ·
    refine ⟨147121736409288724858285441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196162315212384966477713921 147121736409288724858285441)
    ·
      refine ⟨110341302306966543643714081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147121736409288724858285441 110341302306966543643714081)
      ·
        refine ⟨82755976730224907732785561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110341302306966543643714081 82755976730224907732785561)
        ·
          refine ⟨62066982547668680799589171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82755976730224907732785561 62066982547668680799589171)
          ·
            refine ⟨93100473821503021199383757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62066982547668680799589171 93100473821503021199383757)
            ·
              refine ⟨34912677683063632949768909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93100473821503021199383757 34912677683063632949768909)
              ·
                refine ⟨13092254131148862356163341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34912677683063632949768909 13092254131148862356163341)
                ·
                  refine ⟨4909595299180823383561253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13092254131148862356163341 4909595299180823383561253)
                  ·
                    refine ⟨920549118596404384417735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909595299180823383561253 920549118596404384417735)
                    ·
                      rfl

theorem cell23_5378289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_5378289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378289 prefixEnd_5378289 := by exact prefixLift 5378289
  have htrace : WordTrace (prefixWord ++ tailWord_5378289) baseStart_5378289 baseEnd_5378289 := by
    simpa [prefixWord, tailWord_5378289, baseEnd_5378289] using wordTrace_append hprefix tailTrace_5378289
  have hstable : (prefixWord ++ tailWord_5378289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378289).length < 2 ^ (prefixWord ++ tailWord_5378289).sum := by decide
  have hdescent : baseEnd_5378289 < baseStart_5378289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378333 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5378333 : Nat := 118140960795 + 5378333 * 2 ^ 59
def prefixEnd_5378333 : Nat := 4983230072969 + 3 ^ 40 * 5378333 * 2
def baseEnd_5378333 : Nat := 2761669948938010981103003

theorem tailTrace_5378333 : CollatzResearch.WordTrace tailWord_5378333 prefixEnd_5378333 2761669948938010981103003 := by
  unfold tailWord_5378333
  simp only [CollatzResearch.WordTrace]
  refine ⟨196163920024225561992315653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130775946682817041328210435 196163920024225561992315653)
  ·
    refine ⟨36780735004542292873559185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196163920024225561992315653 36780735004542292873559185)
    ·
      refine ⟨27585551253406719655169389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36780735004542292873559185 27585551253406719655169389)
      ·
        refine ⟨10344581720027519870688521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27585551253406719655169389 10344581720027519870688521)
        ·
          refine ⟨7758436290020639903016391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10344581720027519870688521 7758436290020639903016391)
          ·
            refine ⟨11637654435030959854524587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7758436290020639903016391 11637654435030959854524587)
            ·
              refine ⟨17456481652546439781786881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11637654435030959854524587 17456481652546439781786881)
              ·
                refine ⟨13092361239409829836340161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17456481652546439781786881 13092361239409829836340161)
                ·
                  refine ⟨9819270929557372377255121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13092361239409829836340161 9819270929557372377255121)
                  ·
                    refine ⟨7364453197168029282941341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9819270929557372377255121 7364453197168029282941341)
                    ·
                      refine ⟨2761669948938010981103003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7364453197168029282941341 2761669948938010981103003)
                      ·
                        rfl

theorem cell23_5378333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5378333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378333 prefixEnd_5378333 := by exact prefixLift 5378333
  have htrace : WordTrace (prefixWord ++ tailWord_5378333) baseStart_5378333 baseEnd_5378333 := by
    simpa [prefixWord, tailWord_5378333, baseEnd_5378333] using wordTrace_append hprefix tailTrace_5378333
  have hstable : (prefixWord ++ tailWord_5378333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378333).length < 2 ^ (prefixWord ++ tailWord_5378333).sum := by decide
  have hdescent : baseEnd_5378333 < baseStart_5378333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378340 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_5378340 : Nat := 118140960795 + 5378340 * 2 ^ 59
def prefixEnd_5378340 : Nat := 4983230072969 + 3 ^ 40 * 5378340 * 2
def baseEnd_5378340 : Nat := 920557847767530817905157

theorem tailTrace_5378340 : CollatzResearch.WordTrace tailWord_5378340 prefixEnd_5378340 920557847767530817905157 := by
  unfold tailWord_5378340
  simp only [CollatzResearch.WordTrace]
  refine ⟨98082087667600101093910237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130776116890133468125213649 98082087667600101093910237)
  ·
    refine ⟨36780782875350037910216339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98082087667600101093910237 36780782875350037910216339)
    ·
      refine ⟨55171174313025056865324509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36780782875350037910216339 55171174313025056865324509)
      ·
        refine ⟨20689190367384396324496691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55171174313025056865324509 20689190367384396324496691)
        ·
          refine ⟨31033785551076594486745037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20689190367384396324496691 31033785551076594486745037)
          ·
            refine ⟨11637669581653722932529389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31033785551076594486745037 11637669581653722932529389)
            ·
              refine ⟨4364126093120146099698521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11637669581653722932529389 4364126093120146099698521)
              ·
                refine ⟨3273094569840109574773891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4364126093120146099698521 3273094569840109574773891)
                ·
                  refine ⟨4909641854760164362160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273094569840109574773891 4909641854760164362160837)
                  ·
                    refine ⟨920557847767530817905157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909641854760164362160837 920557847767530817905157)
                    ·
                      rfl

theorem cell23_5378340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_5378340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378340 prefixEnd_5378340 := by exact prefixLift 5378340
  have htrace : WordTrace (prefixWord ++ tailWord_5378340) baseStart_5378340 baseEnd_5378340 := by
    simpa [prefixWord, tailWord_5378340, baseEnd_5378340] using wordTrace_append hprefix tailTrace_5378340
  have hstable : (prefixWord ++ tailWord_5378340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378340).length < 2 ^ (prefixWord ++ tailWord_5378340).sum := by decide
  have hdescent : baseEnd_5378340 < baseStart_5378340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378353 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 6]
def baseStart_5378353 : Nat := 118140960795 + 5378353 * 2 ^ 59
def prefixEnd_5378353 : Nat := 4983230072969 + 3 ^ 40 * 5378353 * 2
def baseEnd_5378353 : Nat := 306853357616788989205879

theorem tailTrace_5378353 : CollatzResearch.WordTrace tailWord_5378353 prefixEnd_5378353 306853357616788989205879 := by
  unfold tailWord_5378353
  simp only [CollatzResearch.WordTrace]
  refine ⟨196164649484153105408043713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130776432989435403605362475 196164649484153105408043713)
  ·
    refine ⟨147123487113114829056032785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196164649484153105408043713 147123487113114829056032785)
    ·
      refine ⟨110342615334836121792024589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147123487113114829056032785 110342615334836121792024589)
      ·
        refine ⟨41378480750563545672009221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110342615334836121792024589 41378480750563545672009221)
        ·
          refine ⟨7758465140730664813501729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41378480750563545672009221 7758465140730664813501729)
          ·
            refine ⟨5818848855547998610126297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7758465140730664813501729 5818848855547998610126297)
            ·
              refine ⟨4364136641660998957594723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818848855547998610126297 4364136641660998957594723)
              ·
                refine ⟨6546204962491498436392085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364136641660998957594723 6546204962491498436392085)
                ·
                  refine ⟨306853357616788989205879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6546204962491498436392085 306853357616788989205879)
                  ·
                    rfl

theorem cell23_5378353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 6].length) (baseStart_5378353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378353 prefixEnd_5378353 := by exact prefixLift 5378353
  have htrace : WordTrace (prefixWord ++ tailWord_5378353) baseStart_5378353 baseEnd_5378353 := by
    simpa [prefixWord, tailWord_5378353, baseEnd_5378353] using wordTrace_append hprefix tailTrace_5378353
  have hstable : (prefixWord ++ tailWord_5378353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378353).length < 2 ^ (prefixWord ++ tailWord_5378353).sum := by decide
  have hdescent : baseEnd_5378353 < baseStart_5378353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378366 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_5378366 : Nat := 118140960795 + 5378366 * 2 ^ 59
def prefixEnd_5378366 : Nat := 4983230072969 + 3 ^ 40 * 5378366 * 2
def baseEnd_5378366 : Nat := 920562297933203117330117

theorem tailTrace_5378366 : CollatzResearch.WordTrace tailWord_5378366 prefixEnd_5378366 920562297933203117330117 := by
  unfold tailWord_5378366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24520640454138251078533369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130776749088737339085511301 24520640454138251078533369)
  ·
    refine ⟨18390480340603688308900027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24520640454138251078533369 18390480340603688308900027)
    ·
      refine ⟨27585720510905532463350041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18390480340603688308900027 27585720510905532463350041)
      ·
        refine ⟨20689290383179149347512531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27585720510905532463350041 20689290383179149347512531)
        ·
          refine ⟨31033935574768724021268797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20689290383179149347512531 31033935574768724021268797)
          ·
            refine ⟨11637725840538271507975799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31033935574768724021268797 11637725840538271507975799)
            ·
              refine ⟨17456588760807407261963699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11637725840538271507975799 17456588760807407261963699)
              ·
                refine ⟨26184883141211110892945549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17456588760807407261963699 26184883141211110892945549)
                ·
                  refine ⟨9819331177954166584854581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26184883141211110892945549 9819331177954166584854581)
                  ·
                    refine ⟨920562297933203117330117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9819331177954166584854581 920562297933203117330117)
                    ·
                      rfl

theorem cell23_5378366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_5378366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378366 prefixEnd_5378366 := by exact prefixLift 5378366
  have htrace : WordTrace (prefixWord ++ tailWord_5378366) baseStart_5378366 baseEnd_5378366 := by
    simpa [prefixWord, tailWord_5378366, baseEnd_5378366] using wordTrace_append hprefix tailTrace_5378366
  have hstable : (prefixWord ++ tailWord_5378366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378366).length < 2 ^ (prefixWord ++ tailWord_5378366).sum := by decide
  have hdescent : baseEnd_5378366 < baseStart_5378366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378379 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 4, 4]
def baseStart_5378379 : Nat := 118140960795 + 5378379 * 2 ^ 59
def prefixEnd_5378379 : Nat := 4983230072969 + 3 ^ 40 * 5378379 * 2
def baseEnd_5378379 : Nat := 920564523016039267042597

theorem tailTrace_5378379 : CollatzResearch.WordTrace tailWord_5378379 prefixEnd_5378379 920564523016039267042597 := by
  unfold tailWord_5378379
  simp only [CollatzResearch.WordTrace]
  refine ⟨196165597782058911848490191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130777065188039274565660127 196165597782058911848490191)
  ·
    refine ⟨294248396673088367772735287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196165597782058911848490191 294248396673088367772735287)
    ·
      refine ⟨441372595009632551659102931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294248396673088367772735287 441372595009632551659102931)
      ·
        refine ⟨662058892514448827488654397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441372595009632551659102931 662058892514448827488654397)
        ·
          refine ⟨248272084692918310308245399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 662058892514448827488654397 248272084692918310308245399)
          ·
            refine ⟨372408127039377465462368099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248272084692918310308245399 372408127039377465462368099)
            ·
              refine ⟨558612190559066198193552149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372408127039377465462368099 558612190559066198193552149)
              ·
                refine ⟨26184946432456228040322757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 558612190559066198193552149 26184946432456228040322757)
                ·
                  refine ⟨4909677456085542757560517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26184946432456228040322757 4909677456085542757560517)
                  ·
                    refine ⟨920564523016039267042597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909677456085542757560517 920564523016039267042597)
                    ·
                      rfl

theorem cell23_5378379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 4].length) (baseStart_5378379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378379 prefixEnd_5378379 := by exact prefixLift 5378379
  have htrace : WordTrace (prefixWord ++ tailWord_5378379) baseStart_5378379 baseEnd_5378379 := by
    simpa [prefixWord, tailWord_5378379, baseEnd_5378379] using wordTrace_append hprefix tailTrace_5378379
  have hstable : (prefixWord ++ tailWord_5378379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378379).length < 2 ^ (prefixWord ++ tailWord_5378379).sum := by decide
  have hdescent : baseEnd_5378379 < baseStart_5378379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378386 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_5378386 : Nat := 118140960795 + 5378386 * 2 ^ 59
def prefixEnd_5378386 : Nat := 4983230072969 + 3 ^ 40 * 5378386 * 2
def baseEnd_5378386 : Nat := 2761697163412699273740259

theorem tailTrace_5378386 : CollatzResearch.WordTrace tailWord_5378386 prefixEnd_5378386 2761697163412699273740259 := by
  unfold tailWord_5378386
  simp only [CollatzResearch.WordTrace]
  refine ⟨49041463273258388010998753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130777235395355701362663341 49041463273258388010998753)
  ·
    refine ⟨36781097454943791008249065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49041463273258388010998753 36781097454943791008249065)
    ·
      refine ⟨27585823091207843256186799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36781097454943791008249065 27585823091207843256186799)
      ·
        refine ⟨41378734636811764884280199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27585823091207843256186799 41378734636811764884280199)
        ·
          refine ⟨62068101955217647326420299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41378734636811764884280199 62068101955217647326420299)
          ·
            refine ⟨93102152932826470989630449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62068101955217647326420299 93102152932826470989630449)
            ·
              refine ⟨69826614699619853242222837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93102152932826470989630449 69826614699619853242222837)
              ·
                refine ⟨6546245128089361241458391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69826614699619853242222837 6546245128089361241458391)
                ·
                  refine ⟨9819367692134041862187587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546245128089361241458391 9819367692134041862187587)
                  ·
                    refine ⟨14729051538201062793281381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9819367692134041862187587 14729051538201062793281381)
                    ·
                      refine ⟨2761697163412699273740259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14729051538201062793281381 2761697163412699273740259)
                      ·
                        rfl

theorem cell23_5378386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_5378386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378386 prefixEnd_5378386 := by exact prefixLift 5378386
  have htrace : WordTrace (prefixWord ++ tailWord_5378386) baseStart_5378386 baseEnd_5378386 := by
    simpa [prefixWord, tailWord_5378386, baseEnd_5378386] using wordTrace_append hprefix tailTrace_5378386
  have hstable : (prefixWord ++ tailWord_5378386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378386).length < 2 ^ (prefixWord ++ tailWord_5378386).sum := by decide
  have hdescent : baseEnd_5378386 < baseStart_5378386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378403 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 3, 2, 2]
def baseStart_5378403 : Nat := 118140960795 + 5378403 * 2 ^ 59
def prefixEnd_5378403 : Nat := 4983230072969 + 3 ^ 40 * 5378403 * 2
def baseEnd_5378403 : Nat := 2761705892583825707227681

theorem tailTrace_5378403 : CollatzResearch.WordTrace tailWord_5378403 prefixEnd_5378403 2761705892583825707227681 := by
  unfold tailWord_5378403
  simp only [CollatzResearch.WordTrace]
  refine ⟨196166473133971963947363863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130777648755981309298242575 196166473133971963947363863)
  ·
    refine ⟨294249709700957945921045795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196166473133971963947363863 294249709700957945921045795)
    ·
      refine ⟨441374564551436918881568693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294249709700957945921045795 441374564551436918881568693)
      ·
        refine ⟨41378865426697211145147065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 441374564551436918881568693 41378865426697211145147065)
        ·
          refine ⟨31034149070022908358860299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41378865426697211145147065 31034149070022908358860299)
          ·
            refine ⟨46551223605034362538290449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31034149070022908358860299 46551223605034362538290449)
            ·
              refine ⟨34913417703775771903717837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46551223605034362538290449 34913417703775771903717837)
              ·
                refine ⟨13092531638915914463894189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34913417703775771903717837 13092531638915914463894189)
                ·
                  refine ⟨4909699364593467923960321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13092531638915914463894189 4909699364593467923960321)
                  ·
                    refine ⟨3682274523445100942970241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4909699364593467923960321 3682274523445100942970241)
                    ·
                      refine ⟨2761705892583825707227681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682274523445100942970241 2761705892583825707227681)
                      ·
                        rfl

theorem cell23_5378403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_5378403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378403 prefixEnd_5378403 := by exact prefixLift 5378403
  have htrace : WordTrace (prefixWord ++ tailWord_5378403) baseStart_5378403 baseEnd_5378403 := by
    simpa [prefixWord, tailWord_5378403, baseEnd_5378403] using wordTrace_append hprefix tailTrace_5378403
  have hstable : (prefixWord ++ tailWord_5378403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378403).length < 2 ^ (prefixWord ++ tailWord_5378403).sum := by decide
  have hdescent : baseEnd_5378403 < baseStart_5378403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378416 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_5378416 : Nat := 118140960795 + 5378416 * 2 ^ 59
def prefixEnd_5378416 : Nat := 4983230072969 + 3 ^ 40 * 5378416 * 2
def baseEnd_5378416 : Nat := 2761712567832334156365121

theorem tailTrace_5378416 : CollatzResearch.WordTrace tailWord_5378416 prefixEnd_5378416 2761712567832334156365121 := by
  unfold tailWord_5378416
  simp only [CollatzResearch.WordTrace]
  refine ⟨98083473641462433583793551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130777964855283244778391401 98083473641462433583793551)
  ·
    refine ⟨147125210462193650375690327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98083473641462433583793551 147125210462193650375690327)
    ·
      refine ⟨220687815693290475563535491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147125210462193650375690327 220687815693290475563535491)
      ·
        refine ⟨331031723539935713345303237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220687815693290475563535491 331031723539935713345303237)
        ·
          refine ⟨62068448163737946252244357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331031723539935713345303237 62068448163737946252244357)
          ·
            refine ⟨11637834030700864922295817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62068448163737946252244357 11637834030700864922295817)
            ·
              refine ⟨8728375523025648691721863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11637834030700864922295817 8728375523025648691721863)
              ·
                refine ⟨13092563284538473037582795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728375523025648691721863 13092563284538473037582795)
                ·
                  refine ⟨19638844926807709556374193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13092563284538473037582795 19638844926807709556374193)
                  ·
                    refine ⟨14729133695105782167280645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19638844926807709556374193 14729133695105782167280645)
                    ·
                      refine ⟨2761712567832334156365121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14729133695105782167280645 2761712567832334156365121)
                      ·
                        rfl

theorem cell23_5378416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_5378416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378416 prefixEnd_5378416 := by exact prefixLift 5378416
  have htrace : WordTrace (prefixWord ++ tailWord_5378416) baseStart_5378416 baseEnd_5378416 := by
    simpa [prefixWord, tailWord_5378416, baseEnd_5378416] using wordTrace_append hprefix tailTrace_5378416
  have hstable : (prefixWord ++ tailWord_5378416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378416).length < 2 ^ (prefixWord ++ tailWord_5378416).sum := by decide
  have hdescent : baseEnd_5378416 < baseStart_5378416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378419 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3]
def baseStart_5378419 : Nat := 118140960795 + 5378419 * 2 ^ 59
def prefixEnd_5378419 : Nat := 4983230072969 + 3 ^ 40 * 5378419 * 2
def baseEnd_5378419 : Nat := 2761714108274297644627607

theorem tailTrace_5378419 : CollatzResearch.WordTrace tailWord_5378419 prefixEnd_5378419 2761714108274297644627607 := by
  unfold tailWord_5378419
  simp only [CollatzResearch.WordTrace]
  refine ⟨196167056701913998679946311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130778037801275999119964207 196167056701913998679946311)
  ·
    refine ⟨294250585052870998019919467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196167056701913998679946311 294250585052870998019919467)
    ·
      refine ⟨441375877579306497029879201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294250585052870998019919467 441375877579306497029879201)
      ·
        refine ⟨331031908184479872772409401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441375877579306497029879201 331031908184479872772409401)
        ·
          refine ⟨248273931138359904579307051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331031908184479872772409401 248273931138359904579307051)
          ·
            refine ⟨372410896707539856868960577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248273931138359904579307051 372410896707539856868960577)
            ·
              refine ⟨279308172530654892651720433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372410896707539856868960577 279308172530654892651720433)
              ·
                refine ⟨209481129397991169488790325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279308172530654892651720433 209481129397991169488790325)
                ·
                  refine ⟨19638855881061672139574093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209481129397991169488790325 19638855881061672139574093)
                  ·
                    refine ⟨7364570955398127052340285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19638855881061672139574093 7364570955398127052340285)
                    ·
                      refine ⟨2761714108274297644627607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7364570955398127052340285 2761714108274297644627607)
                      ·
                        rfl

theorem cell23_5378419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_5378419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378419 prefixEnd_5378419 := by exact prefixLift 5378419
  have htrace : WordTrace (prefixWord ++ tailWord_5378419) baseStart_5378419 baseEnd_5378419 := by
    simpa [prefixWord, tailWord_5378419, baseEnd_5378419] using wordTrace_append hprefix tailTrace_5378419
  have hstable : (prefixWord ++ tailWord_5378419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378419).length < 2 ^ (prefixWord ++ tailWord_5378419).sum := by decide
  have hdescent : baseEnd_5378419 < baseStart_5378419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378434 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5378434 : Nat := 118140960795 + 5378434 * 2 ^ 59
def prefixEnd_5378434 : Nat := 4983230072969 + 3 ^ 40 * 5378434 * 2
def baseEnd_5378434 : Nat := 920573936828038361980013

theorem tailTrace_5378434 : CollatzResearch.WordTrace tailWord_5378434 prefixEnd_5378434 920573936828038361980013 := by
  unfold tailWord_5378434
  simp only [CollatzResearch.WordTrace]
  refine ⟨49041900949214914060435589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130778402531239770827828237 49041900949214914060435589)
  ·
    refine ⟨9195356427977796386331673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49041900949214914060435589 9195356427977796386331673)
    ·
      refine ⟨6896517320983347289748755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9195356427977796386331673 6896517320983347289748755)
      ·
        refine ⟨10344775981475020934623133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6896517320983347289748755 10344775981475020934623133)
        ·
          refine ⟨3879290993053132850483675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10344775981475020934623133 3879290993053132850483675)
          ·
            refine ⟨5818936489579699275725513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879290993053132850483675 5818936489579699275725513)
            ·
              refine ⟨4364202367184774456794135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818936489579699275725513 4364202367184774456794135)
              ·
                refine ⟨6546303550777161685191203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364202367184774456794135 6546303550777161685191203)
                ·
                  refine ⟨9819455326165742527786805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546303550777161685191203 9819455326165742527786805)
                  ·
                    refine ⟨920573936828038361980013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9819455326165742527786805 920573936828038361980013)
                    ·
                      rfl

theorem cell23_5378434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5378434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378434 prefixEnd_5378434 := by exact prefixLift 5378434
  have htrace : WordTrace (prefixWord ++ tailWord_5378434) baseStart_5378434 baseEnd_5378434 := by
    simpa [prefixWord, tailWord_5378434, baseEnd_5378434] using wordTrace_append hprefix tailTrace_5378434
  have hstable : (prefixWord ++ tailWord_5378434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378434).length < 2 ^ (prefixWord ++ tailWord_5378434).sum := by decide
  have hdescent : baseEnd_5378434 < baseStart_5378434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378436 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_5378436 : Nat := 118140960795 + 5378436 * 2 ^ 59
def prefixEnd_5378436 : Nat := 4983230072969 + 3 ^ 40 * 5378436 * 2
def baseEnd_5378436 : Nat := 2761722837445424078115029

theorem tailTrace_5378436 : CollatzResearch.WordTrace tailWord_5378436 prefixEnd_5378436 2761722837445424078115029 := by
  unfold tailWord_5378436
  simp only [CollatzResearch.WordTrace]
  refine ⟨98083838371426205291657581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130778451161901607055543441 98083838371426205291657581)
  ·
    refine ⟨36781439389284826984371593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98083838371426205291657581 36781439389284826984371593)
    ·
      refine ⟨27586079541963620238278695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36781439389284826984371593 27586079541963620238278695)
      ·
        refine ⟨41379119312945430357418043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27586079541963620238278695 41379119312945430357418043)
        ·
          refine ⟨62068678969418145536127065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41379119312945430357418043 62068678969418145536127065)
          ·
            refine ⟨46551509227063609152095299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62068678969418145536127065 46551509227063609152095299)
            ·
              refine ⟨69827263840595413728142949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46551509227063609152095299 69827263840595413728142949)
              ·
                refine ⟨13092611970111640074026803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69827263840595413728142949 13092611970111640074026803)
                ·
                  refine ⟨19638917955167460111040205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13092611970111640074026803 19638917955167460111040205)
                  ·
                    refine ⟨7364594233187797541640077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19638917955167460111040205 7364594233187797541640077)
                    ·
                      refine ⟨2761722837445424078115029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7364594233187797541640077 2761722837445424078115029)
                      ·
                        rfl

theorem cell23_5378436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_5378436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378436 prefixEnd_5378436 := by exact prefixLift 5378436
  have htrace : WordTrace (prefixWord ++ tailWord_5378436) baseStart_5378436 baseEnd_5378436 := by
    simpa [prefixWord, tailWord_5378436, baseEnd_5378436] using wordTrace_append hprefix tailTrace_5378436
  have hstable : (prefixWord ++ tailWord_5378436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378436).length < 2 ^ (prefixWord ++ tailWord_5378436).sum := by decide
  have hdescent : baseEnd_5378436 < baseStart_5378436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378469 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 2, 6]
def baseStart_5378469 : Nat := 118140960795 + 5378469 * 2 ^ 59
def prefixEnd_5378469 : Nat := 4983230072969 + 3 ^ 40 * 5378469 * 2
def baseEnd_5378469 : Nat := 920579927435674149667459

theorem tailTrace_5378469 : CollatzResearch.WordTrace tailWord_5378469 prefixEnd_5378469 920579927435674149667459 := by
  unfold tailWord_5378469
  simp only [CollatzResearch.WordTrace]
  refine ⟨196168880351732857219266461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130779253567821904812844307 196168880351732857219266461)
  ·
    refine ⟨73563330131899821457224923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196168880351732857219266461 73563330131899821457224923)
    ·
      refine ⟨110344995197849732185837385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73563330131899821457224923 110344995197849732185837385)
      ·
        refine ⟨82758746398387299139378039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110344995197849732185837385 82758746398387299139378039)
        ·
          refine ⟨124138119597580948709067059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82758746398387299139378039 124138119597580948709067059)
          ·
            refine ⟨186207179396371423063600589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124138119597580948709067059 186207179396371423063600589)
            ·
              refine ⟨69827692273639283648850221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186207179396371423063600589 69827692273639283648850221)
              ·
                refine ⟨26185384602614731368318833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69827692273639283648850221 26185384602614731368318833)
                ·
                  refine ⟨19639038451961048526239125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26185384602614731368318833 19639038451961048526239125)
                  ·
                    refine ⟨920579927435674149667459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19639038451961048526239125 920579927435674149667459)
                    ·
                      rfl

theorem cell23_5378469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_5378469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378469 prefixEnd_5378469 := by exact prefixLift 5378469
  have htrace : WordTrace (prefixWord ++ tailWord_5378469) baseStart_5378469 baseEnd_5378469 := by
    simpa [prefixWord, tailWord_5378469, baseEnd_5378469] using wordTrace_append hprefix tailTrace_5378469
  have hstable : (prefixWord ++ tailWord_5378469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378469).length < 2 ^ (prefixWord ++ tailWord_5378469).sum := by decide
  have hdescent : baseEnd_5378469 < baseStart_5378469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378474 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5378474 : Nat := 118140960795 + 5378474 * 2 ^ 59
def prefixEnd_5378474 : Nat := 4983230072969 + 3 ^ 40 * 5378474 * 2
def baseEnd_5378474 : Nat := 2761742349710294929439855

theorem tailTrace_5378474 : CollatzResearch.WordTrace tailWord_5378474 prefixEnd_5378474 2761742349710294929439855 := by
  unfold tailWord_5378474
  simp only [CollatzResearch.WordTrace]
  refine ⟨49042265679178685768299619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130779375144476495382132317 49042265679178685768299619)
  ·
    refine ⟨73563398518768028652449429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49042265679178685768299619 73563398518768028652449429)
    ·
      refine ⟨3448284305567251343083567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73563398518768028652449429 3448284305567251343083567)
      ·
        refine ⟨5172426458350877014625351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3448284305567251343083567 5172426458350877014625351)
        ·
          refine ⟨7758639687526315521938027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5172426458350877014625351 7758639687526315521938027)
          ·
            refine ⟨11637959531289473282907041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7758639687526315521938027 11637959531289473282907041)
            ·
              refine ⟨8728469648467104962180281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11637959531289473282907041 8728469648467104962180281)
              ·
                refine ⟨6546352236350328721635211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8728469648467104962180281 6546352236350328721635211)
                ·
                  refine ⟨9819528354525493082452817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546352236350328721635211 9819528354525493082452817)
                  ·
                    refine ⟨7364646265894119811839613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9819528354525493082452817 7364646265894119811839613)
                    ·
                      refine ⟨2761742349710294929439855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7364646265894119811839613 2761742349710294929439855)
                      ·
                        rfl

theorem cell23_5378474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5378474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378474 prefixEnd_5378474 := by exact prefixLift 5378474
  have htrace : WordTrace (prefixWord ++ tailWord_5378474) baseStart_5378474 baseEnd_5378474 := by
    simpa [prefixWord, tailWord_5378474, baseEnd_5378474] using wordTrace_append hprefix tailTrace_5378474
  have hstable : (prefixWord ++ tailWord_5378474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378474).length < 2 ^ (prefixWord ++ tailWord_5378474).sum := by decide
  have hdescent : baseEnd_5378474 < baseStart_5378474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378510 : List Nat := [4, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_5378510 : Nat := 118140960795 + 5378510 * 2 ^ 59
def prefixEnd_5378510 : Nat := 4983230072969 + 3 ^ 40 * 5378510 * 2
def baseEnd_5378510 : Nat := 2761760835013856788589689

theorem tailTrace_5378510 : CollatzResearch.WordTrace tailWord_5378510 prefixEnd_5378510 2761760835013856788589689 := by
  unfold tailWord_5378510
  simp only [CollatzResearch.WordTrace]
  refine ⟨24521296968073040152688623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130780250496389547481005989 24521296968073040152688623)
  ·
    refine ⟨36781945452109560229032935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24521296968073040152688623 36781945452109560229032935)
    ·
      refine ⟨55172918178164340343549403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36781945452109560229032935 55172918178164340343549403)
      ·
        refine ⟨82759377267246510515324105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55172918178164340343549403 82759377267246510515324105)
        ·
          refine ⟨62069532950434882886493079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82759377267246510515324105 62069532950434882886493079)
          ·
            refine ⟨93104299425652324329739619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62069532950434882886493079 93104299425652324329739619)
            ·
              refine ⟨139656449138478486494609429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93104299425652324329739619 139656449138478486494609429)
              ·
                refine ⟨6546396053366179054434817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139656449138478486494609429 6546396053366179054434817)
                ·
                  refine ⟨4909797040024634290826113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6546396053366179054434817 4909797040024634290826113)
                  ·
                    refine ⟨3682347780018475718119585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4909797040024634290826113 3682347780018475718119585)
                    ·
                      refine ⟨2761760835013856788589689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682347780018475718119585 2761760835013856788589689)
                      ·
                        rfl

theorem cell23_5378510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_5378510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378510 prefixEnd_5378510 := by exact prefixLift 5378510
  have htrace : WordTrace (prefixWord ++ tailWord_5378510) baseStart_5378510 baseEnd_5378510 := by
    simpa [prefixWord, tailWord_5378510, baseEnd_5378510] using wordTrace_append hprefix tailTrace_5378510
  have hstable : (prefixWord ++ tailWord_5378510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378510).length < 2 ^ (prefixWord ++ tailWord_5378510).sum := by decide
  have hdescent : baseEnd_5378510 < baseStart_5378510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378527 : List Nat := [1, 1, 2, 3, 3, 2, 4, 1, 2, 2, 2]
def baseStart_5378527 : Nat := 118140960795 + 5378527 * 2 ^ 59
def prefixEnd_5378527 : Nat := 4983230072969 + 3 ^ 40 * 5378527 * 2
def baseEnd_5378527 : Nat := 2761769564184983222077111

theorem tailTrace_5378527 : CollatzResearch.WordTrace tailWord_5378527 prefixEnd_5378527 2761769564184983222077111 := by
  unfold tailWord_5378527
  simp only [CollatzResearch.WordTrace]
  refine ⟨196170995785522733124877835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130780663857015155416585223 196170995785522733124877835)
  ·
    refine ⟨294256493678284099687316753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196170995785522733124877835 294256493678284099687316753)
    ·
      refine ⟨220692370258713074765487565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294256493678284099687316753 220692370258713074765487565)
      ·
        refine ⟨82759638847017403037057837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220692370258713074765487565 82759638847017403037057837)
        ·
          refine ⟨31034864567631526138896689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82759638847017403037057837 31034864567631526138896689)
          ·
            refine ⟨23276148425723644604172517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31034864567631526138896689 23276148425723644604172517)
            ·
              refine ⟨4364277829823183363282347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23276148425723644604172517 4364277829823183363282347)
              ·
                refine ⟨6546416744734775044923521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4364277829823183363282347 6546416744734775044923521)
                ·
                  refine ⟨4909812558551081283692641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6546416744734775044923521 4909812558551081283692641)
                  ·
                    refine ⟨3682359418913310962769481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4909812558551081283692641 3682359418913310962769481)
                    ·
                      refine ⟨2761769564184983222077111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682359418913310962769481 2761769564184983222077111)
                      ·
                        rfl

theorem cell23_5378527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_5378527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378527 prefixEnd_5378527 := by exact prefixLift 5378527
  have htrace : WordTrace (prefixWord ++ tailWord_5378527) baseStart_5378527 baseEnd_5378527 := by
    simpa [prefixWord, tailWord_5378527, baseEnd_5378527] using wordTrace_append hprefix tailTrace_5378527
  have hstable : (prefixWord ++ tailWord_5378527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378527).length < 2 ^ (prefixWord ++ tailWord_5378527).sum := by decide
  have hdescent : baseEnd_5378527 < baseStart_5378527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378539 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7]
def baseStart_5378539 : Nat := 118140960795 + 5378539 * 2 ^ 59
def prefixEnd_5378539 : Nat := 4983230072969 + 3 ^ 40 * 5378539 * 2
def baseEnd_5378539 : Nat := 2761775725952837175127055

theorem tailTrace_5378539 : CollatzResearch.WordTrace tailWord_5378539 prefixEnd_5378539 2761775725952837175127055 := by
  unfold tailWord_5378539
  simp only [CollatzResearch.WordTrace]
  refine ⟨196171433461479259174314671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130780955640986172782876447 196171433461479259174314671)
  ·
    refine ⟨294257150192218888761472007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196171433461479259174314671 294257150192218888761472007)
    ·
      refine ⟨441385725288328333142208011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294257150192218888761472007 441385725288328333142208011)
      ·
        refine ⟨662078587932492499713312017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441385725288328333142208011 662078587932492499713312017)
        ·
          refine ⟨496558940949369374784984013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662078587932492499713312017 496558940949369374784984013)
          ·
            refine ⟨186209602856013515544369005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496558940949369374784984013 186209602856013515544369005)
            ·
              refine ⟨69828601071005068329138377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186209602856013515544369005 69828601071005068329138377)
              ·
                refine ⟨52371450803253801246853783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69828601071005068329138377 52371450803253801246853783)
                ·
                  refine ⟨78557176204880701870280675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52371450803253801246853783 78557176204880701870280675)
                  ·
                    refine ⟨117835764307321052805421013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78557176204880701870280675 117835764307321052805421013)
                    ·
                      refine ⟨2761775725952837175127055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117835764307321052805421013 2761775725952837175127055)
                      ·
                        rfl

theorem cell23_5378539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_5378539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378539 prefixEnd_5378539 := by exact prefixLift 5378539
  have htrace : WordTrace (prefixWord ++ tailWord_5378539) baseStart_5378539 baseEnd_5378539 := by
    simpa [prefixWord, tailWord_5378539, baseEnd_5378539] using wordTrace_append hprefix tailTrace_5378539
  have hstable : (prefixWord ++ tailWord_5378539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378539).length < 2 ^ (prefixWord ++ tailWord_5378539).sum := by decide
  have hdescent : baseEnd_5378539 < baseStart_5378539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378567 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 5]
def baseStart_5378567 : Nat := 118140960795 + 5378567 * 2 ^ 59
def prefixEnd_5378567 : Nat := 4983230072969 + 3 ^ 40 * 5378567 * 2
def baseEnd_5378567 : Nat := 306865567045684785064103

theorem tailTrace_5378567 : CollatzResearch.WordTrace tailWord_5378567 prefixEnd_5378567 306865567045684785064103 := by
  unfold tailWord_5378567
  simp only [CollatzResearch.WordTrace]
  refine ⟨196172454705377819956333955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130781636470251879970889303 196172454705377819956333955)
  ·
    refine ⟨294258682058066729934500933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196172454705377819956333955 294258682058066729934500933)
    ·
      refine ⟨55173502885887511862718925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294258682058066729934500933 55173502885887511862718925)
      ·
        refine ⟨20690063582207816948519597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55173502885887511862718925 20690063582207816948519597)
        ·
          refine ⟨7758773843327931355694849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20690063582207816948519597 7758773843327931355694849)
          ·
            refine ⟨5819080382495948516771137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7758773843327931355694849 5819080382495948516771137)
            ·
              refine ⟨4364310286871961387578353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5819080382495948516771137 4364310286871961387578353)
              ·
                refine ⟨3273232715153971040683765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4364310286871961387578353 3273232715153971040683765)
                ·
                  refine ⟨306865567045684785064103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3273232715153971040683765 306865567045684785064103)
                  ·
                    rfl

theorem cell23_5378567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 5].length) (baseStart_5378567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378567 prefixEnd_5378567 := by exact prefixLift 5378567
  have htrace : WordTrace (prefixWord ++ tailWord_5378567) baseStart_5378567 baseEnd_5378567 := by
    simpa [prefixWord, tailWord_5378567, baseEnd_5378567] using wordTrace_append hprefix tailTrace_5378567
  have hstable : (prefixWord ++ tailWord_5378567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378567).length < 2 ^ (prefixWord ++ tailWord_5378567).sum := by decide
  have hdescent : baseEnd_5378567 < baseStart_5378567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378593 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 3, 4]
def baseStart_5378593 : Nat := 118140960795 + 5378593 * 2 ^ 59
def prefixEnd_5378593 : Nat := 4983230072969 + 3 ^ 40 * 5378593 * 2
def baseEnd_5378593 : Nat := 920601151302726654617269

theorem tailTrace_5378593 : CollatzResearch.WordTrace tailWord_5378593 prefixEnd_5378593 920601151302726654617269 := by
  unfold tailWord_5378593
  simp only [CollatzResearch.WordTrace]
  refine ⟨196173403003283626396780433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130782268668855750931186955 196173403003283626396780433)
  ·
    refine ⟨147130052252462719797585325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196173403003283626396780433 147130052252462719797585325)
    ·
      refine ⟨55173769594673519924094497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147130052252462719797585325 55173769594673519924094497)
      ·
        refine ⟨41380327196005139943070873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55173769594673519924094497 41380327196005139943070873)
        ·
          refine ⟨31035245397003854957303155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41380327196005139943070873 31035245397003854957303155)
          ·
            refine ⟨46552868095505782435954733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31035245397003854957303155 46552868095505782435954733)
            ·
              refine ⟨17457325535814668413483025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46552868095505782435954733 17457325535814668413483025)
              ·
                refine ⟨13092994151861001310112269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17457325535814668413483025 13092994151861001310112269)
                ·
                  refine ⟨4909872806947875491292101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13092994151861001310112269 4909872806947875491292101)
                  ·
                    refine ⟨920601151302726654617269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909872806947875491292101 920601151302726654617269)
                    ·
                      rfl

theorem cell23_5378593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_5378593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378593 prefixEnd_5378593 := by exact prefixLift 5378593
  have htrace : WordTrace (prefixWord ++ tailWord_5378593) baseStart_5378593 baseEnd_5378593 := by
    simpa [prefixWord, tailWord_5378593, baseEnd_5378593] using wordTrace_append hprefix tailTrace_5378593
  have hstable : (prefixWord ++ tailWord_5378593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378593).length < 2 ^ (prefixWord ++ tailWord_5378593).sum := by decide
  have hdescent : baseEnd_5378593 < baseStart_5378593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378600 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5378600 : Nat := 118140960795 + 5378600 * 2 ^ 59
def prefixEnd_5378600 : Nat := 4983230072969 + 3 ^ 40 * 5378600 * 2
def baseEnd_5378600 : Nat := 2761807048272761436464275

theorem tailTrace_5378600 : CollatzResearch.WordTrace tailWord_5378600 prefixEnd_5378600 2761807048272761436464275 := by
  unfold tailWord_5378600
  simp only [CollatzResearch.WordTrace]
  refine ⟨98086829157129133296142627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130782438876172177728190169 98086829157129133296142627)
  ·
    refine ⟨147130243735693699944213941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98086829157129133296142627 147130243735693699944213941)
    ·
      refine ⟨13793460350221284369770057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147130243735693699944213941 13793460350221284369770057)
      ·
        refine ⟨10345095262665963277327543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13793460350221284369770057 10345095262665963277327543)
        ·
          refine ⟨15517642893998944915991315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10345095262665963277327543 15517642893998944915991315)
          ·
            refine ⟨23276464340998417373986973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15517642893998944915991315 23276464340998417373986973)
            ·
              refine ⟨8728674127874406515245115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23276464340998417373986973 8728674127874406515245115)
              ·
                refine ⟨13093011191811609772867673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8728674127874406515245115 13093011191811609772867673)
                ·
                  refine ⟨9819758393858707329650755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13093011191811609772867673 9819758393858707329650755)
                  ·
                    refine ⟨14729637590788060994476133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9819758393858707329650755 14729637590788060994476133)
                    ·
                      refine ⟨2761807048272761436464275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14729637590788060994476133 2761807048272761436464275)
                      ·
                        rfl

theorem cell23_5378600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5378600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378600 prefixEnd_5378600 := by exact prefixLift 5378600
  have htrace : WordTrace (prefixWord ++ tailWord_5378600) baseStart_5378600 baseEnd_5378600 := by
    simpa [prefixWord, tailWord_5378600, baseEnd_5378600] using wordTrace_append hprefix tailTrace_5378600
  have hstable : (prefixWord ++ tailWord_5378600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378600).length < 2 ^ (prefixWord ++ tailWord_5378600).sum := by decide
  have hdescent : baseEnd_5378600 < baseStart_5378600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378610 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_5378610 : Nat := 118140960795 + 5378610 * 2 ^ 59
def prefixEnd_5378610 : Nat := 4983230072969 + 3 ^ 40 * 5378610 * 2
def baseEnd_5378610 : Nat := 920604061026435465779743

theorem tailTrace_5378610 : CollatzResearch.WordTrace tailWord_5378610 prefixEnd_5378610 920604061026435465779743 := by
  unfold tailWord_5378610
  simp only [CollatzResearch.WordTrace]
  refine ⟨49043505761055509575037321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130782682029481358866766189 49043505761055509575037321)
  ·
    refine ⟨36782629320791632181277991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49043505761055509575037321 36782629320791632181277991)
    ·
      refine ⟨55173943981187448271916987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36782629320791632181277991 55173943981187448271916987)
      ·
        refine ⟨82760915971781172407875481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55173943981187448271916987 82760915971781172407875481)
        ·
          refine ⟨62070686978835879305906611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82760915971781172407875481 62070686978835879305906611)
          ·
            refine ⟨93106030468253818958859917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62070686978835879305906611 93106030468253818958859917)
            ·
              refine ⟨34914761425595182109572469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93106030468253818958859917 34914761425595182109572469)
              ·
                refine ⟨3273258883649548322772419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34914761425595182109572469 3273258883649548322772419)
                ·
                  refine ⟨4909888325474322484158629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273258883649548322772419 4909888325474322484158629)
                  ·
                    refine ⟨920604061026435465779743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4909888325474322484158629 920604061026435465779743)
                    ·
                      rfl

theorem cell23_5378610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_5378610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378610 prefixEnd_5378610 := by exact prefixLift 5378610
  have htrace : WordTrace (prefixWord ++ tailWord_5378610) baseStart_5378610 baseEnd_5378610 := by
    simpa [prefixWord, tailWord_5378610, baseEnd_5378610] using wordTrace_append hprefix tailTrace_5378610
  have hstable : (prefixWord ++ tailWord_5378610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378610).length < 2 ^ (prefixWord ++ tailWord_5378610).sum := by decide
  have hdescent : baseEnd_5378610 < baseStart_5378610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378660 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_5378660 : Nat := 118140960795 + 5378660 * 2 ^ 59
def prefixEnd_5378660 : Nat := 4983230072969 + 3 ^ 40 * 5378660 * 2
def baseEnd_5378660 : Nat := 2761837857112031201713999

theorem tailTrace_5378660 : CollatzResearch.WordTrace tailWord_5378660 prefixEnd_5378660 2761837857112031201713999 := by
  unfold tailWord_5378660
  simp only [CollatzResearch.WordTrace]
  refine ⟨98087923347020448419734717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130783897796027264559646289 98087923347020448419734717)
  ·
    refine ⟨36782971255132668157400519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98087923347020448419734717 36782971255132668157400519)
    ·
      refine ⟨55174456882699002236100779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36782971255132668157400519 55174456882699002236100779)
      ·
        refine ⟨82761685324048503354151169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55174456882699002236100779 82761685324048503354151169)
        ·
          refine ⟨62071263993036377515613377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82761685324048503354151169 62071263993036377515613377)
          ·
            refine ⟨46553447994777283136710033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62071263993036377515613377 46553447994777283136710033)
            ·
              refine ⟨34915085996082962352532525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46553447994777283136710033 34915085996082962352532525)
              ·
                refine ⟨13093157248531110882199697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34915085996082962352532525 13093157248531110882199697)
                ·
                  refine ⟨9819867936398333161649773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13093157248531110882199697 9819867936398333161649773)
                  ·
                    refine ⟨3682450476149374935618665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9819867936398333161649773 3682450476149374935618665)
                    ·
                      refine ⟨2761837857112031201713999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682450476149374935618665 2761837857112031201713999)
                      ·
                        rfl

theorem cell23_5378660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_5378660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378660 prefixEnd_5378660 := by exact prefixLift 5378660
  have htrace : WordTrace (prefixWord ++ tailWord_5378660) baseStart_5378660 baseEnd_5378660 := by
    simpa [prefixWord, tailWord_5378660, baseEnd_5378660] using wordTrace_append hprefix tailTrace_5378660
  have hstable : (prefixWord ++ tailWord_5378660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378660).length < 2 ^ (prefixWord ++ tailWord_5378660).sum := by decide
  have hdescent : baseEnd_5378660 < baseStart_5378660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378670 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_5378670 : Nat := 118140960795 + 5378670 * 2 ^ 59
def prefixEnd_5378670 : Nat := 4983230072969 + 3 ^ 40 * 5378670 * 2
def baseEnd_5378670 : Nat := 920614330639525387529651

theorem tailTrace_5378670 : CollatzResearch.WordTrace tailWord_5378670 prefixEnd_5378670 920614330639525387529651 := by
  unfold tailWord_5378670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24522026428000583568416683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130784140949336445698222309 24522026428000583568416683)
  ·
    refine ⟨36783039642000875352625025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24522026428000583568416683 36783039642000875352625025)
    ·
      refine ⟨27587279731500656514468769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36783039642000875352625025 27587279731500656514468769)
      ·
        refine ⟨20690459798625492385851577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27587279731500656514468769 20690459798625492385851577)
        ·
          refine ⟨15517844848969119289388683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20690459798625492385851577 15517844848969119289388683)
          ·
            refine ⟨23276767273453678934083025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15517844848969119289388683 23276767273453678934083025)
            ·
              refine ⟨17457575455090259200562269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23276767273453678934083025 17457575455090259200562269)
              ·
                refine ⟨6546590795658847200210851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17457575455090259200562269 6546590795658847200210851)
                ·
                  refine ⟨9819886193488270800316277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6546590795658847200210851 9819886193488270800316277)
                  ·
                    refine ⟨920614330639525387529651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9819886193488270800316277 920614330639525387529651)
                    ·
                      rfl

theorem cell23_5378670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_5378670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378670 prefixEnd_5378670 := by exact prefixLift 5378670
  have htrace : WordTrace (prefixWord ++ tailWord_5378670) baseStart_5378670 baseEnd_5378670 := by
    simpa [prefixWord, tailWord_5378670, baseEnd_5378670] using wordTrace_append hprefix tailTrace_5378670
  have hstable : (prefixWord ++ tailWord_5378670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378670).length < 2 ^ (prefixWord ++ tailWord_5378670).sum := by decide
  have hdescent : baseEnd_5378670 < baseStart_5378670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378693 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_5378693 : Nat := 118140960795 + 5378693 * 2 ^ 59
def prefixEnd_5378693 : Nat := 4983230072969 + 3 ^ 40 * 5378693 * 2
def baseEnd_5378693 : Nat := 2761854801973629572601347

theorem tailTrace_5378693 : CollatzResearch.WordTrace tailWord_5378693 prefixEnd_5378693 2761854801973629572601347 := by
  unfold tailWord_5378693
  simp only [CollatzResearch.WordTrace]
  refine ⟨196177050302921343475420733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130784700201947562316947155 196177050302921343475420733)
  ·
    refine ⟨73566393863595503803282775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196177050302921343475420733 73566393863595503803282775)
    ·
      refine ⟨110349590795393255704924163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73566393863595503803282775 110349590795393255704924163)
      ·
        refine ⟨165524386193089883557386245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110349590795393255704924163 165524386193089883557386245)
        ·
          refine ⟨31035822411204353167009921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165524386193089883557386245 31035822411204353167009921)
          ·
            refine ⟨23276866808403264875257441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31035822411204353167009921 23276866808403264875257441)
            ·
              refine ⟨17457650106302448656443081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23276866808403264875257441 17457650106302448656443081)
              ·
                refine ⟨13093237579726836492332311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17457650106302448656443081 13093237579726836492332311)
                ·
                  refine ⟨19639856369590254738498467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13093237579726836492332311 19639856369590254738498467)
                  ·
                    refine ⟨29459784554385382107747701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19639856369590254738498467 29459784554385382107747701)
                    ·
                      refine ⟨2761854801973629572601347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29459784554385382107747701 2761854801973629572601347)
                      ·
                        rfl

theorem cell23_5378693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_5378693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378693 prefixEnd_5378693 := by exact prefixLift 5378693
  have htrace : WordTrace (prefixWord ++ tailWord_5378693) baseStart_5378693 baseEnd_5378693 := by
    simpa [prefixWord, tailWord_5378693, baseEnd_5378693] using wordTrace_append hprefix tailTrace_5378693
  have hstable : (prefixWord ++ tailWord_5378693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378693).length < 2 ^ (prefixWord ++ tailWord_5378693).sum := by decide
  have hdescent : baseEnd_5378693 < baseStart_5378693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378720 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_5378720 : Nat := 118140960795 + 5378720 * 2 ^ 59
def prefixEnd_5378720 : Nat := 4983230072969 + 3 ^ 40 * 5378720 * 2
def baseEnd_5378720 : Nat := 2761868665951300966963723

theorem tailTrace_5378720 : CollatzResearch.WordTrace tailWord_5378720 prefixEnd_5378720 2761868665951300966963723 := by
  unfold tailWord_5378720
  simp only [CollatzResearch.WordTrace]
  refine ⟨98089017536911763543326807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130785356715882351391102409 98089017536911763543326807)
  ·
    refine ⟨147133526305367645314990211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98089017536911763543326807 147133526305367645314990211)
    ·
      refine ⟨220700289458051467972485317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147133526305367645314990211 220700289458051467972485317)
      ·
        refine ⟨41381304273384650244840997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220700289458051467972485317 41381304273384650244840997)
        ·
          refine ⟨7758994551259621920907687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41381304273384650244840997 7758994551259621920907687)
          ·
            refine ⟨11638491826889432881361531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7758994551259621920907687 11638491826889432881361531)
            ·
              refine ⟨17457737740334149322042297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11638491826889432881361531 17457737740334149322042297)
              ·
                refine ⟨13093303305250611991531723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17457737740334149322042297 13093303305250611991531723)
                ·
                  refine ⟨19639954957875917987297585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13093303305250611991531723 19639954957875917987297585)
                  ·
                    refine ⟨14729966218406938490473189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19639954957875917987297585 14729966218406938490473189)
                    ·
                      refine ⟨2761868665951300966963723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14729966218406938490473189 2761868665951300966963723)
                      ·
                        rfl

theorem cell23_5378720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_5378720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378720 prefixEnd_5378720 := by exact prefixLift 5378720
  have htrace : WordTrace (prefixWord ++ tailWord_5378720) baseStart_5378720 baseEnd_5378720 := by
    simpa [prefixWord, tailWord_5378720, baseEnd_5378720] using wordTrace_append hprefix tailTrace_5378720
  have hstable : (prefixWord ++ tailWord_5378720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378720).length < 2 ^ (prefixWord ++ tailWord_5378720).sum := by decide
  have hdescent : baseEnd_5378720 < baseStart_5378720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378724 : List Nat := [2, 3, 1, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_5378724 : Nat := 118140960795 + 5378724 * 2 ^ 59
def prefixEnd_5378724 : Nat := 4983230072969 + 3 ^ 40 * 5378724 * 2
def baseEnd_5378724 : Nat := 2761870719873918951313705

theorem tailTrace_5378724 : CollatzResearch.WordTrace tailWord_5378724 prefixEnd_5378724 2761870719873918951313705 := by
  unfold tailWord_5378724
  simp only [CollatzResearch.WordTrace]
  refine ⟨98089090482904517884899613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130785453977206023846532817 98089090482904517884899613)
  ·
    refine ⟨36783408931089194206837355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98089090482904517884899613 36783408931089194206837355)
    ·
      refine ⟨55175113396633791310256033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36783408931089194206837355 55175113396633791310256033)
      ·
        refine ⟨41381335047475343482692025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55175113396633791310256033 41381335047475343482692025)
        ·
          refine ⟨31036001285606507612019019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41381335047475343482692025 31036001285606507612019019)
          ·
            refine ⟨46554001928409761418028529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31036001285606507612019019 46554001928409761418028529)
            ·
              refine ⟨34915501446307321063521397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46554001928409761418028529 34915501446307321063521397)
              ·
                refine ⟨3273328260591311349705131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34915501446307321063521397 3273328260591311349705131)
                ·
                  refine ⟨4909992390886967024557697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273328260591311349705131 4909992390886967024557697)
                  ·
                    refine ⟨3682494293165225268418273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4909992390886967024557697 3682494293165225268418273)
                    ·
                      refine ⟨2761870719873918951313705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682494293165225268418273 2761870719873918951313705)
                      ·
                        rfl

theorem cell23_5378724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_5378724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378724 prefixEnd_5378724 := by exact prefixLift 5378724
  have htrace : WordTrace (prefixWord ++ tailWord_5378724) baseStart_5378724 baseEnd_5378724 := by
    simpa [prefixWord, tailWord_5378724, baseEnd_5378724] using wordTrace_append hprefix tailTrace_5378724
  have hstable : (prefixWord ++ tailWord_5378724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378724).length < 2 ^ (prefixWord ++ tailWord_5378724).sum := by decide
  have hdescent : baseEnd_5378724 < baseStart_5378724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378730 : List Nat := [3, 1, 5, 2, 1, 11]
def baseStart_5378730 : Nat := 118140960795 + 5378730 * 2 ^ 59
def prefixEnd_5378730 : Nat := 4983230072969 + 3 ^ 40 * 5378730 * 2
def baseEnd_5378730 : Nat := 11365735805587843324439

theorem tailTrace_5378730 : CollatzResearch.WordTrace tailWord_5378730 prefixEnd_5378730 11365735805587843324439 := by
  unfold tailWord_5378730
  simp only [CollatzResearch.WordTrace]
  refine ⟨49044599950946824698629411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130785599869191532529678429 49044599950946824698629411)
  ·
    refine ⟨73566899926420237047944117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49044599950946824698629411 73566899926420237047944117)
    ·
      refine ⟨6896896868101897223244761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73566899926420237047944117 6896896868101897223244761)
      ·
        refine ⟨5172672651076422917433571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6896896868101897223244761 5172672651076422917433571)
        ·
          refine ⟨7759008976614634376150357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5172672651076422917433571 7759008976614634376150357)
          ·
            refine ⟨11365735805587843324439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7759008976614634376150357 11365735805587843324439)
            ·
              rfl

theorem cell23_5378730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 11].length) (baseStart_5378730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378730 prefixEnd_5378730 := by exact prefixLift 5378730
  have htrace : WordTrace (prefixWord ++ tailWord_5378730) baseStart_5378730 baseEnd_5378730 := by
    simpa [prefixWord, tailWord_5378730, baseEnd_5378730] using wordTrace_append hprefix tailTrace_5378730
  have hstable : (prefixWord ++ tailWord_5378730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378730).length < 2 ^ (prefixWord ++ tailWord_5378730).sum := by decide
  have hdescent : baseEnd_5378730 < baseStart_5378730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378734 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5378734 : Nat := 118140960795 + 5378734 * 2 ^ 59
def prefixEnd_5378734 : Nat := 4983230072969 + 3 ^ 40 * 5378734 * 2
def baseEnd_5378734 : Nat := 920625284893487970729553

theorem tailTrace_5378734 : CollatzResearch.WordTrace tailWord_5378734 prefixEnd_5378734 920625284893487970729553 := by
  unfold tailWord_5378734
  simp only [CollatzResearch.WordTrace]
  refine ⟨24522318211971600934707907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130785697130515204985108837 24522318211971600934707907)
  ·
    refine ⟨36783477317957401402061861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24522318211971600934707907 36783477317957401402061861)
    ·
      refine ⟨6896901997117012762886599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36783477317957401402061861 6896901997117012762886599)
      ·
        refine ⟨10345352995675519144329899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6896901997117012762886599 10345352995675519144329899)
        ·
          refine ⟨15518029493513278716494849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10345352995675519144329899 15518029493513278716494849)
          ·
            refine ⟨11638522120134959037371137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15518029493513278716494849 11638522120134959037371137)
            ·
              refine ⟨8728891590101219278028353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11638522120134959037371137 8728891590101219278028353)
              ·
                refine ⟨6546668692575914458521265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8728891590101219278028353 6546668692575914458521265)
                ·
                  refine ⟨4910001519431935843890949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6546668692575914458521265 4910001519431935843890949)
                  ·
                    refine ⟨920625284893487970729553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910001519431935843890949 920625284893487970729553)
                    ·
                      rfl

theorem cell23_5378734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5378734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378734 prefixEnd_5378734 := by exact prefixLift 5378734
  have htrace : WordTrace (prefixWord ++ tailWord_5378734) baseStart_5378734 baseEnd_5378734 := by
    simpa [prefixWord, tailWord_5378734, baseEnd_5378734] using wordTrace_append hprefix tailTrace_5378734
  have hstable : (prefixWord ++ tailWord_5378734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378734).length < 2 ^ (prefixWord ++ tailWord_5378734).sum := by decide
  have hdescent : baseEnd_5378734 < baseStart_5378734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378741 : List Nat := [1, 3, 3, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5378741 : Nat := 118140960795 + 5378741 * 2 ^ 59
def prefixEnd_5378741 : Nat := 4983230072969 + 3 ^ 40 * 5378741 * 2
def baseEnd_5378741 : Nat := 2761879449045045384801127

theorem tailTrace_5378741 : CollatzResearch.WordTrace tailWord_5378741 prefixEnd_5378741 2761879449045045384801127 := by
  unfold tailWord_5378741
  simp only [CollatzResearch.WordTrace]
  refine ⟨196178801006747447673168077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130785867337831631782112051 196178801006747447673168077)
  ·
    refine ⟨73567050377530292877438029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196178801006747447673168077 73567050377530292877438029)
    ·
      refine ⟨27587643891573859829039261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73567050377530292877438029 27587643891573859829039261)
      ·
        refine ⟨10345366459340197435889723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27587643891573859829039261 10345366459340197435889723)
        ·
          refine ⟨15518049689010296153834585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10345366459340197435889723 15518049689010296153834585)
          ·
            refine ⟨11638537266757722115375939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15518049689010296153834585 11638537266757722115375939)
            ·
              refine ⟨17457805900136583173063909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11638537266757722115375939 17457805900136583173063909)
              ·
                refine ⟨3273338606275609344949483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17457805900136583173063909 3273338606275609344949483)
                ·
                  refine ⟨4910007909413414017424225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273338606275609344949483 4910007909413414017424225)
                  ·
                    refine ⟨3682505932060060513068169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4910007909413414017424225 3682505932060060513068169)
                    ·
                      refine ⟨2761879449045045384801127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682505932060060513068169 2761879449045045384801127)
                      ·
                        rfl

theorem cell23_5378741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5378741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378741 prefixEnd_5378741 := by exact prefixLift 5378741
  have htrace : WordTrace (prefixWord ++ tailWord_5378741) baseStart_5378741 baseEnd_5378741 := by
    simpa [prefixWord, tailWord_5378741, baseEnd_5378741] using wordTrace_append hprefix tailTrace_5378741
  have hstable : (prefixWord ++ tailWord_5378741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378741).length < 2 ^ (prefixWord ++ tailWord_5378741).sum := by decide
  have hdescent : baseEnd_5378741 < baseStart_5378741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378758 : List Nat := [6, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5378758 : Nat := 118140960795 + 5378758 * 2 ^ 59
def prefixEnd_5378758 : Nat := 4983230072969 + 3 ^ 40 * 5378758 * 2
def baseEnd_5378758 : Nat := 2761888178216171818288549

theorem tailTrace_5378758 : CollatzResearch.WordTrace tailWord_5378758 prefixEnd_5378758 2761888178216171818288549 := by
  unfold tailWord_5378758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6130606907740183111766779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130786280698457239717691285 6130606907740183111766779)
  ·
    refine ⟨9195910361610274667650169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6130606907740183111766779 9195910361610274667650169)
    ·
      refine ⟨6896932771207706000737627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9195910361610274667650169 6896932771207706000737627)
      ·
        refine ⟨10345399156811559001106441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6896932771207706000737627 10345399156811559001106441)
        ·
          refine ⟨7759049367608669250829831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10345399156811559001106441 7759049367608669250829831)
          ·
            refine ⟨11638574051413003876244747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7759049367608669250829831 11638574051413003876244747)
            ·
              refine ⟨17457861077119505814367121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11638574051413003876244747 17457861077119505814367121)
              ·
                refine ⟨13093395807839629360775341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17457861077119505814367121 13093395807839629360775341)
                ·
                  refine ⟨4910023427939861010290753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13093395807839629360775341 4910023427939861010290753)
                  ·
                    refine ⟨3682517570954895757718065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4910023427939861010290753 3682517570954895757718065)
                    ·
                      refine ⟨2761888178216171818288549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682517570954895757718065 2761888178216171818288549)
                      ·
                        rfl

theorem cell23_5378758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5378758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378758 prefixEnd_5378758 := by exact prefixLift 5378758
  have htrace : WordTrace (prefixWord ++ tailWord_5378758) baseStart_5378758 baseEnd_5378758 := by
    simpa [prefixWord, tailWord_5378758, baseEnd_5378758] using wordTrace_append hprefix tailTrace_5378758
  have hstable : (prefixWord ++ tailWord_5378758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378758).length < 2 ^ (prefixWord ++ tailWord_5378758).sum := by decide
  have hdescent : baseEnd_5378758 < baseStart_5378758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378793 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_5378793 : Nat := 118140960795 + 5378793 * 2 ^ 59
def prefixEnd_5378793 : Nat := 4983230072969 + 3 ^ 40 * 5378793 * 2
def baseEnd_5378793 : Nat := 2761906150039079181350887

theorem tailTrace_5378793 : CollatzResearch.WordTrace tailWord_5378793 prefixEnd_5378793 2761906150039079181350887 := by
  unfold tailWord_5378793
  simp only [CollatzResearch.WordTrace]
  refine ⟨196180697602559060554061033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130787131735039373702707355 196180697602559060554061033)
  ·
    refine ⟨147135523201919295415545775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196180697602559060554061033 147135523201919295415545775)
    ·
      refine ⟨220703284802878943123318663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147135523201919295415545775 220703284802878943123318663)
      ·
        refine ⟨331054927204318414684977995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220703284802878943123318663 331054927204318414684977995)
        ·
          refine ⟨496582390806477622027466993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331054927204318414684977995 496582390806477622027466993)
          ·
            refine ⟨372436793104858216520600245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496582390806477622027466993 372436793104858216520600245)
            ·
              refine ⟨34915949353580457798806273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372436793104858216520600245 34915949353580457798806273)
              ·
                refine ⟨26186962015185343349104705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34915949353580457798806273 26186962015185343349104705)
                ·
                  refine ⟨19640221511389007511828529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26186962015185343349104705 19640221511389007511828529)
                  ·
                    refine ⟨14730166133541755633871397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19640221511389007511828529 14730166133541755633871397)
                    ·
                      refine ⟨2761906150039079181350887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14730166133541755633871397 2761906150039079181350887)
                      ·
                        rfl

theorem cell23_5378793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_5378793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378793 prefixEnd_5378793 := by exact prefixLift 5378793
  have htrace : WordTrace (prefixWord ++ tailWord_5378793) baseStart_5378793 baseEnd_5378793 := by
    simpa [prefixWord, tailWord_5378793, baseEnd_5378793] using wordTrace_append hprefix tailTrace_5378793
  have hstable : (prefixWord ++ tailWord_5378793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378793).length < 2 ^ (prefixWord ++ tailWord_5378793).sum := by decide
  have hdescent : baseEnd_5378793 < baseStart_5378793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378814 : List Nat := [4, 2, 2, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_5378814 : Nat := 118140960795 + 5378814 * 2 ^ 59
def prefixEnd_5378814 : Nat := 4983230072969 + 3 ^ 40 * 5378814 * 2
def baseEnd_5378814 : Nat := 2761916933132823599188291

theorem tailTrace_5378814 : CollatzResearch.WordTrace tailWord_5378814 prefixEnd_5378814 2761916933132823599188291 := by
  unfold tailWord_5378814
  simp only [CollatzResearch.WordTrace]
  refine ⟨24522682941935372642571937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130787642356988654093716997 24522682941935372642571937)
  ·
    refine ⟨18392012206451529481928953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24522682941935372642571937 18392012206451529481928953)
    ·
      refine ⟨13794009154838647111446715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18392012206451529481928953 13794009154838647111446715)
      ·
        refine ⟨20691013732257970667170073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13794009154838647111446715 20691013732257970667170073)
        ·
          refine ⟨15518260299193478000377555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20691013732257970667170073 15518260299193478000377555)
          ·
            refine ⟨23277390448790217000566333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15518260299193478000377555 23277390448790217000566333)
            ·
              refine ⟨8729021418296331375212375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23277390448790217000566333 8729021418296331375212375)
              ·
                refine ⟨13093532127444497062818563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729021418296331375212375 13093532127444497062818563)
                ·
                  refine ⟨19640298191166745594227845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13093532127444497062818563 19640298191166745594227845)
                  ·
                    refine ⟨3682555910843764798917721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19640298191166745594227845 3682555910843764798917721)
                    ·
                      refine ⟨2761916933132823599188291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682555910843764798917721 2761916933132823599188291)
                      ·
                        rfl

theorem cell23_5378814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_5378814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378814 prefixEnd_5378814 := by exact prefixLift 5378814
  have htrace : WordTrace (prefixWord ++ tailWord_5378814) baseStart_5378814 baseEnd_5378814 := by
    simpa [prefixWord, tailWord_5378814, baseEnd_5378814] using wordTrace_append hprefix tailTrace_5378814
  have hstable : (prefixWord ++ tailWord_5378814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378814).length < 2 ^ (prefixWord ++ tailWord_5378814).sum := by decide
  have hdescent : baseEnd_5378814 < baseStart_5378814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378833 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 1, 7]
def baseStart_5378833 : Nat := 118140960795 + 5378833 * 2 ^ 59
def prefixEnd_5378833 : Nat := 4983230072969 + 3 ^ 40 * 5378833 * 2
def baseEnd_5378833 : Nat := 920642229755086341616901

theorem tailTrace_5378833 : CollatzResearch.WordTrace tailWord_5378833 prefixEnd_5378833 920642229755086341616901 := by
  unfold tailWord_5378833
  simp only [CollatzResearch.WordTrace]
  refine ⟨196182156522414147385517153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130788104348276098257011435 196182156522414147385517153)
  ·
    refine ⟨147136617391810610539137865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196182156522414147385517153 147136617391810610539137865)
    ·
      refine ⟨110352463043857957904353399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147136617391810610539137865 110352463043857957904353399)
      ·
        refine ⟨165528694565786936856530099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110352463043857957904353399 165528694565786936856530099)
        ·
          refine ⟨248293041848680405284795149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165528694565786936856530099 248293041848680405284795149)
          ·
            refine ⟨93109890693255151981798181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248293041848680405284795149 93109890693255151981798181)
            ·
              refine ⟨17458104504985340996587159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93109890693255151981798181 17458104504985340996587159)
              ·
                refine ⟨26187156757478011494880739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17458104504985340996587159 26187156757478011494880739)
                ·
                  refine ⟨39280735136217017242321109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26187156757478011494880739 39280735136217017242321109)
                  ·
                    refine ⟨920642229755086341616901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39280735136217017242321109 920642229755086341616901)
                    ·
                      rfl

theorem cell23_5378833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_5378833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378833 prefixEnd_5378833 := by exact prefixLift 5378833
  have htrace : WordTrace (prefixWord ++ tailWord_5378833) baseStart_5378833 baseEnd_5378833 := by
    simpa [prefixWord, tailWord_5378833, baseEnd_5378833] using wordTrace_append hprefix tailTrace_5378833
  have hstable : (prefixWord ++ tailWord_5378833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378833).length < 2 ^ (prefixWord ++ tailWord_5378833).sum := by decide
  have hdescent : baseEnd_5378833 < baseStart_5378833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378840 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 7, 2]
def baseStart_5378840 : Nat := 118140960795 + 5378840 * 2 ^ 59
def prefixEnd_5378840 : Nat := 4983230072969 + 3 ^ 40 * 5378840 * 2
def baseEnd_5378840 : Nat := 2761930283629840497463171

theorem tailTrace_5378840 : CollatzResearch.WordTrace tailWord_5378840 prefixEnd_5378840 2761930283629840497463171 := by
  unfold tailWord_5378840
  simp only [CollatzResearch.WordTrace]
  refine ⟨98091205916694393790510987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130788274555592525054014649 98091205916694393790510987)
  ·
    refine ⟨147136808875041590685766481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98091205916694393790510987 147136808875041590685766481)
    ·
      refine ⟨110352606656281193014324861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147136808875041590685766481 110352606656281193014324861)
      ·
        refine ⟨41382227496105447380371823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110352606656281193014324861 41382227496105447380371823)
        ·
          refine ⟨62073341244158171070557735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41382227496105447380371823 62073341244158171070557735)
          ·
            refine ⟨93110011866237256605836603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62073341244158171070557735 93110011866237256605836603)
            ·
              refine ⟨139665017799355884908754905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93110011866237256605836603 139665017799355884908754905)
              ·
                refine ⟨104748763349516913681566179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139665017799355884908754905 104748763349516913681566179)
                ·
                  refine ⟨157123145024275370522349269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104748763349516913681566179 157123145024275370522349269)
                  ·
                    refine ⟨3682573711506453996617561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 157123145024275370522349269 3682573711506453996617561)
                    ·
                      refine ⟨2761930283629840497463171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682573711506453996617561 2761930283629840497463171)
                      ·
                        rfl

theorem cell23_5378840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_5378840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378840 prefixEnd_5378840 := by exact prefixLift 5378840
  have htrace : WordTrace (prefixWord ++ tailWord_5378840) baseStart_5378840 baseEnd_5378840 := by
    simpa [prefixWord, tailWord_5378840, baseEnd_5378840] using wordTrace_append hprefix tailTrace_5378840
  have hstable : (prefixWord ++ tailWord_5378840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378840).length < 2 ^ (prefixWord ++ tailWord_5378840).sum := by decide
  have hdescent : baseEnd_5378840 < baseStart_5378840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378850 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5378850 : Nat := 118140960795 + 5378850 * 2 ^ 59
def prefixEnd_5378850 : Nat := 4983230072969 + 3 ^ 40 * 5378850 * 2
def baseEnd_5378850 : Nat := 920645139478795152779375

theorem tailTrace_5378850 : CollatzResearch.WordTrace tailWord_5378850 prefixEnd_5378850 920645139478795152779375 := by
  unfold tailWord_5378850
  simp only [CollatzResearch.WordTrace]
  refine ⟨49045694140838139822221501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130788517708901706192590669 49045694140838139822221501)
  ·
    refine ⟨18392135302814302433333063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49045694140838139822221501 18392135302814302433333063)
    ·
      refine ⟨27588202954221453649999595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18392135302814302433333063 27588202954221453649999595)
      ·
        refine ⟨41382304431332180474999393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27588202954221453649999595 41382304431332180474999393)
        ·
          refine ⟨31036728323499135356249545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41382304431332180474999393 31036728323499135356249545)
          ·
            refine ⟨23277546242624351517187159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31036728323499135356249545 23277546242624351517187159)
            ·
              refine ⟨34916319363936527275780739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23277546242624351517187159 34916319363936527275780739)
              ·
                refine ⟨52374479045904790913671109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34916319363936527275780739 52374479045904790913671109)
                ·
                  refine ⟨9820214821107148296313333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52374479045904790913671109 9820214821107148296313333)
                  ·
                    refine ⟨920645139478795152779375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9820214821107148296313333 920645139478795152779375)
                    ·
                      rfl

theorem cell23_5378850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5378850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378850 prefixEnd_5378850 := by exact prefixLift 5378850
  have htrace : WordTrace (prefixWord ++ tailWord_5378850) baseStart_5378850 baseEnd_5378850 := by
    simpa [prefixWord, tailWord_5378850, baseEnd_5378850] using wordTrace_append hprefix tailTrace_5378850
  have hstable : (prefixWord ++ tailWord_5378850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378850).length < 2 ^ (prefixWord ++ tailWord_5378850).sum := by decide
  have hdescent : baseEnd_5378850 < baseStart_5378850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378880 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 3, 4]
def baseStart_5378880 : Nat := 118140960795 + 5378880 * 2 ^ 59
def prefixEnd_5378880 : Nat := 4983230072969 + 3 ^ 40 * 5378880 * 2
def baseEnd_5378880 : Nat := 920650274285340113654329

theorem tailTrace_5378880 : CollatzResearch.WordTrace tailWord_5378880 prefixEnd_5378880 920650274285340113654329 := by
  unfold tailWord_5378880
  simp only [CollatzResearch.WordTrace]
  refine ⟨98091935376621937206239047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130789247168829249608318729 98091935376621937206239047)
  ·
    refine ⟨147137903064932905809358571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98091935376621937206239047 147137903064932905809358571)
    ·
      refine ⟨220706854597399358714037857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147137903064932905809358571 220706854597399358714037857)
      ·
        refine ⟨165530140948049519035528393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220706854597399358714037857 165530140948049519035528393)
        ·
          refine ⟨124147605711037139276646295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165530140948049519035528393 124147605711037139276646295)
          ·
            refine ⟨186221408566555708914969443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124147605711037139276646295 186221408566555708914969443)
            ·
              refine ⟨279332112849833563372454165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186221408566555708914969443 279332112849833563372454165)
              ·
                refine ⟨13093692789835948283083789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279332112849833563372454165 13093692789835948283083789)
                ·
                  refine ⟨4910134796188480606156421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13093692789835948283083789 4910134796188480606156421)
                  ·
                    refine ⟨920650274285340113654329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910134796188480606156421 920650274285340113654329)
                    ·
                      rfl

theorem cell23_5378880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_5378880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378880 prefixEnd_5378880 := by exact prefixLift 5378880
  have htrace : WordTrace (prefixWord ++ tailWord_5378880) baseStart_5378880 baseEnd_5378880 := by
    simpa [prefixWord, tailWord_5378880, baseEnd_5378880] using wordTrace_append hprefix tailTrace_5378880
  have hstable : (prefixWord ++ tailWord_5378880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378880).length < 2 ^ (prefixWord ++ tailWord_5378880).sum := by decide
  have hdescent : baseEnd_5378880 < baseStart_5378880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378937 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 3]
def baseStart_5378937 : Nat := 118140960795 + 5378937 * 2 ^ 59
def prefixEnd_5378937 : Nat := 4983230072969 + 3 ^ 40 * 5378937 * 2
def baseEnd_5378937 : Nat := 2761980091253326617950225

theorem tailTrace_5378937 : CollatzResearch.WordTrace tailWord_5378937 prefixEnd_5378937 2761980091253326617950225 := by
  unfold tailWord_5378937
  simp only [CollatzResearch.WordTrace]
  refine ⟨196185949714037373147303065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130790633142691582098202043 196185949714037373147303065)
  ·
    refine ⟨147139462285528029860477299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196185949714037373147303065 147139462285528029860477299)
    ·
      refine ⟨220709193428292044790715949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147139462285528029860477299 220709193428292044790715949)
      ·
        refine ⟨82765947535609516796518481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220709193428292044790715949 82765947535609516796518481)
        ·
          refine ⟨62074460651707137597388861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82765947535609516796518481 62074460651707137597388861)
          ·
            refine ⟨23277922744390176599020823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62074460651707137597388861 23277922744390176599020823)
            ·
              refine ⟨34916884116585264898531235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23277922744390176599020823 34916884116585264898531235)
              ·
                refine ⟨52375326174877897347796853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34916884116585264898531235 52375326174877897347796853)
                ·
                  refine ⟨4910186828894802876355955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52375326174877897347796853 4910186828894802876355955)
                  ·
                    refine ⟨7365280243342204314533933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4910186828894802876355955 7365280243342204314533933)
                    ·
                      refine ⟨2761980091253326617950225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7365280243342204314533933 2761980091253326617950225)
                      ·
                        rfl

theorem cell23_5378937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_5378937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378937 prefixEnd_5378937 := by exact prefixLift 5378937
  have htrace : WordTrace (prefixWord ++ tailWord_5378937) baseStart_5378937 baseEnd_5378937 := by
    simpa [prefixWord, tailWord_5378937, baseEnd_5378937] using wordTrace_append hprefix tailTrace_5378937
  have hstable : (prefixWord ++ tailWord_5378937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378937).length < 2 ^ (prefixWord ++ tailWord_5378937).sum := by decide
  have hdescent : baseEnd_5378937 < baseStart_5378937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378947 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 1, 5, 2]
def baseStart_5378947 : Nat := 118140960795 + 5378947 * 2 ^ 59
def prefixEnd_5378947 : Nat := 4983230072969 + 3 ^ 40 * 5378947 * 2
def baseEnd_5378947 : Nat := 2761985226059871578825179

theorem tailTrace_5378947 : CollatzResearch.WordTrace tailWord_5378947 prefixEnd_5378947 2761985226059871578825179 := by
  unfold tailWord_5378947
  simp only [CollatzResearch.WordTrace]
  refine ⟨196186314444001144855167095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130790876296000763236778063 196186314444001144855167095)
  ·
    refine ⟨294279471666001717282750643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196186314444001144855167095 294279471666001717282750643)
    ·
      refine ⟨441419207499002575924125965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294279471666001717282750643 441419207499002575924125965)
      ·
        refine ⟨165532202812125965971547237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441419207499002575924125965 165532202812125965971547237)
        ·
          refine ⟨31037288027273618619665107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165532202812125965971547237 31037288027273618619665107)
          ·
            refine ⟨46555932040910427929497661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31037288027273618619665107 46555932040910427929497661)
            ·
              refine ⟨17458474515341410473561623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46555932040910427929497661 17458474515341410473561623)
              ·
                refine ⟨26187711773012115710342435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17458474515341410473561623 26187711773012115710342435)
                ·
                  refine ⟨39281567659518173565513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26187711773012115710342435 39281567659518173565513653)
                  ·
                    refine ⟨3682646968079828771766905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39281567659518173565513653 3682646968079828771766905)
                    ·
                      refine ⟨2761985226059871578825179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682646968079828771766905 2761985226059871578825179)
                      ·
                        rfl

theorem cell23_5378947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_5378947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378947 prefixEnd_5378947 := by exact prefixLift 5378947
  have htrace : WordTrace (prefixWord ++ tailWord_5378947) baseStart_5378947 baseEnd_5378947 := by
    simpa [prefixWord, tailWord_5378947, baseEnd_5378947] using wordTrace_append hprefix tailTrace_5378947
  have hstable : (prefixWord ++ tailWord_5378947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378947).length < 2 ^ (prefixWord ++ tailWord_5378947).sum := by decide
  have hdescent : baseEnd_5378947 < baseStart_5378947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5378964 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5378964 : Nat := 118140960795 + 5378964 * 2 ^ 59
def prefixEnd_5378964 : Nat := 4983230072969 + 3 ^ 40 * 5378964 * 2
def baseEnd_5378964 : Nat := 2761993955230998012312601

theorem tailTrace_5378964 : CollatzResearch.WordTrace tailWord_5378964 prefixEnd_5378964 2761993955230998012312601 := by
  unfold tailWord_5378964
  simp only [CollatzResearch.WordTrace]
  refine ⟨98093467242469778379267973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130791289656626371172357297 98093467242469778379267973)
  ·
    refine ⟨18392525107963083446112745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98093467242469778379267973 18392525107963083446112745)
    ·
      refine ⟨13794393830972312584584559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18392525107963083446112745 13794393830972312584584559)
      ·
        refine ⟨20691590746458468876876839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13794393830972312584584559 20691590746458468876876839)
        ·
          refine ⟨31037386119687703315315259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20691590746458468876876839 31037386119687703315315259)
          ·
            refine ⟨46556079179531554972972889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31037386119687703315315259 46556079179531554972972889)
            ·
              refine ⟨34917059384648666229729667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46556079179531554972972889 34917059384648666229729667)
              ·
                refine ⟨52375589076972999344594501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34917059384648666229729667 52375589076972999344594501)
                ·
                  refine ⟨9820422951932437377111469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52375589076972999344594501 9820422951932437377111469)
                  ·
                    refine ⟨3682658606974664016416801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9820422951932437377111469 3682658606974664016416801)
                    ·
                      refine ⟨2761993955230998012312601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682658606974664016416801 2761993955230998012312601)
                      ·
                        rfl

theorem cell23_5378964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5378964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5378964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5378964 prefixEnd_5378964 := by exact prefixLift 5378964
  have htrace : WordTrace (prefixWord ++ tailWord_5378964) baseStart_5378964 baseEnd_5378964 := by
    simpa [prefixWord, tailWord_5378964, baseEnd_5378964] using wordTrace_append hprefix tailTrace_5378964
  have hstable : (prefixWord ++ tailWord_5378964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5378964).length < 2 ^ (prefixWord ++ tailWord_5378964).sum := by decide
  have hdescent : baseEnd_5378964 < baseStart_5378964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5378964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379000 : List Nat := [2, 1, 2, 1, 2, 5, 1, 9]
def baseStart_5379000 : Nat := 118140960795 + 5379000 * 2 ^ 59
def prefixEnd_5379000 : Nat := 4983230072969 + 3 ^ 40 * 5379000 * 2
def baseEnd_5379000 : Nat := 102296757056835550794905

theorem tailTrace_5379000 : CollatzResearch.WordTrace tailWord_5379000 prefixEnd_5379000 102296757056835550794905 := by
  unfold tailWord_5379000
  simp only [CollatzResearch.WordTrace]
  refine ⟨98094123756404567453423227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130792165008539423271230969 98094123756404567453423227)
  ·
    refine ⟨147141185634606851180134841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98094123756404567453423227 147141185634606851180134841)
    ·
      refine ⟨110355889225955138385101131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147141185634606851180134841 110355889225955138385101131)
      ·
        refine ⟨165533833838932707577651697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110355889225955138385101131 165533833838932707577651697)
        ·
          refine ⟨124150375379199530683238773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165533833838932707577651697 124150375379199530683238773)
          ·
            refine ⟨11639097691799956001553635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124150375379199530683238773 11639097691799956001553635)
            ·
              refine ⟨17458646537699934002330453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11639097691799956001553635 17458646537699934002330453)
              ·
                refine ⟨102296757056835550794905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17458646537699934002330453 102296757056835550794905)
                ·
                  rfl

theorem cell23_5379000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 9].length) (baseStart_5379000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379000 prefixEnd_5379000 := by exact prefixLift 5379000
  have htrace : WordTrace (prefixWord ++ tailWord_5379000) baseStart_5379000 baseEnd_5379000 := by
    simpa [prefixWord, tailWord_5379000, baseEnd_5379000] using wordTrace_append hprefix tailTrace_5379000
  have hstable : (prefixWord ++ tailWord_5379000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379000).length < 2 ^ (prefixWord ++ tailWord_5379000).sum := by decide
  have hdescent : baseEnd_5379000 < baseStart_5379000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379005 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_5379005 : Nat := 118140960795 + 5379005 * 2 ^ 59
def prefixEnd_5379005 : Nat := 4983230072969 + 3 ^ 40 * 5379005 * 2
def baseEnd_5379005 : Nat := 2762015007937832351899913

theorem tailTrace_5379005 : CollatzResearch.WordTrace tailWord_5379005 prefixEnd_5379005 2762015007937832351899913 := by
  unfold tailWord_5379005
  simp only [CollatzResearch.WordTrace]
  refine ⟨196188429877791020760778469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130792286585194013840518979 196188429877791020760778469)
  ·
    refine ⟨36785330602085816392645963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196188429877791020760778469 36785330602085816392645963)
    ·
      refine ⟨55177995903128724588968945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36785330602085816392645963 55177995903128724588968945)
      ·
        refine ⟨41383496927346543441726709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55177995903128724588968945 41383496927346543441726709)
        ·
          refine ⟨3879702836938738447661879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41383496927346543441726709 3879702836938738447661879)
          ·
            refine ⟨5819554255408107671492819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3879702836938738447661879 5819554255408107671492819)
            ·
              refine ⟨8729331383112161507239229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819554255408107671492819 8729331383112161507239229)
              ·
                refine ⟨3273499268667060565214711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8729331383112161507239229 3273499268667060565214711)
                ·
                  refine ⟨4910248903000590847822067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273499268667060565214711 4910248903000590847822067)
                  ·
                    refine ⟨7365373354500886271733101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4910248903000590847822067 7365373354500886271733101)
                    ·
                      refine ⟨2762015007937832351899913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7365373354500886271733101 2762015007937832351899913)
                      ·
                        rfl

theorem cell23_5379005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_5379005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379005 prefixEnd_5379005 := by exact prefixLift 5379005
  have htrace : WordTrace (prefixWord ++ tailWord_5379005) baseStart_5379005 baseEnd_5379005 := by
    simpa [prefixWord, tailWord_5379005, baseEnd_5379005] using wordTrace_append hprefix tailTrace_5379005
  have hstable : (prefixWord ++ tailWord_5379005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379005).length < 2 ^ (prefixWord ++ tailWord_5379005).sum := by decide
  have hdescent : baseEnd_5379005 < baseStart_5379005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379028 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_5379028 : Nat := 118140960795 + 5379028 * 2 ^ 59
def prefixEnd_5379028 : Nat := 4983230072969 + 3 ^ 40 * 5379028 * 2
def baseEnd_5379028 : Nat := 2762026817992885761912307

theorem tailTrace_5379028 : CollatzResearch.WordTrace tailWord_5379028 prefixEnd_5379028 2762026817992885761912307 := by
  unfold tailWord_5379028
  simp only [CollatzResearch.WordTrace]
  refine ⟨98094634378353847844432869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130792845837805130459243825 98094634378353847844432869)
  ·
    refine ⟨18392743945941346470831163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98094634378353847844432869 18392743945941346470831163)
    ·
      refine ⟨27589115918912019706246745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18392743945941346470831163 27589115918912019706246745)
      ·
        refine ⟨20691836939184014779685059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27589115918912019706246745 20691836939184014779685059)
        ·
          refine ⟨31037755408776022169527589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20691836939184014779685059 31037755408776022169527589)
          ·
            refine ⟨5819579139145504156786423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31037755408776022169527589 5819579139145504156786423)
            ·
              refine ⟨8729368708718256235179635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819579139145504156786423 8729368708718256235179635)
              ·
                refine ⟨13094053063077384352769453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729368708718256235179635 13094053063077384352769453)
                ·
                  refine ⟨4910269898654019132288545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13094053063077384352769453 4910269898654019132288545)
                  ·
                    refine ⟨3682702423990514349216409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4910269898654019132288545 3682702423990514349216409)
                    ·
                      refine ⟨2762026817992885761912307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682702423990514349216409 2762026817992885761912307)
                      ·
                        rfl

theorem cell23_5379028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_5379028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379028 prefixEnd_5379028 := by exact prefixLift 5379028
  have htrace : WordTrace (prefixWord ++ tailWord_5379028) baseStart_5379028 baseEnd_5379028 := by
    simpa [prefixWord, tailWord_5379028, baseEnd_5379028] using wordTrace_append hprefix tailTrace_5379028
  have hstable : (prefixWord ++ tailWord_5379028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379028).length < 2 ^ (prefixWord ++ tailWord_5379028).sum := by decide
  have hdescent : baseEnd_5379028 < baseStart_5379028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379107 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 7]
def baseStart_5379107 : Nat := 118140960795 + 5379107 * 2 ^ 59
def prefixEnd_5379107 : Nat := 4983230072969 + 3 ^ 40 * 5379107 * 2
def baseEnd_5379107 : Nat := 306896375884954550313827

theorem tailTrace_5379107 : CollatzResearch.WordTrace tailWord_5379107 prefixEnd_5379107 306896375884954550313827 := by
  unfold tailWord_5379107
  simp only [CollatzResearch.WordTrace]
  refine ⟨196192150123421492180991575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130794766748947661453994383 196192150123421492180991575)
  ·
    refine ⟨294288225185132238271487363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196192150123421492180991575 294288225185132238271487363)
    ·
      refine ⟨441432337777698357407231045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294288225185132238271487363 441432337777698357407231045)
      ·
        refine ⟨82768563333318442013855821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441432337777698357407231045 82768563333318442013855821)
        ·
          refine ⟨31038211249994415755195933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82768563333318442013855821 31038211249994415755195933)
          ·
            refine ⟨11639329218747905908198475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31038211249994415755195933 11639329218747905908198475)
            ·
              refine ⟨17458993828121858862297713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11639329218747905908198475 17458993828121858862297713)
              ·
                refine ⟨13094245371091394146723285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17458993828121858862297713 13094245371091394146723285)
                ·
                  refine ⟨306896375884954550313827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13094245371091394146723285 306896375884954550313827)
                  ·
                    rfl

theorem cell23_5379107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 7].length) (baseStart_5379107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379107 prefixEnd_5379107 := by exact prefixLift 5379107
  have htrace : WordTrace (prefixWord ++ tailWord_5379107) baseStart_5379107 baseEnd_5379107 := by
    simpa [prefixWord, tailWord_5379107, baseEnd_5379107] using wordTrace_append hprefix tailTrace_5379107
  have hstable : (prefixWord ++ tailWord_5379107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379107).length < 2 ^ (prefixWord ++ tailWord_5379107).sum := by decide
  have hdescent : baseEnd_5379107 < baseStart_5379107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379157 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5379157 : Nat := 118140960795 + 5379157 * 2 ^ 59
def prefixEnd_5379157 : Nat := 4983230072969 + 3 ^ 40 * 5379157 * 2
def baseEnd_5379157 : Nat := 2762093056997315757199213

theorem tailTrace_5379157 : CollatzResearch.WordTrace tailWord_5379157 prefixEnd_5379157 2762093056997315757199213 := by
  unfold tailWord_5379157
  simp only [CollatzResearch.WordTrace]
  refine ⟨196193973773240350720311725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130795982515493567146874483 196193973773240350720311725)
  ·
    refine ⟨73572740164965131520116897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196193973773240350720311725 73572740164965131520116897)
    ·
      refine ⟨55179555123723848640087673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73572740164965131520116897 55179555123723848640087673)
      ·
        refine ⟨41384666342792886480065755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55179555123723848640087673 41384666342792886480065755)
        ·
          refine ⟨62076999514189329720098633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41384666342792886480065755 62076999514189329720098633)
          ·
            refine ⟨46557749635641997290073975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62076999514189329720098633 46557749635641997290073975)
            ·
              refine ⟨69836624453462995935110963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46557749635641997290073975 69836624453462995935110963)
              ·
                refine ⟨104754936680194493902666445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69836624453462995935110963 104754936680194493902666445)
                ·
                  refine ⟨39283101255072935213499917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104754936680194493902666445 39283101255072935213499917)
                  ·
                    refine ⟨14731162970652350705062469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39283101255072935213499917 14731162970652350705062469)
                    ·
                      refine ⟨2762093056997315757199213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14731162970652350705062469 2762093056997315757199213)
                      ·
                        rfl

theorem cell23_5379157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5379157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379157 prefixEnd_5379157 := by exact prefixLift 5379157
  have htrace : WordTrace (prefixWord ++ tailWord_5379157) baseStart_5379157 baseEnd_5379157 := by
    simpa [prefixWord, tailWord_5379157, baseEnd_5379157] using wordTrace_append hprefix tailTrace_5379157
  have hstable : (prefixWord ++ tailWord_5379157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379157).length < 2 ^ (prefixWord ++ tailWord_5379157).sum := by decide
  have hdescent : baseEnd_5379157 < baseStart_5379157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379197 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 8]
def baseStart_5379197 : Nat := 118140960795 + 5379197 * 2 ^ 59
def prefixEnd_5379197 : Nat := 4983230072969 + 3 ^ 40 * 5379197 * 2
def baseEnd_5379197 : Nat := 306901510691499511188781

theorem tailTrace_5379197 : CollatzResearch.WordTrace tailWord_5379197 prefixEnd_5379197 306901510691499511188781 := by
  unfold tailWord_5379197
  simp only [CollatzResearch.WordTrace]
  refine ⟨196195432693095437551767845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130796955128730291701178563 196195432693095437551767845)
  ·
    refine ⟨36786643629955394540956471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196195432693095437551767845 36786643629955394540956471)
    ·
      refine ⟨55179965444933091811434707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36786643629955394540956471 55179965444933091811434707)
      ·
        refine ⟨82769948167399637717152061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55179965444933091811434707 82769948167399637717152061)
        ·
          refine ⟨31038730562774864143932023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82769948167399637717152061 31038730562774864143932023)
          ·
            refine ⟨46558095844162296215898035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31038730562774864143932023 46558095844162296215898035)
            ·
              refine ⟨69837143766243444323847053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46558095844162296215898035 69837143766243444323847053)
              ·
                refine ⟨26188928912341291621442645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69837143766243444323847053 26188928912341291621442645)
                ·
                  refine ⟨306901510691499511188781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26188928912341291621442645 306901510691499511188781)
                  ·
                    rfl

theorem cell23_5379197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_5379197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379197 prefixEnd_5379197 := by exact prefixLift 5379197
  have htrace : WordTrace (prefixWord ++ tailWord_5379197) baseStart_5379197 baseEnd_5379197 := by
    simpa [prefixWord, tailWord_5379197, baseEnd_5379197] using wordTrace_append hprefix tailTrace_5379197
  have hstable : (prefixWord ++ tailWord_5379197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379197).length < 2 ^ (prefixWord ++ tailWord_5379197).sum := by decide
  have hdescent : baseEnd_5379197 < baseStart_5379197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379201 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 3, 4]
def baseStart_5379201 : Nat := 118140960795 + 5379201 * 2 ^ 59
def prefixEnd_5379201 : Nat := 4983230072969 + 3 ^ 40 * 5379201 * 2
def baseEnd_5379201 : Nat := 920705216715371195016337

theorem tailTrace_5379201 : CollatzResearch.WordTrace tailWord_5379201 prefixEnd_5379201 920705216715371195016337 := by
  unfold tailWord_5379201
  simp only [CollatzResearch.WordTrace]
  refine ⟨196195578585080946234913457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130797052390053964156608971 196195578585080946234913457)
  ·
    refine ⟨147146683938810709676185093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196195578585080946234913457 147146683938810709676185093)
    ·
      refine ⟨27590003238527008064284705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147146683938810709676185093 27590003238527008064284705)
      ·
        refine ⟨20692502428895256048213529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27590003238527008064284705 20692502428895256048213529)
        ·
          refine ⟨15519376821671442036160147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20692502428895256048213529 15519376821671442036160147)
          ·
            refine ⟨23279065232507163054240221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15519376821671442036160147 23279065232507163054240221)
            ·
              refine ⟨8729649462190186145340083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23279065232507163054240221 8729649462190186145340083)
              ·
                refine ⟨13094474193285279218010125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729649462190186145340083 13094474193285279218010125)
                ·
                  refine ⟨4910427822481979706753797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13094474193285279218010125 4910427822481979706753797)
                  ·
                    refine ⟨920705216715371195016337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910427822481979706753797 920705216715371195016337)
                    ·
                      rfl

theorem cell23_5379201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_5379201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379201 prefixEnd_5379201 := by exact prefixLift 5379201
  have htrace : WordTrace (prefixWord ++ tailWord_5379201) baseStart_5379201 baseEnd_5379201 := by
    simpa [prefixWord, tailWord_5379201, baseEnd_5379201] using wordTrace_append hprefix tailTrace_5379201
  have hstable : (prefixWord ++ tailWord_5379201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379201).length < 2 ^ (prefixWord ++ tailWord_5379201).sum := by decide
  have hdescent : baseEnd_5379201 < baseStart_5379201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379251 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 2, 3, 2]
def baseStart_5379251 : Nat := 118140960795 + 5379251 * 2 ^ 59
def prefixEnd_5379251 : Nat := 4983230072969 + 3 ^ 40 * 5379251 * 2
def baseEnd_5379251 : Nat := 2762141324178838389423781

theorem tailTrace_5379251 : CollatzResearch.WordTrace tailWord_5379251 prefixEnd_5379251 2762141324178838389423781 := by
  unfold tailWord_5379251
  simp only [CollatzResearch.WordTrace]
  refine ⟨196197402234899804774233607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130798268156599869849489071 196197402234899804774233607)
  ·
    refine ⟨294296103352349707161350411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196197402234899804774233607 294296103352349707161350411)
    ·
      refine ⟨441444155028524560742025617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294296103352349707161350411 441444155028524560742025617)
      ·
        refine ⟨331083116271393420556519213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441444155028524560742025617 331083116271393420556519213)
        ·
          refine ⟨124156168601772532708694705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331083116271393420556519213 124156168601772532708694705)
          ·
            refine ⟨93117126451329399531521029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124156168601772532708694705 93117126451329399531521029)
            ·
              refine ⟨17459461209624262412160193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93117126451329399531521029 17459461209624262412160193)
              ·
                refine ⟨13094595907218196809120145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17459461209624262412160193 13094595907218196809120145)
                ·
                  refine ⟨9820946930413647606840109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13094595907218196809120145 9820946930413647606840109)
                  ·
                    refine ⟨3682855098905117852565041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9820946930413647606840109 3682855098905117852565041)
                    ·
                      refine ⟨2762141324178838389423781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682855098905117852565041 2762141324178838389423781)
                      ·
                        rfl

theorem cell23_5379251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3, 2].length) (baseStart_5379251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379251 prefixEnd_5379251 := by exact prefixLift 5379251
  have htrace : WordTrace (prefixWord ++ tailWord_5379251) baseStart_5379251 baseEnd_5379251 := by
    simpa [prefixWord, tailWord_5379251, baseEnd_5379251] using wordTrace_append hprefix tailTrace_5379251
  have hstable : (prefixWord ++ tailWord_5379251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379251).length < 2 ^ (prefixWord ++ tailWord_5379251).sum := by decide
  have hdescent : baseEnd_5379251 < baseStart_5379251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379274 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_5379274 : Nat := 118140960795 + 5379274 * 2 ^ 59
def prefixEnd_5379274 : Nat := 4983230072969 + 3 ^ 40 * 5379274 * 2
def baseEnd_5379274 : Nat := 920717711411297266478725

theorem tailTrace_5379274 : CollatzResearch.WordTrace tailWord_5379274 prefixEnd_5379274 920717711411297266478725 := by
  unfold tailWord_5379274
  simp only [CollatzResearch.WordTrace]
  refine ⟨49049560278454119925580219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130798827409210986468213917 49049560278454119925580219)
  ·
    refine ⟨73574340417681179888370329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49049560278454119925580219 73574340417681179888370329)
    ·
      refine ⟨55180755313260884916277747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73574340417681179888370329 55180755313260884916277747)
      ·
        refine ⟨82771132969891327374416621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55180755313260884916277747 82771132969891327374416621)
        ·
          refine ⟨31039174863709247765406233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82771132969891327374416621 31039174863709247765406233)
          ·
            refine ⟨23279381147781935824054675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31039174863709247765406233 23279381147781935824054675)
            ·
              refine ⟨34919071721672903736082013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23279381147781935824054675 34919071721672903736082013)
              ·
                refine ⟨13094651895627338901030755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34919071721672903736082013 13094651895627338901030755)
                ·
                  refine ⟨19641977843441008351546133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13094651895627338901030755 19641977843441008351546133)
                  ·
                    refine ⟨920717711411297266478725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19641977843441008351546133 920717711411297266478725)
                    ·
                      rfl

theorem cell23_5379274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_5379274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379274 prefixEnd_5379274 := by exact prefixLift 5379274
  have htrace : WordTrace (prefixWord ++ tailWord_5379274) baseStart_5379274 baseEnd_5379274 := by
    simpa [prefixWord, tailWord_5379274, baseEnd_5379274] using wordTrace_append hprefix tailTrace_5379274
  have hstable : (prefixWord ++ tailWord_5379274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379274).length < 2 ^ (prefixWord ++ tailWord_5379274).sum := by decide
  have hdescent : baseEnd_5379274 < baseStart_5379274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379285 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5379285 : Nat := 118140960795 + 5379285 * 2 ^ 59
def prefixEnd_5379285 : Nat := 4983230072969 + 3 ^ 40 * 5379285 * 2
def baseEnd_5379285 : Nat := 2762158782521091256398625

theorem tailTrace_5379285 : CollatzResearch.WordTrace tailWord_5379285 prefixEnd_5379285 2762158782521091256398625 := by
  unfold tailWord_5379285
  simp only [CollatzResearch.WordTrace]
  refine ⟨196198642316776628580971309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130799094877851085720647539 196198642316776628580971309)
  ·
    refine ⟨73574490868791235717864241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196198642316776628580971309 73574490868791235717864241)
    ·
      refine ⟨55180868151593426788398181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73574490868791235717864241 55180868151593426788398181)
      ·
        refine ⟨10346412778423767522824659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55180868151593426788398181 10346412778423767522824659)
        ·
          refine ⟨15519619167635651284236989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10346412778423767522824659 15519619167635651284236989)
          ·
            refine ⟨5819857187863369231588871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15519619167635651284236989 5819857187863369231588871)
            ·
              refine ⟨8729785781795053847383307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819857187863369231588871 8729785781795053847383307)
              ·
                refine ⟨13094678672692580771074961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729785781795053847383307 13094678672692580771074961)
                ·
                  refine ⟨9821009004519435578306221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13094678672692580771074961 9821009004519435578306221)
                  ·
                    refine ⟨3682878376694788341864833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9821009004519435578306221 3682878376694788341864833)
                    ·
                      refine ⟨2762158782521091256398625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682878376694788341864833 2762158782521091256398625)
                      ·
                        rfl

theorem cell23_5379285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5379285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379285 prefixEnd_5379285 := by exact prefixLift 5379285
  have htrace : WordTrace (prefixWord ++ tailWord_5379285) baseStart_5379285 baseEnd_5379285 := by
    simpa [prefixWord, tailWord_5379285, baseEnd_5379285] using wordTrace_append hprefix tailTrace_5379285
  have hstable : (prefixWord ++ tailWord_5379285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379285).length < 2 ^ (prefixWord ++ tailWord_5379285).sum := by decide
  have hdescent : baseEnd_5379285 < baseStart_5379285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379287 : List Nat := [1, 1, 3, 2, 1, 2, 2, 11]
def baseStart_5379287 : Nat := 118140960795 + 5379287 * 2 ^ 59
def prefixEnd_5379287 : Nat := 4983230072969 + 3 ^ 40 * 5379287 * 2
def baseEnd_5379287 : Nat := 102302215166014824021245

theorem tailTrace_5379287 : CollatzResearch.WordTrace tailWord_5379287 prefixEnd_5379287 102302215166014824021245 := by
  unfold tailWord_5379287
  simp only [CollatzResearch.WordTrace]
  refine ⟨196198715262769382922544115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130799143508512921948362743 196198715262769382922544115)
  ·
    refine ⟨294298072894154074383816173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196198715262769382922544115 294298072894154074383816173)
    ·
      refine ⟨110361777335307777893931065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294298072894154074383816173 110361777335307777893931065)
      ·
        refine ⟨82771333001480833420448299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110361777335307777893931065 82771333001480833420448299)
        ·
          refine ⟨124156999502221250130672449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82771333001480833420448299 124156999502221250130672449)
          ·
            refine ⟨93117749626665937598004337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124156999502221250130672449 93117749626665937598004337)
            ·
              refine ⟨69838312219999453198503253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93117749626665937598004337 69838312219999453198503253)
              ·
                refine ⟨102302215166014824021245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69838312219999453198503253 102302215166014824021245)
                ·
                  rfl

theorem cell23_5379287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 11].length) (baseStart_5379287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379287 prefixEnd_5379287 := by exact prefixLift 5379287
  have htrace : WordTrace (prefixWord ++ tailWord_5379287) baseStart_5379287 baseEnd_5379287 := by
    simpa [prefixWord, tailWord_5379287, baseEnd_5379287] using wordTrace_append hprefix tailTrace_5379287
  have hstable : (prefixWord ++ tailWord_5379287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379287).length < 2 ^ (prefixWord ++ tailWord_5379287).sum := by decide
  have hdescent : baseEnd_5379287 < baseStart_5379287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379308 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_5379308 : Nat := 118140960795 + 5379308 * 2 ^ 59
def prefixEnd_5379308 : Nat := 4983230072969 + 3 ^ 40 * 5379308 * 2
def baseEnd_5379308 : Nat := 920723530858714888803673

theorem tailTrace_5379308 : CollatzResearch.WordTrace tailWord_5379308 prefixEnd_5379308 920723530858714888803673 := by
  unfold tailWord_5379308
  simp only [CollatzResearch.WordTrace]
  refine ⟨98099740597846651754529289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130799654130462202339372385 98099740597846651754529289)
  ·
    refine ⟨73574805448384988815896967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98099740597846651754529289 73574805448384988815896967)
    ·
      refine ⟨110362208172577483223845451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73574805448384988815896967 110362208172577483223845451)
      ·
        refine ⟨165543312258866224835768177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110362208172577483223845451 165543312258866224835768177)
        ·
          refine ⟨124157484194149668626826133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165543312258866224835768177 124157484194149668626826133)
          ·
            refine ⟨5819882071600765716882475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124157484194149668626826133 5819882071600765716882475)
            ·
              refine ⟨8729823107401148575323713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5819882071600765716882475 8729823107401148575323713)
              ·
                refine ⟨6547367330550861431492785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8729823107401148575323713 6547367330550861431492785)
                ·
                  refine ⟨4910525497913146073619589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6547367330550861431492785 4910525497913146073619589)
                  ·
                    refine ⟨920723530858714888803673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910525497913146073619589 920723530858714888803673)
                    ·
                      rfl

theorem cell23_5379308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_5379308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379308 prefixEnd_5379308 := by exact prefixLift 5379308
  have htrace : WordTrace (prefixWord ++ tailWord_5379308) baseStart_5379308 baseEnd_5379308 := by
    simpa [prefixWord, tailWord_5379308, baseEnd_5379308] using wordTrace_append hprefix tailTrace_5379308
  have hstable : (prefixWord ++ tailWord_5379308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379308).length < 2 ^ (prefixWord ++ tailWord_5379308).sum := by decide
  have hdescent : baseEnd_5379308 < baseStart_5379308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379315 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 1, 2, 2]
def baseStart_5379315 : Nat := 118140960795 + 5379315 * 2 ^ 59
def prefixEnd_5379315 : Nat := 4983230072969 + 3 ^ 40 * 5379315 * 2
def baseEnd_5379315 : Nat := 2762174186940726139023487

theorem tailTrace_5379315 : CollatzResearch.WordTrace tailWord_5379315 prefixEnd_5379315 2762174186940726139023487 := by
  unfold tailWord_5379315
  simp only [CollatzResearch.WordTrace]
  refine ⟨196199736506667943704563399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130799824337778629136375599 196199736506667943704563399)
  ·
    refine ⟨294299604760001915556845099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196199736506667943704563399 294299604760001915556845099)
    ·
      refine ⟨441449407140002873335267649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294299604760001915556845099 441449407140002873335267649)
      ·
        refine ⟨331087055355002155001450737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441449407140002873335267649 331087055355002155001450737)
        ·
          refine ⟨248315291516251616251088053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331087055355002155001450737 248315291516251616251088053)
          ·
            refine ⟨23279558579648589023539505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 248315291516251616251088053 23279558579648589023539505)
            ·
              refine ⟨17459668934736441767654629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23279558579648589023539505 17459668934736441767654629)
              ·
                refine ⟨3273687925263082831435243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17459668934736441767654629 3273687925263082831435243)
                ·
                  refine ⟨4910531887894624247152865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273687925263082831435243 4910531887894624247152865)
                  ·
                    refine ⟨3682898915920968185364649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4910531887894624247152865 3682898915920968185364649)
                    ·
                      refine ⟨2762174186940726139023487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3682898915920968185364649 2762174186940726139023487)
                      ·
                        rfl

theorem cell23_5379315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 2, 2].length) (baseStart_5379315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379315 prefixEnd_5379315 := by exact prefixLift 5379315
  have htrace : WordTrace (prefixWord ++ tailWord_5379315) baseStart_5379315 baseEnd_5379315 := by
    simpa [prefixWord, tailWord_5379315, baseEnd_5379315] using wordTrace_append hprefix tailTrace_5379315
  have hstable : (prefixWord ++ tailWord_5379315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379315).length < 2 ^ (prefixWord ++ tailWord_5379315).sum := by decide
  have hdescent : baseEnd_5379315 < baseStart_5379315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379331 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 3]
def baseStart_5379331 : Nat := 118140960795 + 5379331 * 2 ^ 59
def prefixEnd_5379331 : Nat := 4983230072969 + 3 ^ 40 * 5379331 * 2
def baseEnd_5379331 : Nat := 2762182402631198076423413

theorem tailTrace_5379331 : CollatzResearch.WordTrace tailWord_5379331 prefixEnd_5379331 2762182402631198076423413 := by
  unfold tailWord_5379331
  simp only [CollatzResearch.WordTrace]
  refine ⟨196200320074609978437145847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130800213383073318958097231 196200320074609978437145847)
  ·
    refine ⟨294300480111914967655718771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196200320074609978437145847 294300480111914967655718771)
    ·
      refine ⟨441450720167872451483578157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294300480111914967655718771 441450720167872451483578157)
      ·
        refine ⟨165544020062952169306341809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441450720167872451483578157 165544020062952169306341809)
        ·
          refine ⟨124158015047214126979756357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165544020062952169306341809 124158015047214126979756357)
          ·
            refine ⟨23279627821352648808704317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124158015047214126979756357 23279627821352648808704317)
            ·
              refine ⟨8729860433007243303264119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23279627821352648808704317 8729860433007243303264119)
              ·
                refine ⟨13094790649510864954896179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8729860433007243303264119 13094790649510864954896179)
                ·
                  refine ⟨19642185974266297432344269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13094790649510864954896179 19642185974266297432344269)
                  ·
                    refine ⟨7365819740349861537129101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19642185974266297432344269 7365819740349861537129101)
                    ·
                      refine ⟨2762182402631198076423413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7365819740349861537129101 2762182402631198076423413)
                      ·
                        rfl

theorem cell23_5379331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_5379331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379331 prefixEnd_5379331 := by exact prefixLift 5379331
  have htrace : WordTrace (prefixWord ++ tailWord_5379331) baseStart_5379331 baseEnd_5379331 := by
    simpa [prefixWord, tailWord_5379331, baseEnd_5379331] using wordTrace_append hprefix tailTrace_5379331
  have hstable : (prefixWord ++ tailWord_5379331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379331).length < 2 ^ (prefixWord ++ tailWord_5379331).sum := by decide
  have hdescent : baseEnd_5379331 < baseStart_5379331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379384 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_5379384 : Nat := 118140960795 + 5379384 * 2 ^ 59
def prefixEnd_5379384 : Nat := 4983230072969 + 3 ^ 40 * 5379384 * 2
def baseEnd_5379384 : Nat := 2762209617105886369060669

theorem tailTrace_5379384 : CollatzResearch.WordTrace tailWord_5379384 prefixEnd_5379384 2762209617105886369060669 := by
  unfold tailWord_5379384
  simp only [CollatzResearch.WordTrace]
  refine ⟨98101126571708984244412603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130801502095611978992550137 98101126571708984244412603)
  ·
    refine ⟨147151689857563476366618905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98101126571708984244412603 147151689857563476366618905)
    ·
      refine ⟨110363767393172607274964179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147151689857563476366618905 110363767393172607274964179)
      ·
        refine ⟨165545651089758910912446269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110363767393172607274964179 165545651089758910912446269)
        ·
          refine ⟨62079619158659591592167351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165545651089758910912446269 62079619158659591592167351)
          ·
            refine ⟨93119428737989387388251027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62079619158659591592167351 93119428737989387388251027)
            ·
              refine ⟨139679143106984081082376541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93119428737989387388251027 139679143106984081082376541)
              ·
                refine ⟨52379678665119030405891203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139679143106984081082376541 52379678665119030405891203)
                ·
                  refine ⟨78569517997678545608836805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52379678665119030405891203 78569517997678545608836805)
                  ·
                    refine ⟨14731784624564727301656901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78569517997678545608836805 14731784624564727301656901)
                    ·
                      refine ⟨2762209617105886369060669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14731784624564727301656901 2762209617105886369060669)
                      ·
                        rfl

theorem cell23_5379384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_5379384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379384 prefixEnd_5379384 := by exact prefixLift 5379384
  have htrace : WordTrace (prefixWord ++ tailWord_5379384) baseStart_5379384 baseEnd_5379384 := by
    simpa [prefixWord, tailWord_5379384, baseEnd_5379384] using wordTrace_append hprefix tailTrace_5379384
  have hstable : (prefixWord ++ tailWord_5379384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379384).length < 2 ^ (prefixWord ++ tailWord_5379384).sum := by decide
  have hdescent : baseEnd_5379384 < baseStart_5379384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379411 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 5]
def baseStart_5379411 : Nat := 118140960795 + 5379411 * 2 ^ 59
def prefixEnd_5379411 : Nat := 4983230072969 + 3 ^ 40 * 5379411 * 2
def baseEnd_5379411 : Nat := 306913720120395307047005

theorem tailTrace_5379411 : CollatzResearch.WordTrace tailWord_5379411 prefixEnd_5379411 306913720120395307047005 := by
  unfold tailWord_5379411
  simp only [CollatzResearch.WordTrace]
  refine ⟨196203237914320152100058087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130802158609546768066705391 196203237914320152100058087)
  ·
    refine ⟨294304856871480228150087131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196203237914320152100058087 294304856871480228150087131)
    ·
      refine ⟨441457285307220342225130697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294304856871480228150087131 441457285307220342225130697)
      ·
        refine ⟨331092963980415256668848023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441457285307220342225130697 331092963980415256668848023)
        ·
          refine ⟨496639445970622885003272035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331092963980415256668848023 496639445970622885003272035)
          ·
            refine ⟨744959168955934327504908053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496639445970622885003272035 744959168955934327504908053)
            ·
              refine ⟨34919961044809421601792565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 744959168955934327504908053 34919961044809421601792565)
              ·
                refine ⟨3273746347950883275168053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34919961044809421601792565 3273746347950883275168053)
                ·
                  refine ⟨306913720120395307047005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3273746347950883275168053 306913720120395307047005)
                  ·
                    rfl

theorem cell23_5379411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 5].length) (baseStart_5379411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379411 prefixEnd_5379411 := by exact prefixLift 5379411
  have htrace : WordTrace (prefixWord ++ tailWord_5379411) baseStart_5379411 baseEnd_5379411 := by
    simpa [prefixWord, tailWord_5379411, baseEnd_5379411] using wordTrace_append hprefix tailTrace_5379411
  have hstable : (prefixWord ++ tailWord_5379411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379411).length < 2 ^ (prefixWord ++ tailWord_5379411).sum := by decide
  have hdescent : baseEnd_5379411 < baseStart_5379411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379428 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 5]
def baseStart_5379428 : Nat := 118140960795 + 5379428 * 2 ^ 59
def prefixEnd_5379428 : Nat := 4983230072969 + 3 ^ 40 * 5379428 * 2
def baseEnd_5379428 : Nat := 306914690028298244101163

theorem tailTrace_5379428 : CollatzResearch.WordTrace tailWord_5379428 prefixEnd_5379428 306914690028298244101163 := by
  unfold tailWord_5379428
  simp only [CollatzResearch.WordTrace]
  refine ⟨98101928977629282001713469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130802571970172376002284625 98101928977629282001713469)
  ·
    refine ⟨36788223366610980750642551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98101928977629282001713469 36788223366610980750642551)
    ·
      refine ⟨55182335049916471125963827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36788223366610980750642551 55182335049916471125963827)
      ·
        refine ⟨82773502574874706688945741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55182335049916471125963827 82773502574874706688945741)
        ·
          refine ⟨31040063465578015008354653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82773502574874706688945741 31040063465578015008354653)
          ·
            refine ⟨11640023799591755628132995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31040063465578015008354653 11640023799591755628132995)
            ·
              refine ⟨17460035699387633442199493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640023799591755628132995 17460035699387633442199493)
              ·
                refine ⟨3273756693635181270412405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17460035699387633442199493 3273756693635181270412405)
                ·
                  refine ⟨306914690028298244101163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3273756693635181270412405 306914690028298244101163)
                  ·
                    rfl

theorem cell23_5379428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_5379428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379428 prefixEnd_5379428 := by exact prefixLift 5379428
  have htrace : WordTrace (prefixWord ++ tailWord_5379428) baseStart_5379428 baseEnd_5379428 := by
    simpa [prefixWord, tailWord_5379428, baseEnd_5379428] using wordTrace_append hprefix tailTrace_5379428
  have hstable : (prefixWord ++ tailWord_5379428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379428).length < 2 ^ (prefixWord ++ tailWord_5379428).sum := by decide
  have hdescent : baseEnd_5379428 < baseStart_5379428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379488 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 3, 4]
def baseStart_5379488 : Nat := 118140960795 + 5379488 * 2 ^ 59
def prefixEnd_5379488 : Nat := 4983230072969 + 3 ^ 40 * 5379488 * 2
def baseEnd_5379488 : Nat := 920754339697984654053397

theorem tailTrace_5379488 : CollatzResearch.WordTrace tailWord_5379488 prefixEnd_5379488 920754339697984654053397 := by
  unfold tailWord_5379488
  simp only [CollatzResearch.WordTrace]
  refine ⟨98103023167520597125305559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130804030890027462833740745 98103023167520597125305559)
  ·
    refine ⟨147154534751280895687958339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98103023167520597125305559 147154534751280895687958339)
    ·
      refine ⟨220731802126921343531937509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147154534751280895687958339 220731802126921343531937509)
      ·
        refine ⟨41387212898797751912238283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220731802126921343531937509 41387212898797751912238283)
        ·
          refine ⟨62080819348196627868357425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41387212898797751912238283 62080819348196627868357425)
          ·
            refine ⟨46560614511147470901268069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62080819348196627868357425 46560614511147470901268069)
            ·
              refine ⟨8730115220840150793987763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46560614511147470901268069 8730115220840150793987763)
              ·
                refine ⟨13095172831260226190981645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8730115220840150793987763 13095172831260226190981645)
                ·
                  refine ⟨4910689811722584821618117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13095172831260226190981645 4910689811722584821618117)
                  ·
                    refine ⟨920754339697984654053397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910689811722584821618117 920754339697984654053397)
                    ·
                      rfl

theorem cell23_5379488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_5379488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379488 prefixEnd_5379488 := by exact prefixLift 5379488
  have htrace : WordTrace (prefixWord ++ tailWord_5379488) baseStart_5379488 baseEnd_5379488 := by
    simpa [prefixWord, tailWord_5379488, baseEnd_5379488] using wordTrace_append hprefix tailTrace_5379488
  have hstable : (prefixWord ++ tailWord_5379488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379488).length < 2 ^ (prefixWord ++ tailWord_5379488).sum := by decide
  have hdescent : baseEnd_5379488 < baseStart_5379488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379511 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_5379511 : Nat := 118140960795 + 5379511 * 2 ^ 59
def prefixEnd_5379511 : Nat := 4983230072969 + 3 ^ 40 * 5379511 * 2
def baseEnd_5379511 : Nat := 2762274829149007372172585

theorem tailTrace_5379511 : CollatzResearch.WordTrace tailWord_5379511 prefixEnd_5379511 2762274829149007372172585 := by
  unfold tailWord_5379511
  simp only [CollatzResearch.WordTrace]
  refine ⟨196206885213957869178698387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130804590142638579452465591 196206885213957869178698387)
  ·
    refine ⟨294310327820936803768047581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196206885213957869178698387 294310327820936803768047581)
    ·
      refine ⟨110366372932851301413017843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294310327820936803768047581 110366372932851301413017843)
      ·
        refine ⟨165549559399276952119526765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110366372932851301413017843 165549559399276952119526765)
        ·
          refine ⟨62081084774728857044822537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165549559399276952119526765 62081084774728857044822537)
          ·
            refine ⟨46560813581046642783616903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62081084774728857044822537 46560813581046642783616903)
            ·
              refine ⟨69841220371569964175425355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46560813581046642783616903 69841220371569964175425355)
              ·
                refine ⟨104761830557354946263138033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69841220371569964175425355 104761830557354946263138033)
                ·
                  refine ⟨78571372918016209697353525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104761830557354946263138033 78571372918016209697353525)
                  ·
                    refine ⟨7366066211064019659126893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78571372918016209697353525 7366066211064019659126893)
                    ·
                      refine ⟨2762274829149007372172585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366066211064019659126893 2762274829149007372172585)
                      ·
                        rfl

theorem cell23_5379511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_5379511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379511 prefixEnd_5379511 := by exact prefixLift 5379511
  have htrace : WordTrace (prefixWord ++ tailWord_5379511) baseStart_5379511 baseEnd_5379511 := by
    simpa [prefixWord, tailWord_5379511, baseEnd_5379511] using wordTrace_append hprefix tailTrace_5379511
  have hstable : (prefixWord ++ tailWord_5379511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379511).length < 2 ^ (prefixWord ++ tailWord_5379511).sum := by decide
  have hdescent : baseEnd_5379511 < baseStart_5379511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379545 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 3]
def baseStart_5379545 : Nat := 118140960795 + 5379545 * 2 ^ 59
def prefixEnd_5379545 : Nat := 4983230072969 + 3 ^ 40 * 5379545 * 2
def baseEnd_5379545 : Nat := 2762292287491260239147429

theorem tailTrace_5379545 : CollatzResearch.WordTrace tailWord_5379545 prefixEnd_5379545 2762292287491260239147429 := by
  unfold tailWord_5379545
  simp only [CollatzResearch.WordTrace]
  refine ⟨196208125295834692985436089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130805416863889795323624059 196208125295834692985436089)
  ·
    refine ⟨147156093971876019739077067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196208125295834692985436089 147156093971876019739077067)
    ·
      refine ⟨220734140957814029608615601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147156093971876019739077067 220734140957814029608615601)
      ·
        refine ⟨165550605718360522206461701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220734140957814029608615601 165550605718360522206461701)
        ·
          refine ⟨31040738572192597913711569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165550605718360522206461701 31040738572192597913711569)
          ·
            refine ⟨23280553929144448435283677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31040738572192597913711569 23280553929144448435283677)
            ·
              refine ⟨8730207723429168163231379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23280553929144448435283677 8730207723429168163231379)
              ·
                refine ⟨13095311585143752244847069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8730207723429168163231379 13095311585143752244847069)
                ·
                  refine ⟨4910741844428907091817651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13095311585143752244847069 4910741844428907091817651)
                  ·
                    refine ⟨7366112766643360637726477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4910741844428907091817651 7366112766643360637726477)
                    ·
                      refine ⟨2762292287491260239147429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366112766643360637726477 2762292287491260239147429)
                      ·
                        rfl

theorem cell23_5379545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_5379545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379545 prefixEnd_5379545 := by exact prefixLift 5379545
  have htrace : WordTrace (prefixWord ++ tailWord_5379545) baseStart_5379545 baseEnd_5379545 := by
    simpa [prefixWord, tailWord_5379545, baseEnd_5379545] using wordTrace_append hprefix tailTrace_5379545
  have hstable : (prefixWord ++ tailWord_5379545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379545).length < 2 ^ (prefixWord ++ tailWord_5379545).sum := by decide
  have hdescent : baseEnd_5379545 < baseStart_5379545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379565 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_5379565 : Nat := 118140960795 + 5379565 * 2 ^ 59
def prefixEnd_5379565 : Nat := 4983230072969 + 3 ^ 40 * 5379565 * 2
def baseEnd_5379565 : Nat := 920767519034783386965779

theorem tailTrace_5379565 : CollatzResearch.WordTrace tailWord_5379565 prefixEnd_5379565 920767519034783386965779 := by
  unfold tailWord_5379565
  simp only [CollatzResearch.WordTrace]
  refine ⟨196208854755762236401164149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130805903170508157600776099 196208854755762236401164149)
  ·
    refine ⟨18394580133352709662609139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196208854755762236401164149 18394580133352709662609139)
    ·
      refine ⟨27591870200029064493913709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18394580133352709662609139 27591870200029064493913709)
      ·
        refine ⟨10346951325010899185217641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27591870200029064493913709 10346951325010899185217641)
        ·
          refine ⟨7760213493758174388913231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10346951325010899185217641 7760213493758174388913231)
          ·
            refine ⟨11640320240637261583369847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760213493758174388913231 11640320240637261583369847)
            ·
              refine ⟨17460480360955892375054771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640320240637261583369847 17460480360955892375054771)
              ·
                refine ⟨26190720541433838562582157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17460480360955892375054771 26190720541433838562582157)
                ·
                  refine ⟨9821520203037689460968309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26190720541433838562582157 9821520203037689460968309)
                  ·
                    refine ⟨920767519034783386965779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9821520203037689460968309 920767519034783386965779)
                    ·
                      rfl

theorem cell23_5379565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_5379565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379565 prefixEnd_5379565 := by exact prefixLift 5379565
  have htrace : WordTrace (prefixWord ++ tailWord_5379565) baseStart_5379565 baseEnd_5379565 := by
    simpa [prefixWord, tailWord_5379565, baseEnd_5379565] using wordTrace_append hprefix tailTrace_5379565
  have hstable : (prefixWord ++ tailWord_5379565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379565).length < 2 ^ (prefixWord ++ tailWord_5379565).sum := by decide
  have hdescent : baseEnd_5379565 < baseStart_5379565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379568 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_5379568 : Nat := 118140960795 + 5379568 * 2 ^ 59
def prefixEnd_5379568 : Nat := 4983230072969 + 3 ^ 40 * 5379568 * 2
def baseEnd_5379568 : Nat := 2762304097546313649159823

theorem tailTrace_5379568 : CollatzResearch.WordTrace tailWord_5379568 prefixEnd_5379568 2762304097546313649159823 := by
  unfold tailWord_5379568
  simp only [CollatzResearch.WordTrace]
  refine ⟨98104482087375683956761679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130805976116500911942348905 98104482087375683956761679)
  ·
    refine ⟨147156723131063525935142519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98104482087375683956761679 147156723131063525935142519)
    ·
      refine ⟨220735084696595288902713779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147156723131063525935142519 220735084696595288902713779)
      ·
        refine ⟨331102627044892933354070669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220735084696595288902713779 331102627044892933354070669)
        ·
          refine ⟨124163485141834850007776501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 331102627044892933354070669 124163485141834850007776501)
          ·
            refine ⟨11640326732047017188229047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124163485141834850007776501 11640326732047017188229047)
            ·
              refine ⟨17460490098070525782343571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11640326732047017188229047 17460490098070525782343571)
              ·
                refine ⟨26190735147105788673515357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17460490098070525782343571 26190735147105788673515357)
                ·
                  refine ⟨9821525680164670752568259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26190735147105788673515357 9821525680164670752568259)
                  ·
                    refine ⟨14732288520247006128852389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9821525680164670752568259 14732288520247006128852389)
                    ·
                      refine ⟨2762304097546313649159823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14732288520247006128852389 2762304097546313649159823)
                      ·
                        rfl

theorem cell23_5379568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_5379568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379568 prefixEnd_5379568 := by exact prefixLift 5379568
  have htrace : WordTrace (prefixWord ++ tailWord_5379568) baseStart_5379568 baseEnd_5379568 := by
    simpa [prefixWord, tailWord_5379568, baseEnd_5379568] using wordTrace_append hprefix tailTrace_5379568
  have hstable : (prefixWord ++ tailWord_5379568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379568).length < 2 ^ (prefixWord ++ tailWord_5379568).sum := by decide
  have hdescent : baseEnd_5379568 < baseStart_5379568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379590 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5379590 : Nat := 118140960795 + 5379590 * 2 ^ 59
def prefixEnd_5379590 : Nat := 4983230072969 + 3 ^ 40 * 5379590 * 2
def baseEnd_5379590 : Nat := 920771798040237521028241

theorem tailTrace_5379590 : CollatzResearch.WordTrace tailWord_5379590 prefixEnd_5379590 920771798040237521028241 := by
  unfold tailWord_5379590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6131555205645989552213257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130806511053781110447216149 6131555205645989552213257)
  ·
    refine ⟨4598666404234492164159943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6131555205645989552213257 4598666404234492164159943)
    ·
      refine ⟨6897999606351738246239915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4598666404234492164159943 6897999606351738246239915)
      ·
        refine ⟨10346999409527607369359873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6897999606351738246239915 10346999409527607369359873)
        ·
          refine ⟨7760249557145705527019905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10346999409527607369359873 7760249557145705527019905)
          ·
            refine ⟨5820187167859279145264929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7760249557145705527019905 5820187167859279145264929)
            ·
              refine ⟨4365140375894459358948697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5820187167859279145264929 4365140375894459358948697)
              ·
                refine ⟨3273855281920844519211523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365140375894459358948697 3273855281920844519211523)
                ·
                  refine ⟨4910782922881266778817285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273855281920844519211523 4910782922881266778817285)
                  ·
                    refine ⟨920771798040237521028241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910782922881266778817285 920771798040237521028241)
                    ·
                      rfl

theorem cell23_5379590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5379590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379590 prefixEnd_5379590 := by exact prefixLift 5379590
  have htrace : WordTrace (prefixWord ++ tailWord_5379590) baseStart_5379590 baseEnd_5379590 := by
    simpa [prefixWord, tailWord_5379590, baseEnd_5379590] using wordTrace_append hprefix tailTrace_5379590
  have hstable : (prefixWord ++ tailWord_5379590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379590).length < 2 ^ (prefixWord ++ tailWord_5379590).sum := by decide
  have hdescent : baseEnd_5379590 < baseStart_5379590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379591 : List Nat := [1, 1, 4, 3, 2, 12]
def baseStart_5379591 : Nat := 118140960795 + 5379591 * 2 ^ 59
def prefixEnd_5379591 : Nat := 4983230072969 + 3 ^ 40 * 5379591 * 2
def baseEnd_5379591 : Nat := 11367555175314267733219

theorem tailTrace_5379591 : CollatzResearch.WordTrace tailWord_5379591 prefixEnd_5379591 11367555175314267733219 := by
  unfold tailWord_5379591
  simp only [CollatzResearch.WordTrace]
  refine ⟨196209803053668042841610627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130806535369112028561073751 196209803053668042841610627)
  ·
    refine ⟨294314704580502064262415941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196209803053668042841610627 294314704580502064262415941)
    ·
      refine ⟨55184007108844137049202989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294314704580502064262415941 55184007108844137049202989)
      ·
        refine ⟨20694002665816551393451121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55184007108844137049202989 20694002665816551393451121)
        ·
          refine ⟨15520501999362413545088341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20694002665816551393451121 15520501999362413545088341)
          ·
            refine ⟨11367555175314267733219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15520501999362413545088341 11367555175314267733219)
            ·
              rfl

theorem cell23_5379591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 12].length) (baseStart_5379591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379591 prefixEnd_5379591 := by exact prefixLift 5379591
  have htrace : WordTrace (prefixWord ++ tailWord_5379591) baseStart_5379591 baseEnd_5379591 := by
    simpa [prefixWord, tailWord_5379591, baseEnd_5379591] using wordTrace_append hprefix tailTrace_5379591
  have hstable : (prefixWord ++ tailWord_5379591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379591).length < 2 ^ (prefixWord ++ tailWord_5379591).sum := by decide
  have hdescent : baseEnd_5379591 < baseStart_5379591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379596 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 1, 1, 3]
def baseStart_5379596 : Nat := 118140960795 + 5379596 * 2 ^ 59
def prefixEnd_5379596 : Nat := 4983230072969 + 3 ^ 40 * 5379596 * 2
def baseEnd_5379596 : Nat := 2762318475004639539609695

theorem tailTrace_5379596 : CollatzResearch.WordTrace tailWord_5379596 prefixEnd_5379596 2762318475004639539609695 := by
  unfold tailWord_5379596
  simp only [CollatzResearch.WordTrace]
  refine ⟨98104992709324964347771321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130806656945766619130361761 98104992709324964347771321)
  ·
    refine ⟨73578744531993723260828491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98104992709324964347771321 73578744531993723260828491)
    ·
      refine ⟨110368116797990584891242737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73578744531993723260828491 110368116797990584891242737)
      ·
        refine ⟨82776087598492938668432053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110368116797990584891242737 82776087598492938668432053)
        ·
          refine ⟨7760258212358713000165505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82776087598492938668432053 7760258212358713000165505)
          ·
            refine ⟨5820193659269034750124129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7760258212358713000165505 5820193659269034750124129)
            ·
              refine ⟨4365145244451776062593097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5820193659269034750124129 4365145244451776062593097)
              ·
                refine ⟨3273858933338832046944823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365145244451776062593097 3273858933338832046944823)
                ·
                  refine ⟨4910788400008248070417235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3273858933338832046944823 4910788400008248070417235)
                  ·
                    refine ⟨7366182600012372105625853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4910788400008248070417235 7366182600012372105625853)
                    ·
                      refine ⟨2762318475004639539609695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366182600012372105625853 2762318475004639539609695)
                      ·
                        rfl

theorem cell23_5379596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_5379596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379596 prefixEnd_5379596 := by exact prefixLift 5379596
  have htrace : WordTrace (prefixWord ++ tailWord_5379596) baseStart_5379596 baseEnd_5379596 := by
    simpa [prefixWord, tailWord_5379596, baseEnd_5379596] using wordTrace_append hprefix tailTrace_5379596
  have hstable : (prefixWord ++ tailWord_5379596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379596).length < 2 ^ (prefixWord ++ tailWord_5379596).sum := by decide
  have hdescent : baseEnd_5379596 < baseStart_5379596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379621 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 4, 7]
def baseStart_5379621 : Nat := 118140960795 + 5379621 * 2 ^ 59
def prefixEnd_5379621 : Nat := 4983230072969 + 3 ^ 40 * 5379621 * 2
def baseEnd_5379621 : Nat := 920777104007000647265693

theorem tailTrace_5379621 : CollatzResearch.WordTrace tailWord_5379621 prefixEnd_5379621 920777104007000647265693 := by
  unfold tailWord_5379621
  simp only [CollatzResearch.WordTrace]
  refine ⟨196210897243559357965202717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130807264829039571976801811 196210897243559357965202717)
  ·
    refine ⟨73579086466334759236951019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196210897243559357965202717 73579086466334759236951019)
    ·
      refine ⟨110368629699502138855426529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73579086466334759236951019 110368629699502138855426529)
      ·
        refine ⟨82776472274626604141569897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110368629699502138855426529 82776472274626604141569897)
        ·
          refine ⟨62082354205969953106177423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82776472274626604141569897 62082354205969953106177423)
          ·
            refine ⟨93123531308954929659266135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62082354205969953106177423 93123531308954929659266135)
            ·
              refine ⟨139685296963432394488899203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93123531308954929659266135 139685296963432394488899203)
              ·
                refine ⟨209527945445148591733348805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139685296963432394488899203 209527945445148591733348805)
                ·
                  refine ⟨39286489770965360950002901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209527945445148591733348805 39286489770965360950002901)
                  ·
                    refine ⟨920777104007000647265693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39286489770965360950002901 920777104007000647265693)
                    ·
                      rfl

theorem cell23_5379621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_5379621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379621 prefixEnd_5379621 := by exact prefixLift 5379621
  have htrace : WordTrace (prefixWord ++ tailWord_5379621) baseStart_5379621 baseEnd_5379621 := by
    simpa [prefixWord, tailWord_5379621, baseEnd_5379621] using wordTrace_append hprefix tailTrace_5379621
  have hstable : (prefixWord ++ tailWord_5379621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379621).length < 2 ^ (prefixWord ++ tailWord_5379621).sum := by decide
  have hdescent : baseEnd_5379621 < baseStart_5379621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379668 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_5379668 : Nat := 118140960795 + 5379668 * 2 ^ 59
def prefixEnd_5379668 : Nat := 4983230072969 + 3 ^ 40 * 5379668 * 2
def baseEnd_5379668 : Nat := 920785148537254419303121

theorem tailTrace_5379668 : CollatzResearch.WordTrace tailWord_5379668 prefixEnd_5379668 920785148537254419303121 := by
  unfold tailWord_5379668
  simp only [CollatzResearch.WordTrace]
  refine ⟨98106305737194542496081829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130808407649592723328109105 98106305737194542496081829)
  ·
    refine ⟨18394932325723976718015343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98106305737194542496081829 18394932325723976718015343)
    ·
      refine ⟨27592398488585965077023015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18394932325723976718015343 27592398488585965077023015)
      ·
        refine ⟨41388597732878947615534523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27592398488585965077023015 41388597732878947615534523)
        ·
          refine ⟨62082896599318421423301785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41388597732878947615534523 62082896599318421423301785)
          ·
            refine ⟨46562172449488816067476339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62082896599318421423301785 46562172449488816067476339)
            ·
              refine ⟨69843258674233224101214509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46562172449488816067476339 69843258674233224101214509)
              ·
                refine ⟨26191222002837459037955441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69843258674233224101214509 26191222002837459037955441)
                ·
                  refine ⟨19643416502128094278466581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26191222002837459037955441 19643416502128094278466581)
                  ·
                    refine ⟨920785148537254419303121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19643416502128094278466581 920785148537254419303121)
                    ·
                      rfl

theorem cell23_5379668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_5379668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379668 prefixEnd_5379668 := by exact prefixLift 5379668
  have htrace : WordTrace (prefixWord ++ tailWord_5379668) baseStart_5379668 baseEnd_5379668 := by
    simpa [prefixWord, tailWord_5379668, baseEnd_5379668] using wordTrace_append hprefix tailTrace_5379668
  have hstable : (prefixWord ++ tailWord_5379668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379668).length < 2 ^ (prefixWord ++ tailWord_5379668).sum := by decide
  have hdescent : baseEnd_5379668 < baseStart_5379668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379726 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5379726 : Nat := 118140960795 + 5379726 * 2 ^ 59
def prefixEnd_5379726 : Nat := 4983230072969 + 3 ^ 40 * 5379726 * 2
def baseEnd_5379726 : Nat := 2762385227489724030984097

theorem tailTrace_5379726 : CollatzResearch.WordTrace tailWord_5379726 prefixEnd_5379726 2762385227489724030984097 := by
  unfold tailWord_5379726
  simp only [CollatzResearch.WordTrace]
  refine ⟨24526840863522370112221879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130809817938785973931850021 24526840863522370112221879)
  ·
    refine ⟨36790261295283555168332819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24526840863522370112221879 36790261295283555168332819)
    ·
      refine ⟨55185391942925332752499229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36790261295283555168332819 55185391942925332752499229)
      ·
        refine ⟨20694521978596999782187211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55185391942925332752499229 20694521978596999782187211)
        ·
          refine ⟨31041782967895499673280817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20694521978596999782187211 31041782967895499673280817)
          ·
            refine ⟨23281337225921624754960613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31041782967895499673280817 23281337225921624754960613)
            ·
              refine ⟨4365250729860304641555115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23281337225921624754960613 4365250729860304641555115)
              ·
                refine ⟨6547876094790456962332673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365250729860304641555115 6547876094790456962332673)
                ·
                  refine ⟨4910907071092842721749505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6547876094790456962332673 4910907071092842721749505)
                  ·
                    refine ⟨3683180303319632041312129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4910907071092842721749505 3683180303319632041312129)
                    ·
                      refine ⟨2762385227489724030984097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683180303319632041312129 2762385227489724030984097)
                      ·
                        rfl

theorem cell23_5379726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5379726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379726 prefixEnd_5379726 := by exact prefixLift 5379726
  have htrace : WordTrace (prefixWord ++ tailWord_5379726) baseStart_5379726 baseEnd_5379726 := by
    simpa [prefixWord, tailWord_5379726, baseEnd_5379726] using wordTrace_append hprefix tailTrace_5379726
  have hstable : (prefixWord ++ tailWord_5379726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379726).length < 2 ^ (prefixWord ++ tailWord_5379726).sum := by decide
  have hdescent : baseEnd_5379726 < baseStart_5379726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379745 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 2, 5]
def baseStart_5379745 : Nat := 118140960795 + 5379745 * 2 ^ 59
def prefixEnd_5379745 : Nat := 4983230072969 + 3 ^ 40 * 5379745 * 2
def baseEnd_5379745 : Nat := 920798327874053152215503

theorem tailTrace_5379745 : CollatzResearch.WordTrace tailWord_5379745 prefixEnd_5379745 920798327874053152215503 := by
  unfold tailWord_5379745
  simp only [CollatzResearch.WordTrace]
  refine ⟨196215419895110127142716689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130810279930073418095144459 196215419895110127142716689)
  ·
    refine ⟨147161564921332595357037517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196215419895110127142716689 147161564921332595357037517)
    ·
      refine ⟨55185586845499723258889069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147161564921332595357037517 55185586845499723258889069)
      ·
        refine ⟨20694595067062396222083401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55185586845499723258889069 20694595067062396222083401)
        ·
          refine ⟨15520946300296797166562551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20694595067062396222083401 15520946300296797166562551)
          ·
            refine ⟨23281419450445195749843827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15520946300296797166562551 23281419450445195749843827)
            ·
              refine ⟨34922129175667793624765741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23281419450445195749843827 34922129175667793624765741)
              ·
                refine ⟨13095798440875422609287153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34922129175667793624765741 13095798440875422609287153)
                ·
                  refine ⟨9821848830656566956965365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13095798440875422609287153 9821848830656566956965365)
                  ·
                    refine ⟨920798327874053152215503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9821848830656566956965365 920798327874053152215503)
                    ·
                      rfl

theorem cell23_5379745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_5379745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379745 prefixEnd_5379745 := by exact prefixLift 5379745
  have htrace : WordTrace (prefixWord ++ tailWord_5379745) baseStart_5379745 baseEnd_5379745 := by
    simpa [prefixWord, tailWord_5379745, baseEnd_5379745] using wordTrace_append hprefix tailTrace_5379745
  have hstable : (prefixWord ++ tailWord_5379745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379745).length < 2 ^ (prefixWord ++ tailWord_5379745).sum := by decide
  have hdescent : baseEnd_5379745 < baseStart_5379745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379766 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_5379766 : Nat := 118140960795 + 5379766 * 2 ^ 59
def prefixEnd_5379766 : Nat := 4983230072969 + 3 ^ 40 * 5379766 * 2
def baseEnd_5379766 : Nat := 306933974079544874942657

theorem tailTrace_5379766 : CollatzResearch.WordTrace tailWord_5379766 prefixEnd_5379766 306933974079544874942657 := by
  unfold tailWord_5379766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12263511614252127983076947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130810790552022698486154101 12263511614252127983076947)
  ·
    refine ⟨18395267421378191974615421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12263511614252127983076947 18395267421378191974615421)
    ·
      refine ⟨6898225283016821990480783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18395267421378191974615421 6898225283016821990480783)
      ·
        refine ⟨10347337924525232985721175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6898225283016821990480783 10347337924525232985721175)
        ·
          refine ⟨15521006886787849478581763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10347337924525232985721175 15521006886787849478581763)
          ·
            refine ⟨23281510330181774217872645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15521006886787849478581763 23281510330181774217872645)
            ·
              refine ⟨4365283186909082665851121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23281510330181774217872645 4365283186909082665851121)
              ·
                refine ⟨3273962390181811999388341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365283186909082665851121 3273962390181811999388341)
                ·
                  refine ⟨306933974079544874942657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3273962390181811999388341 306933974079544874942657)
                  ·
                    rfl

theorem cell23_5379766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_5379766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379766 prefixEnd_5379766 := by exact prefixLift 5379766
  have htrace : WordTrace (prefixWord ++ tailWord_5379766) baseStart_5379766 baseEnd_5379766 := by
    simpa [prefixWord, tailWord_5379766, baseEnd_5379766] using wordTrace_append hprefix tailTrace_5379766
  have hstable : (prefixWord ++ tailWord_5379766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379766).length < 2 ^ (prefixWord ++ tailWord_5379766).sum := by decide
  have hdescent : baseEnd_5379766 < baseStart_5379766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379775 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 3, 4]
def baseStart_5379775 : Nat := 118140960795 + 5379775 * 2 ^ 59
def prefixEnd_5379775 : Nat := 4983230072969 + 3 ^ 40 * 5379775 * 2
def baseEnd_5379775 : Nat := 920803462680598113090457

theorem tailTrace_5379775 : CollatzResearch.WordTrace tailWord_5379775 prefixEnd_5379775 920803462680598113090457 := by
  unfold tailWord_5379775
  simp only [CollatzResearch.WordTrace]
  refine ⟨196216514085001442266308779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130811009390000961510872519 196216514085001442266308779)
  ·
    refine ⟨294324771127502163399463169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196216514085001442266308779 294324771127502163399463169)
    ·
      refine ⟨220743578345626622549597377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294324771127502163399463169 220743578345626622549597377)
      ·
        refine ⟨165557683759219966912198033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220743578345626622549597377 165557683759219966912198033)
        ·
          refine ⟨124168262819414975184148525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165557683759219966912198033 124168262819414975184148525)
          ·
            refine ⟨46563098557280615694055697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124168262819414975184148525 46563098557280615694055697)
            ·
              refine ⟨34922323917960461770541773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46563098557280615694055697 34922323917960461770541773)
              ·
                refine ⟨13095871469235173163953165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34922323917960461770541773 13095871469235173163953165)
                ·
                  refine ⟨4910951800963189936482437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13095871469235173163953165 4910951800963189936482437)
                  ·
                    refine ⟨920803462680598113090457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4910951800963189936482437 920803462680598113090457)
                    ·
                      rfl

theorem cell23_5379775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_5379775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379775 prefixEnd_5379775 := by exact prefixLift 5379775
  have htrace : WordTrace (prefixWord ++ tailWord_5379775) baseStart_5379775 baseEnd_5379775 := by
    simpa [prefixWord, tailWord_5379775, baseEnd_5379775] using wordTrace_append hprefix tailTrace_5379775
  have hstable : (prefixWord ++ tailWord_5379775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379775).length < 2 ^ (prefixWord ++ tailWord_5379775).sum := by decide
  have hdescent : baseEnd_5379775 < baseStart_5379775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379802 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_5379802 : Nat := 118140960795 + 5379802 * 2 ^ 59
def prefixEnd_5379802 : Nat := 4983230072969 + 3 ^ 40 * 5379802 * 2
def baseEnd_5379802 : Nat := 2762424252019465733633747

theorem tailTrace_5379802 : CollatzResearch.WordTrace tailWord_5379802 prefixEnd_5379802 2762424252019465733633747 := by
  unfold tailWord_5379802
  simp only [CollatzResearch.WordTrace]
  refine ⟨49054374713975906469385415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130811665903935750585027773 49054374713975906469385415)
  ·
    refine ⟨73581562070963859704078123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49054374713975906469385415 73581562070963859704078123)
    ·
      refine ⟨110372343106445789556117185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73581562070963859704078123 110372343106445789556117185)
      ·
        refine ⟨82779257329834342167087889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110372343106445789556117185 82779257329834342167087889)
        ·
          refine ⟨62084442997375756625315917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82779257329834342167087889 62084442997375756625315917)
          ·
            refine ⟨23281666124015908734493469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62084442997375756625315917 23281666124015908734493469)
            ·
              refine ⟨8730624796505965775435051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23281666124015908734493469 8730624796505965775435051)
              ·
                refine ⟨13095937194758948663152577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8730624796505965775435051 13095937194758948663152577)
                ·
                  refine ⟨9821952896069211497364433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13095937194758948663152577 9821952896069211497364433)
                  ·
                    refine ⟨7366464672051908623023325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9821952896069211497364433 7366464672051908623023325)
                    ·
                      refine ⟨2762424252019465733633747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366464672051908623023325 2762424252019465733633747)
                      ·
                        rfl

theorem cell23_5379802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_5379802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379802 prefixEnd_5379802 := by exact prefixLift 5379802
  have htrace : WordTrace (prefixWord ++ tailWord_5379802) baseStart_5379802 baseEnd_5379802 := by
    simpa [prefixWord, tailWord_5379802, baseEnd_5379802] using wordTrace_append hprefix tailTrace_5379802
  have hstable : (prefixWord ++ tailWord_5379802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379802).length < 2 ^ (prefixWord ++ tailWord_5379802).sum := by decide
  have hdescent : baseEnd_5379802 < baseStart_5379802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379866 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3]
def baseStart_5379866 : Nat := 118140960795 + 5379866 * 2 ^ 59
def prefixEnd_5379866 : Nat := 4983230072969 + 3 ^ 40 * 5379866 * 2
def baseEnd_5379866 : Nat := 2762457114781353483233453

theorem tailTrace_5379866 : CollatzResearch.WordTrace tailWord_5379866 prefixEnd_5379866 2762457114781353483233453 := by
  unfold tailWord_5379866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49054958281917941201967863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130813222085114509871914301 49054958281917941201967863)
  ·
    refine ⟨73582437422876911802951795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49054958281917941201967863 73582437422876911802951795)
    ·
      refine ⟨110373656134315367704427693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73582437422876911802951795 110373656134315367704427693)
      ·
        refine ⟨41390121050368262889160385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110373656134315367704427693 41390121050368262889160385)
        ·
          refine ⟨31042590787776197166870289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41390121050368262889160385 31042590787776197166870289)
          ·
            refine ⟨23281943090832147875152717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31042590787776197166870289 23281943090832147875152717)
            ·
              refine ⟨8730728659062055453182269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23281943090832147875152717 8730728659062055453182269)
              ·
                refine ⟨3274023247148270794943351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8730728659062055453182269 3274023247148270794943351)
                ·
                  refine ⟨4911034870722406192415027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274023247148270794943351 4911034870722406192415027)
                  ·
                    refine ⟨7366552306083609288622541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4911034870722406192415027 7366552306083609288622541)
                    ·
                      refine ⟨2762457114781353483233453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366552306083609288622541 2762457114781353483233453)
                      ·
                        rfl

theorem cell23_5379866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_5379866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379866 prefixEnd_5379866 := by exact prefixLift 5379866
  have htrace : WordTrace (prefixWord ++ tailWord_5379866) baseStart_5379866 baseEnd_5379866 := by
    simpa [prefixWord, tailWord_5379866, baseEnd_5379866] using wordTrace_append hprefix tailTrace_5379866
  have hstable : (prefixWord ++ tailWord_5379866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379866).length < 2 ^ (prefixWord ++ tailWord_5379866).sum := by decide
  have hdescent : baseEnd_5379866 < baseStart_5379866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379872 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5379872 : Nat := 118140960795 + 5379872 * 2 ^ 59
def prefixEnd_5379872 : Nat := 4983230072969 + 3 ^ 40 * 5379872 * 2
def baseEnd_5379872 : Nat := 2762460195665280459758425

theorem tailTrace_5379872 : CollatzResearch.WordTrace tailWord_5379872 prefixEnd_5379872 2762460195665280459758425 := by
  unfold tailWord_5379872
  simp only [CollatzResearch.WordTrace]
  refine ⟨98110025982825013916294935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130813367977100018555059913 98110025982825013916294935)
  ·
    refine ⟨147165038974237520874442403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98110025982825013916294935 147165038974237520874442403)
    ·
      refine ⟨220747558461356281311663605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147165038974237520874442403 220747558461356281311663605)
      ·
        refine ⟨20695083605752151372968463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220747558461356281311663605 20695083605752151372968463)
        ·
          refine ⟨31042625408628227059452695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20695083605752151372968463 31042625408628227059452695)
          ·
            refine ⟨46563938112942340589179043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31042625408628227059452695 46563938112942340589179043)
            ·
              refine ⟨69845907169413510883768565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46563938112942340589179043 69845907169413510883768565)
              ·
                refine ⟨6548053797132516645353303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69845907169413510883768565 6548053797132516645353303)
                ·
                  refine ⟨9822080695698774968029955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6548053797132516645353303 9822080695698774968029955)
                  ·
                    refine ⟨14733121043548162452044933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9822080695698774968029955 14733121043548162452044933)
                    ·
                      refine ⟨2762460195665280459758425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14733121043548162452044933 2762460195665280459758425)
                      ·
                        rfl

theorem cell23_5379872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5379872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379872 prefixEnd_5379872 := by exact prefixLift 5379872
  have htrace : WordTrace (prefixWord ++ tailWord_5379872) baseStart_5379872 baseEnd_5379872 := by
    simpa [prefixWord, tailWord_5379872, baseEnd_5379872] using wordTrace_append hprefix tailTrace_5379872
  have hstable : (prefixWord ++ tailWord_5379872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379872).length < 2 ^ (prefixWord ++ tailWord_5379872).sum := by decide
  have hdescent : baseEnd_5379872 < baseStart_5379872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379875 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5]
def baseStart_5379875 : Nat := 118140960795 + 5379875 * 2 ^ 59
def prefixEnd_5379875 : Nat := 4983230072969 + 3 ^ 40 * 5379875 * 2
def baseEnd_5379875 : Nat := 2762461736107243948020911

theorem tailTrace_5379875 : CollatzResearch.WordTrace tailWord_5379875 prefixEnd_5379875 2762461736107243948020911 := by
  unfold tailWord_5379875
  simp only [CollatzResearch.WordTrace]
  refine ⟨196220161384639159344949079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130813440923092772896632719 196220161384639159344949079)
  ·
    refine ⟨294330242076958739017423619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196220161384639159344949079 294330242076958739017423619)
    ·
      refine ⟨441495363115438108526135429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294330242076958739017423619 441495363115438108526135429)
      ·
        refine ⟨82780380584144645348650393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 441495363115438108526135429 82780380584144645348650393)
        ·
          refine ⟨62085285438108484011487795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82780380584144645348650393 62085285438108484011487795)
          ·
            refine ⟨93127928157162726017231693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62085285438108484011487795 93127928157162726017231693)
            ·
              refine ⟨34922973058936022256461885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93127928157162726017231693 34922973058936022256461885)
              ·
                refine ⟨13096114897101008346173207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34922973058936022256461885 13096114897101008346173207)
                ·
                  refine ⟨19644172345651512519259811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13096114897101008346173207 19644172345651512519259811)
                  ·
                    refine ⟨29466258518477268778889717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19644172345651512519259811 29466258518477268778889717)
                    ·
                      refine ⟨2762461736107243948020911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29466258518477268778889717 2762461736107243948020911)
                      ·
                        rfl

theorem cell23_5379875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_5379875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379875 prefixEnd_5379875 := by exact prefixLift 5379875
  have htrace : WordTrace (prefixWord ++ tailWord_5379875) baseStart_5379875 baseEnd_5379875 := by
    simpa [prefixWord, tailWord_5379875, baseEnd_5379875] using wordTrace_append hprefix tailTrace_5379875
  have hstable : (prefixWord ++ tailWord_5379875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379875).length < 2 ^ (prefixWord ++ tailWord_5379875).sum := by decide
  have hdescent : baseEnd_5379875 < baseStart_5379875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379902 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5379902 : Nat := 118140960795 + 5379902 * 2 ^ 59
def prefixEnd_5379902 : Nat := 4983230072969 + 3 ^ 40 * 5379902 * 2
def baseEnd_5379902 : Nat := 2762475600084915342383287

theorem tailTrace_5379902 : CollatzResearch.WordTrace tailWord_5379902 prefixEnd_5379902 2762475600084915342383287 := by
  unfold tailWord_5379902
  simp only [CollatzResearch.WordTrace]
  refine ⟨24527643269442667869522745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130814097437027561970787973 24527643269442667869522745)
  ·
    refine ⟨18395732452082000902142059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24527643269442667869522745 18395732452082000902142059)
    ·
      refine ⟨27593598678123001353213089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18395732452082000902142059 27593598678123001353213089)
      ·
        refine ⟨20695199008592251014909817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27593598678123001353213089 20695199008592251014909817)
        ·
          refine ⟨15521399256444188261182363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20695199008592251014909817 15521399256444188261182363)
          ·
            refine ⟨23282098884666282391773545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15521399256444188261182363 23282098884666282391773545)
            ·
              refine ⟨17461574163499711793830159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23282098884666282391773545 17461574163499711793830159)
              ·
                refine ⟨26192361245249567690745239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17461574163499711793830159 26192361245249567690745239)
                ·
                  refine ⟨39288541867874351536117859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26192361245249567690745239 39288541867874351536117859)
                  ·
                    refine ⟨58932812801811527304176789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39288541867874351536117859 58932812801811527304176789)
                    ·
                      refine ⟨2762475600084915342383287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58932812801811527304176789 2762475600084915342383287)
                      ·
                        rfl

theorem cell23_5379902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5379902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379902 prefixEnd_5379902 := by exact prefixLift 5379902
  have htrace : WordTrace (prefixWord ++ tailWord_5379902) baseStart_5379902 baseEnd_5379902 := by
    simpa [prefixWord, tailWord_5379902, baseEnd_5379902] using wordTrace_append hprefix tailTrace_5379902
  have hstable : (prefixWord ++ tailWord_5379902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379902).length < 2 ^ (prefixWord ++ tailWord_5379902).sum := by decide
  have hdescent : baseEnd_5379902 < baseStart_5379902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379922 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_5379922 : Nat := 118140960795 + 5379922 * 2 ^ 59
def prefixEnd_5379922 : Nat := 4983230072969 + 3 ^ 40 * 5379922 * 2
def baseEnd_5379922 : Nat := 2762485869698005264133195

theorem tailTrace_5379922 : CollatzResearch.WordTrace tailWord_5379922 prefixEnd_5379922 2762485869698005264133195 := by
  unfold tailWord_5379922
  simp only [CollatzResearch.WordTrace]
  refine ⟨49055468903867221592977505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130814583743645924247940013 49055468903867221592977505)
  ·
    refine ⟨36791601677900416194733129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49055468903867221592977505 36791601677900416194733129)
    ·
      refine ⟨27593701258425312146049847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36791601677900416194733129 27593701258425312146049847)
      ·
        refine ⟨41390551887637968219074771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27593701258425312146049847 41390551887637968219074771)
        ·
          refine ⟨62085827831456952328612157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41390551887637968219074771 62085827831456952328612157)
          ·
            refine ⟨23282185436796357123229559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62085827831456952328612157 23282185436796357123229559)
            ·
              refine ⟨34923278155194535684844339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23282185436796357123229559 34923278155194535684844339)
              ·
                refine ⟨52384917232791803527266509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34923278155194535684844339 52384917232791803527266509)
                ·
                  refine ⟨19644343962296926322724941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52384917232791803527266509 19644343962296926322724941)
                  ·
                    refine ⟨7366628985861347371021853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19644343962296926322724941 7366628985861347371021853)
                    ·
                      refine ⟨2762485869698005264133195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366628985861347371021853 2762485869698005264133195)
                      ·
                        rfl

theorem cell23_5379922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_5379922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379922 prefixEnd_5379922 := by exact prefixLift 5379922
  have htrace : WordTrace (prefixWord ++ tailWord_5379922) baseStart_5379922 baseEnd_5379922 := by
    simpa [prefixWord, tailWord_5379922, baseEnd_5379922] using wordTrace_append hprefix tailTrace_5379922
  have hstable : (prefixWord ++ tailWord_5379922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379922).length < 2 ^ (prefixWord ++ tailWord_5379922).sum := by decide
  have hdescent : baseEnd_5379922 < baseStart_5379922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379946 : List Nat := [3, 1, 3, 4, 2, 1, 1, 8]
def baseStart_5379946 : Nat := 118140960795 + 5379946 * 2 ^ 59
def prefixEnd_5379946 : Nat := 4983230072969 + 3 ^ 40 * 5379946 * 2
def baseEnd_5379946 : Nat := 102314747897544932230855

theorem tailTrace_5379946 : CollatzResearch.WordTrace tailWord_5379946 prefixEnd_5379946 102314747897544932230855 := by
  unfold tailWord_5379946
  simp only [CollatzResearch.WordTrace]
  refine ⟨49055687741845484617695923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130815167311587958980522461 49055687741845484617695923)
  ·
    refine ⟨73583531612768226926543885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49055687741845484617695923 73583531612768226926543885)
    ·
      refine ⟨27593824354788085097453957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73583531612768226926543885 27593824354788085097453957)
      ·
        refine ⟨5173842066522765955772617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27593824354788085097453957 5173842066522765955772617)
        ·
          refine ⟨3880381549892074466829463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5173842066522765955772617 3880381549892074466829463)
          ·
            refine ⟨5820572324838111700244195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880381549892074466829463 5820572324838111700244195)
            ·
              refine ⟨8730858487257167550366293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5820572324838111700244195 8730858487257167550366293)
              ·
                refine ⟨102314747897544932230855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8730858487257167550366293 102314747897544932230855)
                ·
                  rfl

theorem cell23_5379946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_5379946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379946 prefixEnd_5379946 := by exact prefixLift 5379946
  have htrace : WordTrace (prefixWord ++ tailWord_5379946) baseStart_5379946 baseEnd_5379946 := by
    simpa [prefixWord, tailWord_5379946, baseEnd_5379946] using wordTrace_append hprefix tailTrace_5379946
  have hstable : (prefixWord ++ tailWord_5379946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379946).length < 2 ^ (prefixWord ++ tailWord_5379946).sum := by decide
  have hdescent : baseEnd_5379946 < baseStart_5379946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379949 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_5379949 : Nat := 118140960795 + 5379949 * 2 ^ 59
def prefixEnd_5379949 : Nat := 4983230072969 + 3 ^ 40 * 5379949 * 2
def baseEnd_5379949 : Nat := 2762499733675676658495571

theorem tailTrace_5379949 : CollatzResearch.WordTrace tailWord_5379949 prefixEnd_5379949 2762499733675676658495571 := by
  unfold tailWord_5379949
  simp only [CollatzResearch.WordTrace]
  refine ⟨196222860386371069983142901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130815240257580713322095267 196222860386371069983142901)
  ·
    refine ⟨18395893161222287810919647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 196222860386371069983142901 18395893161222287810919647)
    ·
      refine ⟨27593839741833431716379471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18395893161222287810919647 27593839741833431716379471)
      ·
        refine ⟨41390759612750147574569207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27593839741833431716379471 41390759612750147574569207)
        ·
          refine ⟨62086139419125221361853811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41390759612750147574569207 62086139419125221361853811)
          ·
            refine ⟨93129209128687832042780717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62086139419125221361853811 93129209128687832042780717)
            ·
              refine ⟨34923453423257937016042769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93129209128687832042780717 34923453423257937016042769)
              ·
                refine ⟨26192590067443452762032077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34923453423257937016042769 26192590067443452762032077)
                ·
                  refine ⟨9822221275291294785762029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26192590067443452762032077 9822221275291294785762029)
                  ·
                    refine ⟨3683332978234235544660761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9822221275291294785762029 3683332978234235544660761)
                    ·
                      refine ⟨2762499733675676658495571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683332978234235544660761 2762499733675676658495571)
                      ·
                        rfl

theorem cell23_5379949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_5379949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379949 prefixEnd_5379949 := by exact prefixLift 5379949
  have htrace : WordTrace (prefixWord ++ tailWord_5379949) baseStart_5379949 baseEnd_5379949 := by
    simpa [prefixWord, tailWord_5379949, baseEnd_5379949] using wordTrace_append hprefix tailTrace_5379949
  have hstable : (prefixWord ++ tailWord_5379949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379949).length < 2 ^ (prefixWord ++ tailWord_5379949).sum := by decide
  have hdescent : baseEnd_5379949 < baseStart_5379949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379979 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 4, 2, 2]
def baseStart_5379979 : Nat := 118140960795 + 5379979 * 2 ^ 59
def prefixEnd_5379979 : Nat := 4983230072969 + 3 ^ 40 * 5379979 * 2
def baseEnd_5379979 : Nat := 2762515138095311541120433

theorem tailTrace_5379979 : CollatzResearch.WordTrace tailWord_5379979 prefixEnd_5379979 2762515138095311541120433 := by
  unfold tailWord_5379979
  simp only [CollatzResearch.WordTrace]
  refine ⟨196223954576262385106734991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130815969717508256737823327 196223954576262385106734991)
  ·
    refine ⟨294335931864393577660102487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196223954576262385106734991 294335931864393577660102487)
    ·
      refine ⟨441503897796590366490153731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294335931864393577660102487 441503897796590366490153731)
      ·
        refine ⟨662255846694885549735230597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441503897796590366490153731 662255846694885549735230597)
        ·
          refine ⟨124172971255291040575355737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 662255846694885549735230597 124172971255291040575355737)
          ·
            refine ⟨93129728441468280431516803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124172971255291040575355737 93129728441468280431516803)
            ·
              refine ⟨139694592662202420647275205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93129728441468280431516803 139694592662202420647275205)
              ·
                refine ⟨26192736124162953871364101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139694592662202420647275205 26192736124162953871364101)
                ·
                  refine ⟨4911138023280553850880769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26192736124162953871364101 4911138023280553850880769)
                  ·
                    refine ⟨3683353517460415388160577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4911138023280553850880769 3683353517460415388160577)
                    ·
                      refine ⟨2762515138095311541120433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683353517460415388160577 2762515138095311541120433)
                      ·
                        rfl

theorem cell23_5379979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 2, 2].length) (baseStart_5379979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379979 prefixEnd_5379979 := by exact prefixLift 5379979
  have htrace : WordTrace (prefixWord ++ tailWord_5379979) baseStart_5379979 baseEnd_5379979 := by
    simpa [prefixWord, tailWord_5379979, baseEnd_5379979] using wordTrace_append hprefix tailTrace_5379979
  have hstable : (prefixWord ++ tailWord_5379979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379979).length < 2 ^ (prefixWord ++ tailWord_5379979).sum := by decide
  have hdescent : baseEnd_5379979 < baseStart_5379979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5379990 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5379990 : Nat := 118140960795 + 5379990 * 2 ^ 59
def prefixEnd_5379990 : Nat := 4983230072969 + 3 ^ 40 * 5379990 * 2
def baseEnd_5379990 : Nat := 2762520786382510998082883

theorem tailTrace_5379990 : CollatzResearch.WordTrace tailWord_5379990 prefixEnd_5379990 2762520786382510998082883 := by
  unfold tailWord_5379990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12264022236201408374086589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130816237186148355990256949 12264022236201408374086589)
  ·
    refine ⟨4599008338575528140282471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12264022236201408374086589 4599008338575528140282471)
    ·
      refine ⟨6898512507863292210423707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599008338575528140282471 6898512507863292210423707)
      ·
        refine ⟨10347768761794938315635561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6898512507863292210423707 10347768761794938315635561)
        ·
          refine ⟨7760826571346203736726671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10347768761794938315635561 7760826571346203736726671)
          ·
            refine ⟨11641239857019305605090007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760826571346203736726671 11641239857019305605090007)
            ·
              refine ⟨17461859785528958407635011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641239857019305605090007 17461859785528958407635011)
              ·
                refine ⟨26192789678293437611452517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17461859785528958407635011 26192789678293437611452517)
                ·
                  refine ⟨4911148064680019552147347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26192789678293437611452517 4911148064680019552147347)
                  ·
                    refine ⟨7366722097020029328221021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4911148064680019552147347 7366722097020029328221021)
                    ·
                      refine ⟨2762520786382510998082883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366722097020029328221021 2762520786382510998082883)
                      ·
                        rfl

theorem cell23_5379990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5379990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5379990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5379990 prefixEnd_5379990 := by exact prefixLift 5379990
  have htrace : WordTrace (prefixWord ++ tailWord_5379990) baseStart_5379990 baseEnd_5379990 := by
    simpa [prefixWord, tailWord_5379990, baseEnd_5379990] using wordTrace_append hprefix tailTrace_5379990
  have hstable : (prefixWord ++ tailWord_5379990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5379990).length < 2 ^ (prefixWord ++ tailWord_5379990).sum := by decide
  have hdescent : baseEnd_5379990 < baseStart_5379990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5379990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380015 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 3, 7]
def baseStart_5380015 : Nat := 118140960795 + 5380015 * 2 ^ 59
def prefixEnd_5380015 : Nat := 4983230072969 + 3 ^ 40 * 5380015 * 2
def baseEnd_5380015 : Nat := 920844541132957800090089

theorem tailTrace_5380015 : CollatzResearch.WordTrace tailWord_5380015 prefixEnd_5380015 920844541132957800090089 := by
  unfold tailWord_5380015
  simp only [CollatzResearch.WordTrace]
  refine ⟨196225267604131963255045499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130816845069421308836696999 196225267604131963255045499)
  ·
    refine ⟨294337901406197944882568249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196225267604131963255045499 294337901406197944882568249)
    ·
      refine ⟨220753426054648458661926187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294337901406197944882568249 220753426054648458661926187)
      ·
        refine ⟨331130139081972687992889281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220753426054648458661926187 331130139081972687992889281)
        ·
          refine ⟨248347604311479515994666961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331130139081972687992889281 248347604311479515994666961)
          ·
            refine ⟨186260703233609636996000221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248347604311479515994666961 186260703233609636996000221)
            ·
              refine ⟨69847763712603613873500083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186260703233609636996000221 69847763712603613873500083)
              ·
                refine ⟨104771645568905420810250125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69847763712603613873500083 104771645568905420810250125)
                ·
                  refine ⟨39289367088339532803843797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104771645568905420810250125 39289367088339532803843797)
                  ·
                    refine ⟨920844541132957800090089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39289367088339532803843797 920844541132957800090089)
                    ·
                      rfl

theorem cell23_5380015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_5380015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380015 prefixEnd_5380015 := by exact prefixLift 5380015
  have htrace : WordTrace (prefixWord ++ tailWord_5380015) baseStart_5380015 baseEnd_5380015 := by
    simpa [prefixWord, tailWord_5380015, baseEnd_5380015] using wordTrace_append hprefix tailTrace_5380015
  have hstable : (prefixWord ++ tailWord_5380015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380015).length < 2 ^ (prefixWord ++ tailWord_5380015).sum := by decide
  have hdescent : baseEnd_5380015 < baseStart_5380015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380032 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_5380032 : Nat := 118140960795 + 5380032 * 2 ^ 59
def prefixEnd_5380032 : Nat := 4983230072969 + 3 ^ 40 * 5380032 * 2
def baseEnd_5380032 : Nat := 920847450856666611252563

theorem tailTrace_5380032 : CollatzResearch.WordTrace tailWord_5380032 prefixEnd_5380032 920847450856666611252563 := by
  unfold tailWord_5380032
  simp only [CollatzResearch.WordTrace]
  refine ⟨98112943822535187579207175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130817258430046916772276233 98112943822535187579207175)
  ·
    refine ⟨147169415733802781368810763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98112943822535187579207175 147169415733802781368810763)
    ·
      refine ⟨220754123600704172053216145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147169415733802781368810763 220754123600704172053216145)
      ·
        refine ⟨165565592700528129039912109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220754123600704172053216145 165565592700528129039912109)
        ·
          refine ⟨62087097262698048389967041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165565592700528129039912109 62087097262698048389967041)
          ·
            refine ⟨46565322947023536292475281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62087097262698048389967041 46565322947023536292475281)
            ·
              refine ⟨34923992210267652219356461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46565322947023536292475281 34923992210267652219356461)
              ·
                refine ⟨13096497078850369582258673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34923992210267652219356461 13096497078850369582258673)
                ·
                  refine ⟨9822372809137777186694005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13096497078850369582258673 9822372809137777186694005)
                  ·
                    refine ⟨920847450856666611252563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9822372809137777186694005 920847450856666611252563)
                    ·
                      rfl

theorem cell23_5380032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_5380032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380032 prefixEnd_5380032 := by exact prefixLift 5380032
  have htrace : WordTrace (prefixWord ++ tailWord_5380032) baseStart_5380032 baseEnd_5380032 := by
    simpa [prefixWord, tailWord_5380032, baseEnd_5380032] using wordTrace_append hprefix tailTrace_5380032
  have hstable : (prefixWord ++ tailWord_5380032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380032).length < 2 ^ (prefixWord ++ tailWord_5380032).sum := by decide
  have hdescent : baseEnd_5380032 < baseStart_5380032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380089 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_5380089 : Nat := 118140960795 + 5380089 * 2 ^ 59
def prefixEnd_5380089 : Nat := 4983230072969 + 3 ^ 40 * 5380089 * 2
def baseEnd_5380089 : Nat := 2762571620967306110744927

theorem tailTrace_5380089 : CollatzResearch.WordTrace tailWord_5380089 prefixEnd_5380089 2762571620967306110744927 := by
  unfold tailWord_5380089
  simp only [CollatzResearch.WordTrace]
  refine ⟨196227966605863873893239321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130818644403909249262159547 196227966605863873893239321)
  ·
    refine ⟨147170974954397905419929491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196227966605863873893239321 147170974954397905419929491)
    ·
      refine ⟨220756462431596858129894237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147170974954397905419929491 220756462431596858129894237)
      ·
        refine ⟨82783673411848821798710339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220756462431596858129894237 82783673411848821798710339)
        ·
          refine ⟨124175510117773232698065509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82783673411848821798710339 124175510117773232698065509)
          ·
            refine ⟨23282908147082481130887283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124175510117773232698065509 23282908147082481130887283)
            ·
              refine ⟨34924362220623721696330925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23282908147082481130887283 34924362220623721696330925)
              ·
                refine ⟨13096635832733895636124097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34924362220623721696330925 13096635832733895636124097)
                ·
                  refine ⟨9822476874550421727093073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13096635832733895636124097 9822476874550421727093073)
                  ·
                    refine ⟨7366857655912816295319805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9822476874550421727093073 7366857655912816295319805)
                    ·
                      refine ⟨2762571620967306110744927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7366857655912816295319805 2762571620967306110744927)
                      ·
                        rfl

theorem cell23_5380089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_5380089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380089 prefixEnd_5380089 := by exact prefixLift 5380089
  have htrace : WordTrace (prefixWord ++ tailWord_5380089) baseStart_5380089 baseEnd_5380089 := by
    simpa [prefixWord, tailWord_5380089, baseEnd_5380089] using wordTrace_append hprefix tailTrace_5380089
  have hstable : (prefixWord ++ tailWord_5380089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380089).length < 2 ^ (prefixWord ++ tailWord_5380089).sum := by decide
  have hdescent : baseEnd_5380089 < baseStart_5380089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380146 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2]
def baseStart_5380146 : Nat := 118140960795 + 5380146 * 2 ^ 59
def prefixEnd_5380146 : Nat := 4983230072969 + 3 ^ 40 * 5380146 * 2
def baseEnd_5380146 : Nat := 2762600889364612387732165

theorem tailTrace_5380146 : CollatzResearch.WordTrace tailWord_5380146 prefixEnd_5380146 2762600889364612387732165 := by
  unfold tailWord_5380146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49057511391664343157016073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130820030377771581752042861 49057511391664343157016073)
  ·
    refine ⟨36793133543748257367762055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49057511391664343157016073 36793133543748257367762055)
    ·
      refine ⟨55189700315622386051643083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36793133543748257367762055 55189700315622386051643083)
      ·
        refine ⟨82784550473433579077464625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55189700315622386051643083 82784550473433579077464625)
        ·
          refine ⟨62088412855075184308098469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82784550473433579077464625 62088412855075184308098469)
          ·
            refine ⟨11641577410326597057768463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62088412855075184308098469 11641577410326597057768463)
            ·
              refine ⟨17462366115489895586652695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641577410326597057768463 17462366115489895586652695)
              ·
                refine ⟨26193549173234843379979043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17462366115489895586652695 26193549173234843379979043)
                ·
                  refine ⟨39290323759852265069968565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26193549173234843379979043 39290323759852265069968565)
                  ·
                    refine ⟨3683467852486149850309553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39290323759852265069968565 3683467852486149850309553)
                    ·
                      refine ⟨2762600889364612387732165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683467852486149850309553 2762600889364612387732165)
                      ·
                        rfl

theorem cell23_5380146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_5380146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380146 prefixEnd_5380146 := by exact prefixLift 5380146
  have htrace : WordTrace (prefixWord ++ tailWord_5380146) baseStart_5380146 baseEnd_5380146 := by
    simpa [prefixWord, tailWord_5380146, baseEnd_5380146] using wordTrace_append hprefix tailTrace_5380146
  have hstable : (prefixWord ++ tailWord_5380146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380146).length < 2 ^ (prefixWord ++ tailWord_5380146).sum := by decide
  have hdescent : baseEnd_5380146 < baseStart_5380146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380169 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 4, 4]
def baseStart_5380169 : Nat := 118140960795 + 5380169 * 2 ^ 59
def prefixEnd_5380169 : Nat := 4983230072969 + 3 ^ 40 * 5380169 * 2
def baseEnd_5380169 : Nat := 920870899806555265914853

theorem tailTrace_5380169 : CollatzResearch.WordTrace tailWord_5380169 prefixEnd_5380169 920870899806555265914853 := by
  unfold tailWord_5380169
  simp only [CollatzResearch.WordTrace]
  refine ⟨196230884445574047556151561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130820589630382698370767707 196230884445574047556151561)
  ·
    refine ⟨147173163334180535667113671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196230884445574047556151561 147173163334180535667113671)
    ·
      refine ⟨220759745001270803500670507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147173163334180535667113671 220759745001270803500670507)
      ·
        refine ⟨331139617501906205251005761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220759745001270803500670507 331139617501906205251005761)
        ·
          refine ⟨248354713126429653938254321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331139617501906205251005761 248354713126429653938254321)
          ·
            refine ⟨186266034844822240453690741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248354713126429653938254321 186266034844822240453690741)
            ·
              refine ⟨17462440766702085042533507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186266034844822240453690741 17462440766702085042533507)
              ·
                refine ⟨26193661150053127563800261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17462440766702085042533507 26193661150053127563800261)
                ·
                  refine ⟨4911311465634961418212549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26193661150053127563800261 4911311465634961418212549)
                  ·
                    refine ⟨920870899806555265914853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4911311465634961418212549 920870899806555265914853)
                    ·
                      rfl

theorem cell23_5380169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 4].length) (baseStart_5380169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380169 prefixEnd_5380169 := by exact prefixLift 5380169
  have htrace : WordTrace (prefixWord ++ tailWord_5380169) baseStart_5380169 baseEnd_5380169 := by
    simpa [prefixWord, tailWord_5380169, baseEnd_5380169] using wordTrace_append hprefix tailTrace_5380169
  have hstable : (prefixWord ++ tailWord_5380169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380169).length < 2 ^ (prefixWord ++ tailWord_5380169).sum := by decide
  have hdescent : baseEnd_5380169 < baseStart_5380169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380196 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_5380196 : Nat := 118140960795 + 5380196 * 2 ^ 59
def prefixEnd_5380196 : Nat := 4983230072969 + 3 ^ 40 * 5380196 * 2
def baseEnd_5380196 : Nat := 2762626563397337192106935

theorem tailTrace_5380196 : CollatzResearch.WordTrace tailWord_5380196 prefixEnd_5380196 2762626563397337192106935 := by
  unfold tailWord_5380196
  simp only [CollatzResearch.WordTrace]
  refine ⟨98115934608238115583692221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130821246144317487444922961 98115934608238115583692221)
  ·
    refine ⟨36793475478089293343884583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98115934608238115583692221 36793475478089293343884583)
    ·
      refine ⟨55190213217133940015826875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36793475478089293343884583 55190213217133940015826875)
      ·
        refine ⟨82785319825700910023740313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55190213217133940015826875 82785319825700910023740313)
        ·
          refine ⟨62088989869275682517805235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82785319825700910023740313 62088989869275682517805235)
          ·
            refine ⟨93133484803913523776707853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62088989869275682517805235 93133484803913523776707853)
            ·
              refine ⟨34925056801467571416265445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93133484803913523776707853 34925056801467571416265445)
              ·
                refine ⟨6548448150275169640549771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34925056801467571416265445 6548448150275169640549771)
                ·
                  refine ⟨9822672225412754460824657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6548448150275169640549771 9822672225412754460824657)
                  ·
                    refine ⟨7367004169059565845618493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9822672225412754460824657 7367004169059565845618493)
                    ·
                      refine ⟨2762626563397337192106935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367004169059565845618493 2762626563397337192106935)
                      ·
                        rfl

theorem cell23_5380196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_5380196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380196 prefixEnd_5380196 := by exact prefixLift 5380196
  have htrace : WordTrace (prefixWord ++ tailWord_5380196) baseStart_5380196 baseEnd_5380196 := by
    simpa [prefixWord, tailWord_5380196, baseEnd_5380196] using wordTrace_append hprefix tailTrace_5380196
  have hstable : (prefixWord ++ tailWord_5380196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380196).length < 2 ^ (prefixWord ++ tailWord_5380196).sum := by decide
  have hdescent : baseEnd_5380196 < baseStart_5380196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380209 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_5380209 : Nat := 118140960795 + 5380209 * 2 ^ 59
def prefixEnd_5380209 : Nat := 4983230072969 + 3 ^ 40 * 5380209 * 2
def baseEnd_5380209 : Nat := 2762633238645845641244375

theorem tailTrace_5380209 : CollatzResearch.WordTrace tailWord_5380209 prefixEnd_5380209 2762633238645845641244375 := by
  unfold tailWord_5380209
  simp only [CollatzResearch.WordTrace]
  refine ⟨196232343365429134387607681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130821562243619422925071787 196232343365429134387607681)
  ·
    refine ⟨147174257524071850790705761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196232343365429134387607681 147174257524071850790705761)
    ·
      refine ⟨110380693143053888093029321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147174257524071850790705761 110380693143053888093029321)
      ·
        refine ⟨82785519857290416069771991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110380693143053888093029321 82785519857290416069771991)
        ·
          refine ⟨124178279785935624104657987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82785519857290416069771991 124178279785935624104657987)
          ·
            refine ⟨186267419678903436156986981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124178279785935624104657987 186267419678903436156986981)
            ·
              refine ⟨34925141189794394279435059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186267419678903436156986981 34925141189794394279435059)
              ·
                refine ⟨52387711784691591419152589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34925141189794394279435059 52387711784691591419152589)
                ·
                  refine ⟨19645391919259346782182221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52387711784691591419152589 19645391919259346782182221)
                  ·
                    refine ⟨7367021969722255043318333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19645391919259346782182221 7367021969722255043318333)
                    ·
                      refine ⟨2762633238645845641244375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367021969722255043318333 2762633238645845641244375)
                      ·
                        rfl

theorem cell23_5380209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_5380209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380209 prefixEnd_5380209 := by exact prefixLift 5380209
  have htrace : WordTrace (prefixWord ++ tailWord_5380209) baseStart_5380209 baseEnd_5380209 := by
    simpa [prefixWord, tailWord_5380209, baseEnd_5380209] using wordTrace_append hprefix tailTrace_5380209
  have hstable : (prefixWord ++ tailWord_5380209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380209).length < 2 ^ (prefixWord ++ tailWord_5380209).sum := by decide
  have hdescent : baseEnd_5380209 < baseStart_5380209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380227 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 1, 2, 2]
def baseStart_5380227 : Nat := 118140960795 + 5380227 * 2 ^ 59
def prefixEnd_5380227 : Nat := 4983230072969 + 3 ^ 40 * 5380227 * 2
def baseEnd_5380227 : Nat := 2762642481297626570819293

theorem tailTrace_5380227 : CollatzResearch.WordTrace tailWord_5380227 prefixEnd_5380227 2762642481297626570819293 := by
  unfold tailWord_5380227
  simp only [CollatzResearch.WordTrace]
  refine ⟨196232999879363923461762935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130821999919575948974508623 196232999879363923461762935)
  ·
    refine ⟨294349499819045885192644403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196232999879363923461762935 294349499819045885192644403)
    ·
      refine ⟨441524249728568827788966605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294349499819045885192644403 441524249728568827788966605)
      ·
        refine ⟨165571593648213310420862477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 441524249728568827788966605 165571593648213310420862477)
        ·
          refine ⟨62089347618079991407823429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165571593648213310420862477 62089347618079991407823429)
          ·
            refine ⟨11641752678389998388966893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62089347618079991407823429 11641752678389998388966893)
            ·
              refine ⟨4365657254396249395862585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11641752678389998388966893 4365657254396249395862585)
              ·
                refine ⟨3274242940797187046896939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4365657254396249395862585 3274242940797187046896939)
                ·
                  refine ⟨4911364411195780570345409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274242940797187046896939 4911364411195780570345409)
                  ·
                    refine ⟨3683523308396835427759057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4911364411195780570345409 3683523308396835427759057)
                    ·
                      refine ⟨2762642481297626570819293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683523308396835427759057 2762642481297626570819293)
                      ·
                        rfl

theorem cell23_5380227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_5380227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380227 prefixEnd_5380227 := by exact prefixLift 5380227
  have htrace : WordTrace (prefixWord ++ tailWord_5380227) baseStart_5380227 baseEnd_5380227 := by
    simpa [prefixWord, tailWord_5380227, baseEnd_5380227] using wordTrace_append hprefix tailTrace_5380227
  have hstable : (prefixWord ++ tailWord_5380227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380227).length < 2 ^ (prefixWord ++ tailWord_5380227).sum := by decide
  have hdescent : baseEnd_5380227 < baseStart_5380227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380253 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_5380253 : Nat := 118140960795 + 5380253 * 2 ^ 59
def prefixEnd_5380253 : Nat := 4983230072969 + 3 ^ 40 * 5380253 * 2
def baseEnd_5380253 : Nat := 2762655831794643469094173

theorem tailTrace_5380253 : CollatzResearch.WordTrace tailWord_5380253 prefixEnd_5380253 2762655831794643469094173 := by
  unfold tailWord_5380253
  simp only [CollatzResearch.WordTrace]
  refine ⟨196233948177269729902209413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130822632118179819934806275 196233948177269729902209413)
  ·
    refine ⟨36793865283238074356664265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196233948177269729902209413 36793865283238074356664265)
    ·
      refine ⟨27595398962428555767498199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36793865283238074356664265 27595398962428555767498199)
      ·
        refine ⟨41393098443642833651247299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27595398962428555767498199 41393098443642833651247299)
        ·
          refine ⟨62089647665464250476870949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41393098443642833651247299 62089647665464250476870949)
          ·
            refine ⟨11641808937274546964413303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62089647665464250476870949 11641808937274546964413303)
            ·
              refine ⟨17462713405911820446619955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641808937274546964413303 17462713405911820446619955)
              ·
                refine ⟨26194070108867730669929933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17462713405911820446619955 26194070108867730669929933)
                ·
                  refine ⟨9822776290825399001223725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26194070108867730669929933 9822776290825399001223725)
                  ·
                    refine ⟨3683541109059524625458897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9822776290825399001223725 3683541109059524625458897)
                    ·
                      refine ⟨2762655831794643469094173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683541109059524625458897 2762655831794643469094173)
                      ·
                        rfl

theorem cell23_5380253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_5380253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380253 prefixEnd_5380253 := by exact prefixLift 5380253
  have htrace : WordTrace (prefixWord ++ tailWord_5380253) baseStart_5380253 baseEnd_5380253 := by
    simpa [prefixWord, tailWord_5380253, baseEnd_5380253] using wordTrace_append hprefix tailTrace_5380253
  have hstable : (prefixWord ++ tailWord_5380253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380253).length < 2 ^ (prefixWord ++ tailWord_5380253).sum := by decide
  have hdescent : baseEnd_5380253 < baseStart_5380253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380277 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5380277 : Nat := 118140960795 + 5380277 * 2 ^ 59
def prefixEnd_5380277 : Nat := 4983230072969 + 3 ^ 40 * 5380277 * 2
def baseEnd_5380277 : Nat := 2762668155330351375194063

theorem tailTrace_5380277 : CollatzResearch.WordTrace tailWord_5380277 prefixEnd_5380277 2762668155330351375194063 := by
  unfold tailWord_5380277
  simp only [CollatzResearch.WordTrace]
  refine ⟨196234823529182782001083085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130823215686121854667388723 196234823529182782001083085)
  ·
    refine ⟨73588058823443543250406157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196234823529182782001083085 73588058823443543250406157)
    ·
      refine ⟨27595522058791328718902309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73588058823443543250406157 27595522058791328718902309)
      ·
        refine ⟨5174160386023374134794183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27595522058791328718902309 5174160386023374134794183)
        ·
          refine ⟨7761240579035061202191275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174160386023374134794183 7761240579035061202191275)
          ·
            refine ⟨11641860868552591803286913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7761240579035061202191275 11641860868552591803286913)
            ·
              refine ⟨8731395651414443852465185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11641860868552591803286913 8731395651414443852465185)
              ·
                refine ⟨6548546738560832889348889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8731395651414443852465185 6548546738560832889348889)
                ·
                  refine ⟨4911410053920624667011667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6548546738560832889348889 4911410053920624667011667)
                  ·
                    refine ⟨7367115080880937000517501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4911410053920624667011667 7367115080880937000517501)
                    ·
                      refine ⟨2762668155330351375194063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367115080880937000517501 2762668155330351375194063)
                      ·
                        rfl

theorem cell23_5380277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5380277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380277 prefixEnd_5380277 := by exact prefixLift 5380277
  have htrace : WordTrace (prefixWord ++ tailWord_5380277) baseStart_5380277 baseEnd_5380277 := by
    simpa [prefixWord, tailWord_5380277, baseEnd_5380277] using wordTrace_append hprefix tailTrace_5380277
  have hstable : (prefixWord ++ tailWord_5380277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380277).length < 2 ^ (prefixWord ++ tailWord_5380277).sum := by decide
  have hdescent : baseEnd_5380277 < baseStart_5380277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380306 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_5380306 : Nat := 118140960795 + 5380306 * 2 ^ 59
def prefixEnd_5380306 : Nat := 4983230072969 + 3 ^ 40 * 5380306 * 2
def baseEnd_5380306 : Nat := 306964782918814640192381

theorem tailTrace_5380306 : CollatzResearch.WordTrace tailWord_5380306 prefixEnd_5380306 306964782918814640192381 := by
  unfold tailWord_5380306
  simp only [CollatzResearch.WordTrace]
  refine ⟨49058970311519429988472193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130823920830718479969259181 49058970311519429988472193)
  ·
    refine ⟨36794227733639572491354145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49058970311519429988472193 36794227733639572491354145)
    ·
      refine ⟨27595670800229679368515609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36794227733639572491354145 27595670800229679368515609)
      ·
        refine ⟨20696753100172259526386707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27595670800229679368515609 20696753100172259526386707)
        ·
          refine ⟨31045129650258389289580061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20696753100172259526386707 31045129650258389289580061)
          ·
            refine ⟨11641923618846895983592523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31045129650258389289580061 11641923618846895983592523)
            ·
              refine ⟨17462885428270343975388785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641923618846895983592523 17462885428270343975388785)
              ·
                refine ⟨13097164071202757981541589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17462885428270343975388785 13097164071202757981541589)
                ·
                  refine ⟨306964782918814640192381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13097164071202757981541589 306964782918814640192381)
                  ·
                    rfl

theorem cell23_5380306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_5380306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380306 prefixEnd_5380306 := by exact prefixLift 5380306
  have htrace : WordTrace (prefixWord ++ tailWord_5380306) baseStart_5380306 baseEnd_5380306 := by
    simpa [prefixWord, tailWord_5380306, baseEnd_5380306] using wordTrace_append hprefix tailTrace_5380306
  have hstable : (prefixWord ++ tailWord_5380306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380306).length < 2 ^ (prefixWord ++ tailWord_5380306).sum := by decide
  have hdescent : baseEnd_5380306 < baseStart_5380306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380376 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_5380376 : Nat := 118140960795 + 5380376 * 2 ^ 59
def prefixEnd_5380376 : Nat := 4983230072969 + 3 ^ 40 * 5380376 * 2
def baseEnd_5380376 : Nat := 2762718989915146487856107

theorem tailTrace_5380376 : CollatzResearch.WordTrace tailWord_5380376 prefixEnd_5380376 2762718989915146487856107 := by
  unfold tailWord_5380376
  simp only [CollatzResearch.WordTrace]
  refine ⟨98119217177912060954468491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130825622903882747939291321 98119217177912060954468491)
  ·
    refine ⟨147178825766868091431702737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98119217177912060954468491 147178825766868091431702737)
    ·
      refine ⟨110384119325151068573777053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147178825766868091431702737 110384119325151068573777053)
      ·
        refine ⟨41394044746931650715166395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110384119325151068573777053 41394044746931650715166395)
        ·
          refine ⟨62091067120397476072749593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41394044746931650715166395 62091067120397476072749593)
          ·
            refine ⟨46568300340298107054562195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62091067120397476072749593 46568300340298107054562195)
            ·
              refine ⟨69852450510447160581843293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46568300340298107054562195 69852450510447160581843293)
              ·
                refine ⟨26194668941417685218191235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69852450510447160581843293 26194668941417685218191235)
                ·
                  refine ⟨39292003412126527827286853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26194668941417685218191235 39292003412126527827286853)
                  ·
                    refine ⟨7367250639773723967616285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39292003412126527827286853 7367250639773723967616285)
                    ·
                      refine ⟨2762718989915146487856107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367250639773723967616285 2762718989915146487856107)
                      ·
                        rfl

theorem cell23_5380376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_5380376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380376 prefixEnd_5380376 := by exact prefixLift 5380376
  have htrace : WordTrace (prefixWord ++ tailWord_5380376) baseStart_5380376 baseEnd_5380376 := by
    simpa [prefixWord, tailWord_5380376, baseEnd_5380376] using wordTrace_append hprefix tailTrace_5380376
  have hstable : (prefixWord ++ tailWord_5380376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380376).length < 2 ^ (prefixWord ++ tailWord_5380376).sum := by decide
  have hdescent : baseEnd_5380376 < baseStart_5380376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380379 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 8]
def baseStart_5380379 : Nat := 118140960795 + 5380379 * 2 ^ 59
def prefixEnd_5380379 : Nat := 4983230072969 + 3 ^ 40 * 5380379 * 2
def baseEnd_5380379 : Nat := 306968947817456664013177

theorem tailTrace_5380379 : CollatzResearch.WordTrace tailWord_5380379 prefixEnd_5380379 306968947817456664013177 := by
  unfold tailWord_5380379
  simp only [CollatzResearch.WordTrace]
  refine ⟨196238543774813253421296191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130825695849875502280864127 196238543774813253421296191)
  ·
    refine ⟨294357815662219880131944287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196238543774813253421296191 294357815662219880131944287)
    ·
      refine ⟨441536723493329820197916431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294357815662219880131944287 441536723493329820197916431)
      ·
        refine ⟨662305085239994730296874647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441536723493329820197916431 662305085239994730296874647)
        ·
          refine ⟨993457627859992095445311971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662305085239994730296874647 993457627859992095445311971)
          ·
            refine ⟨1490186441789988143167967957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993457627859992095445311971 1490186441789988143167967957)
            ·
              refine ⟨34926244729452847105499249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1490186441789988143167967957 34926244729452847105499249)
              ·
                refine ⟨26194683547089635329124437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34926244729452847105499249 26194683547089635329124437)
                ·
                  refine ⟨306968947817456664013177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26194683547089635329124437 306968947817456664013177)
                  ·
                    rfl

theorem cell23_5380379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 8].length) (baseStart_5380379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380379 prefixEnd_5380379 := by exact prefixLift 5380379
  have htrace : WordTrace (prefixWord ++ tailWord_5380379) baseStart_5380379 baseEnd_5380379 := by
    simpa [prefixWord, tailWord_5380379, baseEnd_5380379] using wordTrace_append hprefix tailTrace_5380379
  have hstable : (prefixWord ++ tailWord_5380379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380379).length < 2 ^ (prefixWord ++ tailWord_5380379).sum := by decide
  have hdescent : baseEnd_5380379 < baseStart_5380379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380399 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_5380399 : Nat := 118140960795 + 5380399 * 2 ^ 59
def prefixEnd_5380399 : Nat := 4983230072969 + 3 ^ 40 * 5380399 * 2
def baseEnd_5380399 : Nat := 2762730799970199897868501

theorem tailTrace_5380399 : CollatzResearch.WordTrace tailWord_5380399 prefixEnd_5380399 2762730799970199897868501 := by
  unfold tailWord_5380399
  simp only [CollatzResearch.WordTrace]
  refine ⟨196239273234740796837024251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130826182156493864558016167 196239273234740796837024251)
  ·
    refine ⟨294358909852111195255536377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196239273234740796837024251 294358909852111195255536377)
    ·
      refine ⟨220769182389083396441652283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294358909852111195255536377 220769182389083396441652283)
      ·
        refine ⟨331153773583625094662478425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220769182389083396441652283 331153773583625094662478425)
        ·
          refine ⟨248365330187718820996858819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331153773583625094662478425 248365330187718820996858819)
          ·
            refine ⟨372547995281578231495288229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248365330187718820996858819 372547995281578231495288229)
            ·
              refine ⟨69852749115295918405366543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 372547995281578231495288229 69852749115295918405366543)
              ·
                refine ⟨104779123672943877608049815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69852749115295918405366543 104779123672943877608049815)
                ·
                  refine ⟨157168685509415816412074723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104779123672943877608049815 157168685509415816412074723)
                  ·
                    refine ⟨235753028264123724618112085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157168685509415816412074723 235753028264123724618112085)
                    ·
                      refine ⟨2762730799970199897868501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 235753028264123724618112085 2762730799970199897868501)
                      ·
                        rfl

theorem cell23_5380399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_5380399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380399 prefixEnd_5380399 := by exact prefixLift 5380399
  have htrace : WordTrace (prefixWord ++ tailWord_5380399) baseStart_5380399 baseEnd_5380399 := by
    simpa [prefixWord, tailWord_5380399, baseEnd_5380399] using wordTrace_append hprefix tailTrace_5380399
  have hstable : (prefixWord ++ tailWord_5380399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380399).length < 2 ^ (prefixWord ++ tailWord_5380399).sum := by decide
  have hdescent : baseEnd_5380399 < baseStart_5380399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380423 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_5380423 : Nat := 118140960795 + 5380423 * 2 ^ 59
def prefixEnd_5380423 : Nat := 4983230072969 + 3 ^ 40 * 5380423 * 2
def baseEnd_5380423 : Nat := 2762743123505907803968391

theorem tailTrace_5380423 : CollatzResearch.WordTrace tailWord_5380423 prefixEnd_5380423 2762743123505907803968391 := by
  unfold tailWord_5380423
  simp only [CollatzResearch.WordTrace]
  refine ⟨196240148586653848935897923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130826765724435899290598615 196240148586653848935897923)
  ·
    refine ⟨294360222879980773403846885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196240148586653848935897923 294360222879980773403846885)
    ·
      refine ⟨55192541789996395013221291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294360222879980773403846885 55192541789996395013221291)
      ·
        refine ⟨82788812684994592519831937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55192541789996395013221291 82788812684994592519831937)
        ·
          refine ⟨62091609513745944389873953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82788812684994592519831937 62091609513745944389873953)
          ·
            refine ⟨46568707135309458292405465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62091609513745944389873953 46568707135309458292405465)
            ·
              refine ⟨34926530351482093719304099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46568707135309458292405465 34926530351482093719304099)
              ·
                refine ⟨52389795527223140578956149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34926530351482093719304099 52389795527223140578956149)
                ·
                  refine ⟨4911543330677169429277139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52389795527223140578956149 4911543330677169429277139)
                  ·
                    refine ⟨7367314996015754143915709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4911543330677169429277139 7367314996015754143915709)
                    ·
                      refine ⟨2762743123505907803968391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367314996015754143915709 2762743123505907803968391)
                      ·
                        rfl

theorem cell23_5380423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_5380423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380423 prefixEnd_5380423 := by exact prefixLift 5380423
  have htrace : WordTrace (prefixWord ++ tailWord_5380423) baseStart_5380423 baseEnd_5380423 := by
    simpa [prefixWord, tailWord_5380423, baseEnd_5380423] using wordTrace_append hprefix tailTrace_5380423
  have hstable : (prefixWord ++ tailWord_5380423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380423).length < 2 ^ (prefixWord ++ tailWord_5380423).sum := by decide
  have hdescent : baseEnd_5380423 < baseStart_5380423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380514 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_5380514 : Nat := 118140960795 + 5380514 * 2 ^ 59
def prefixEnd_5380514 : Nat := 4983230072969 + 3 ^ 40 * 5380514 * 2
def baseEnd_5380514 : Nat := 2762789850245466947930473

theorem tailTrace_5380514 : CollatzResearch.WordTrace tailWord_5380514 prefixEnd_5380514 2762789850245466947930473 := by
  unfold tailWord_5380514
  simp only [CollatzResearch.WordTrace]
  refine ⟨49060866907331042869365149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130828978419549447651640397 49060866907331042869365149)
  ·
    refine ⟨18397825090249141076011931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49060866907331042869365149 18397825090249141076011931)
    ·
      refine ⟨27596737635373711614017897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18397825090249141076011931 27596737635373711614017897)
      ·
        refine ⟨20697553226530283710513423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27596737635373711614017897 20697553226530283710513423)
        ·
          refine ⟨31046329839795425565770135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20697553226530283710513423 31046329839795425565770135)
          ·
            refine ⟨46569494759693138348655203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31046329839795425565770135 46569494759693138348655203)
            ·
              refine ⟨69854242139539707522982805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46569494759693138348655203 69854242139539707522982805)
              ·
                refine ⟨3274417600290923790139819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69854242139539707522982805 3274417600290923790139819)
                ·
                  refine ⟨4911626400436385685209729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274417600290923790139819 4911626400436385685209729)
                  ·
                    refine ⟨3683719800327289263907297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4911626400436385685209729 3683719800327289263907297)
                    ·
                      refine ⟨2762789850245466947930473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683719800327289263907297 2762789850245466947930473)
                      ·
                        rfl

theorem cell23_5380514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_5380514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380514 prefixEnd_5380514 := by exact prefixLift 5380514
  have htrace : WordTrace (prefixWord ++ tailWord_5380514) baseStart_5380514 baseEnd_5380514 := by
    simpa [prefixWord, tailWord_5380514, baseEnd_5380514] using wordTrace_append hprefix tailTrace_5380514
  have hstable : (prefixWord ++ tailWord_5380514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380514).length < 2 ^ (prefixWord ++ tailWord_5380514).sum := by decide
  have hdescent : baseEnd_5380514 < baseStart_5380514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380516 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_5380516 : Nat := 118140960795 + 5380516 * 2 ^ 59
def prefixEnd_5380516 : Nat := 4983230072969 + 3 ^ 40 * 5380516 * 2
def baseEnd_5380516 : Nat := 920930292402258646701821

theorem tailTrace_5380516 : CollatzResearch.WordTrace tailWord_5380516 prefixEnd_5380516 920930292402258646701821 := by
  unfold tailWord_5380516
  simp only [CollatzResearch.WordTrace]
  refine ⟨98121770287658462909516701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130829027050211283879355601 98121770287658462909516701)
  ·
    refine ⟨36795663857871923591068763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98121770287658462909516701 36795663857871923591068763)
    ·
      refine ⟨55193495786807885386603145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36795663857871923591068763 55193495786807885386603145)
      ·
        refine ⟨41395121840105914039952359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55193495786807885386603145 41395121840105914039952359)
        ·
          refine ⟨62092682760158871059928539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41395121840105914039952359 62092682760158871059928539)
          ·
            refine ⟨93139024140238306589892809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62092682760158871059928539 93139024140238306589892809)
            ·
              refine ⟨69854268105178729942419607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93139024140238306589892809 69854268105178729942419607)
              ·
                refine ⟨104781402157768094913629411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69854268105178729942419607 104781402157768094913629411)
                ·
                  refine ⟨157172103236652142370444117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104781402157768094913629411 157172103236652142370444117)
                  ·
                    refine ⟨920930292402258646701821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157172103236652142370444117 920930292402258646701821)
                    ·
                      rfl

theorem cell23_5380516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_5380516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380516 prefixEnd_5380516 := by exact prefixLift 5380516
  have htrace : WordTrace (prefixWord ++ tailWord_5380516) baseStart_5380516 baseEnd_5380516 := by
    simpa [prefixWord, tailWord_5380516, baseEnd_5380516] using wordTrace_append hprefix tailTrace_5380516
  have hstable : (prefixWord ++ tailWord_5380516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380516).length < 2 ^ (prefixWord ++ tailWord_5380516).sum := by decide
  have hdescent : baseEnd_5380516 < baseStart_5380516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380548 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_5380548 : Nat := 118140960795 + 5380548 * 2 ^ 59
def prefixEnd_5380548 : Nat := 4983230072969 + 3 ^ 40 * 5380548 * 2
def baseEnd_5380548 : Nat := 2762807308587719814905317

theorem tailTrace_5380548 : CollatzResearch.WordTrace tailWord_5380548 prefixEnd_5380548 2762807308587719814905317 := by
  unfold tailWord_5380548
  simp only [CollatzResearch.WordTrace]
  refine ⟨98122353855600497642099149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130829805140800663522798865 98122353855600497642099149)
  ·
    refine ⟨36795882695850186615787181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98122353855600497642099149 36795882695850186615787181)
    ·
      refine ⟨13798456010943819980920193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36795882695850186615787181 13798456010943819980920193)
      ·
        refine ⟨10348842008207864985690145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13798456010943819980920193 10348842008207864985690145)
        ·
          refine ⟨7761631506155898739267609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10348842008207864985690145 7761631506155898739267609)
          ·
            refine ⟨5821223629616924054450707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7761631506155898739267609 5821223629616924054450707)
            ·
              refine ⟨8731835444425386081676061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821223629616924054450707 8731835444425386081676061)
              ·
                refine ⟨3274438291659519780628523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8731835444425386081676061 3274438291659519780628523)
                ·
                  refine ⟨4911657437489279670942785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274438291659519780628523 4911657437489279670942785)
                  ·
                    refine ⟨3683743078116959753207089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4911657437489279670942785 3683743078116959753207089)
                    ·
                      refine ⟨2762807308587719814905317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683743078116959753207089 2762807308587719814905317)
                      ·
                        rfl

theorem cell23_5380548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_5380548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380548 prefixEnd_5380548 := by exact prefixLift 5380548
  have htrace : WordTrace (prefixWord ++ tailWord_5380548) baseStart_5380548 baseEnd_5380548 := by
    simpa [prefixWord, tailWord_5380548, baseEnd_5380548] using wordTrace_append hprefix tailTrace_5380548
  have hstable : (prefixWord ++ tailWord_5380548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380548).length < 2 ^ (prefixWord ++ tailWord_5380548).sum := by decide
  have hdescent : baseEnd_5380548 < baseStart_5380548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380573 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_5380573 : Nat := 118140960795 + 5380573 * 2 ^ 59
def prefixEnd_5380573 : Nat := 4983230072969 + 3 ^ 40 * 5380573 * 2
def baseEnd_5380573 : Nat := 2762820145604082217092701

theorem tailTrace_5380573 : CollatzResearch.WordTrace tailWord_5380573 prefixEnd_5380573 2762820145604082217092701 := by
  unfold tailWord_5380573
  simp only [CollatzResearch.WordTrace]
  refine ⟨196245619536110424553858373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130830413024073616369238915 196245619536110424553858373)
  ·
    refine ⟨36796053663020704603848445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 196245619536110424553858373 36796053663020704603848445)
    ·
      refine ⟨13798520123632764226443167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36796053663020704603848445 13798520123632764226443167)
      ·
        refine ⟨20697780185449146339664751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13798520123632764226443167 20697780185449146339664751)
        ·
          refine ⟨31046670278173719509497127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20697780185449146339664751 31046670278173719509497127)
          ·
            refine ⟨46570005417260579264245691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31046670278173719509497127 46570005417260579264245691)
            ·
              refine ⟨69855008125890868896368537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46570005417260579264245691 69855008125890868896368537)
              ·
                refine ⟨52391256094418151672276403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69855008125890868896368537 52391256094418151672276403)
                ·
                  refine ⟨78586884141627227508414605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52391256094418151672276403 78586884141627227508414605)
                  ·
                    refine ⟨29470081553110210315655477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78586884141627227508414605 29470081553110210315655477)
                    ·
                      refine ⟨2762820145604082217092701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29470081553110210315655477 2762820145604082217092701)
                      ·
                        rfl

theorem cell23_5380573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_5380573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380573 prefixEnd_5380573 := by exact prefixLift 5380573
  have htrace : WordTrace (prefixWord ++ tailWord_5380573) baseStart_5380573 baseEnd_5380573 := by
    simpa [prefixWord, tailWord_5380573, baseEnd_5380573] using wordTrace_append hprefix tailTrace_5380573
  have hstable : (prefixWord ++ tailWord_5380573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380573).length < 2 ^ (prefixWord ++ tailWord_5380573).sum := by decide
  have hdescent : baseEnd_5380573 < baseStart_5380573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380581 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5380581 : Nat := 118140960795 + 5380581 * 2 ^ 59
def prefixEnd_5380581 : Nat := 4983230072969 + 3 ^ 40 * 5380581 * 2
def baseEnd_5380581 : Nat := 2762824253449318185792665

theorem tailTrace_5380581 : CollatzResearch.WordTrace tailWord_5380581 prefixEnd_5380581 2762824253449318185792665 := by
  unfold tailWord_5380581
  simp only [CollatzResearch.WordTrace]
  refine ⟨196245911320081441920149597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130830607546720961280099731 196245911320081441920149597)
  ·
    refine ⟨73592216745030540720056099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196245911320081441920149597 73592216745030540720056099)
    ·
      refine ⟨110388325117545811080084149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73592216745030540720056099 110388325117545811080084149)
      ·
        refine ⟨10348905479769919788757889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110388325117545811080084149 10348905479769919788757889)
        ·
          refine ⟨7761679109827439841568417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10348905479769919788757889 7761679109827439841568417)
          ·
            refine ⟨5821259332370579881176313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7761679109827439841568417 5821259332370579881176313)
            ·
              refine ⟨4365944499277934910882235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5821259332370579881176313 4365944499277934910882235)
              ·
                refine ⟨6548916748916902366323353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4365944499277934910882235 6548916748916902366323353)
                ·
                  refine ⟨4911687561687676774742515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6548916748916902366323353 4911687561687676774742515)
                  ·
                    refine ⟨7367531342531515162113773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4911687561687676774742515 7367531342531515162113773)
                    ·
                      refine ⟨2762824253449318185792665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367531342531515162113773 2762824253449318185792665)
                      ·
                        rfl

theorem cell23_5380581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5380581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380581 prefixEnd_5380581 := by exact prefixLift 5380581
  have htrace : WordTrace (prefixWord ++ tailWord_5380581) baseStart_5380581 baseEnd_5380581 := by
    simpa [prefixWord, tailWord_5380581, baseEnd_5380581] using wordTrace_append hprefix tailTrace_5380581
  have hstable : (prefixWord ++ tailWord_5380581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380581).length < 2 ^ (prefixWord ++ tailWord_5380581).sum := by decide
  have hdescent : baseEnd_5380581 < baseStart_5380581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380583 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5380583 : Nat := 118140960795 + 5380583 * 2 ^ 59
def prefixEnd_5380583 : Nat := 4983230072969 + 3 ^ 40 * 5380583 * 2
def baseEnd_5380583 : Nat := 2762825280410627177967655

theorem tailTrace_5380583 : CollatzResearch.WordTrace tailWord_5380583 prefixEnd_5380583 2762825280410627177967655 := by
  unfold tailWord_5380583
  simp only [CollatzResearch.WordTrace]
  refine ⟨196245984266074196261722403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130830656177382797507814935 196245984266074196261722403)
  ·
    refine ⟨294368976399111294392583605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196245984266074196261722403 294368976399111294392583605)
    ·
      refine ⟨27597091537416683849304713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 294368976399111294392583605 27597091537416683849304713)
      ·
        refine ⟨20697818653062512886978535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27597091537416683849304713 20697818653062512886978535)
        ·
          refine ⟨31046727979593769330467803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20697818653062512886978535 31046727979593769330467803)
          ·
            refine ⟨46570091969390653995701705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31046727979593769330467803 46570091969390653995701705)
            ·
              refine ⟨34927568977042990496776279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46570091969390653995701705 34927568977042990496776279)
              ·
                refine ⟨52391353465564485745164419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34927568977042990496776279 52391353465564485745164419)
                ·
                  refine ⟨78587030198346728617746629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52391353465564485745164419 78587030198346728617746629)
                  ·
                    refine ⟨14735068162190011615827493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78587030198346728617746629 14735068162190011615827493)
                    ·
                      refine ⟨2762825280410627177967655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14735068162190011615827493 2762825280410627177967655)
                      ·
                        rfl

theorem cell23_5380583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5380583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380583 prefixEnd_5380583 := by exact prefixLift 5380583
  have htrace : WordTrace (prefixWord ++ tailWord_5380583) baseStart_5380583 baseEnd_5380583 := by
    simpa [prefixWord, tailWord_5380583, baseEnd_5380583] using wordTrace_append hprefix tailTrace_5380583
  have hstable : (prefixWord ++ tailWord_5380583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380583).length < 2 ^ (prefixWord ++ tailWord_5380583).sum := by decide
  have hdescent : baseEnd_5380583 < baseStart_5380583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380587 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 2, 2, 2]
def baseStart_5380587 : Nat := 118140960795 + 5380587 * 2 ^ 59
def prefixEnd_5380587 : Nat := 4983230072969 + 3 ^ 40 * 5380587 * 2
def baseEnd_5380587 : Nat := 2762827334333245162317637

theorem tailTrace_5380587 : CollatzResearch.WordTrace tailWord_5380587 prefixEnd_5380587 2762827334333245162317637 := by
  unfold tailWord_5380587
  simp only [CollatzResearch.WordTrace]
  refine ⟨196246130158059704944868015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130830753438706469963245343 196246130158059704944868015)
  ·
    refine ⟨294369195237089557417302023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196246130158059704944868015 294369195237089557417302023)
    ·
      refine ⟨441553792855634336125953035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294369195237089557417302023 441553792855634336125953035)
      ·
        refine ⟨662330689283451504188929553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441553792855634336125953035 662330689283451504188929553)
        ·
          refine ⟨496748016962588628141697165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662330689283451504188929553 496748016962588628141697165)
          ·
            refine ⟨186280506360970735553136437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496748016962588628141697165 186280506360970735553136437)
            ·
              refine ⟨17463797471341006458106541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186280506360970735553136437 17463797471341006458106541)
              ·
                refine ⟨6548924051752877421789953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17463797471341006458106541 6548924051752877421789953)
                ·
                  refine ⟨4911693038814658066342465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6548924051752877421789953 4911693038814658066342465)
                  ·
                    refine ⟨3683769779110993549756849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4911693038814658066342465 3683769779110993549756849)
                    ·
                      refine ⟨2762827334333245162317637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3683769779110993549756849 2762827334333245162317637)
                      ·
                        rfl

theorem cell23_5380587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 2, 2].length) (baseStart_5380587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380587 prefixEnd_5380587 := by exact prefixLift 5380587
  have htrace : WordTrace (prefixWord ++ tailWord_5380587) baseStart_5380587 baseEnd_5380587 := by
    simpa [prefixWord, tailWord_5380587, baseEnd_5380587] using wordTrace_append hprefix tailTrace_5380587
  have hstable : (prefixWord ++ tailWord_5380587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380587).length < 2 ^ (prefixWord ++ tailWord_5380587).sum := by decide
  have hdescent : baseEnd_5380587 < baseStart_5380587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380680 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_5380680 : Nat := 118140960795 + 5380680 * 2 ^ 59
def prefixEnd_5380680 : Nat := 4983230072969 + 3 ^ 40 * 5380680 * 2
def baseEnd_5380680 : Nat := 2762875088034113298454709

theorem tailTrace_5380680 : CollatzResearch.WordTrace tailWord_5380680 prefixEnd_5380680 2762875088034113298454709 := by
  unfold tailWord_5380680
  simp only [CollatzResearch.WordTrace]
  refine ⟨98124761073361390914001747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130833014764481854552002329 98124761073361390914001747)
  ·
    refine ⟨147187141610042086371002621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98124761073361390914001747 147187141610042086371002621)
    ·
      refine ⟨55195178103765782389125983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147187141610042086371002621 55195178103765782389125983)
      ·
        refine ⟨82792767155648673583688975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55195178103765782389125983 82792767155648673583688975)
        ·
          refine ⟨124189150733473010375533463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82792767155648673583688975 124189150733473010375533463)
          ·
            refine ⟨186283726100209515563300195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124189150733473010375533463 186283726100209515563300195)
            ·
              refine ⟨279425589150314273344950293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186283726100209515563300195 279425589150314273344950293)
              ·
                refine ⟨13098074491420981563044545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279425589150314273344950293 13098074491420981563044545)
                ·
                  refine ⟨9823555868565736172283409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13098074491420981563044545 9823555868565736172283409)
                  ·
                    refine ⟨7367666901424302129212557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9823555868565736172283409 7367666901424302129212557)
                    ·
                      refine ⟨2762875088034113298454709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7367666901424302129212557 2762875088034113298454709)
                      ·
                        rfl

theorem cell23_5380680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_5380680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380680 prefixEnd_5380680 := by exact prefixLift 5380680
  have htrace : WordTrace (prefixWord ++ tailWord_5380680) baseStart_5380680 baseEnd_5380680 := by
    simpa [prefixWord, tailWord_5380680, baseEnd_5380680] using wordTrace_append hprefix tailTrace_5380680
  have hstable : (prefixWord ++ tailWord_5380680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380680).length < 2 ^ (prefixWord ++ tailWord_5380680).sum := by decide
  have hdescent : baseEnd_5380680 < baseStart_5380680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380687 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 1, 4]
def baseStart_5380687 : Nat := 118140960795 + 5380687 * 2 ^ 59
def prefixEnd_5380687 : Nat := 4983230072969 + 3 ^ 40 * 5380687 * 2
def baseEnd_5380687 : Nat := 920959560799564923689059

theorem tailTrace_5380687 : CollatzResearch.WordTrace tailWord_5380687 prefixEnd_5380687 920959560799564923689059 := by
  unfold tailWord_5380687
  simp only [CollatzResearch.WordTrace]
  refine ⟨196249777457697422023508315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130833184971798281349005543 196249777457697422023508315)
  ·
    refine ⟨294374666186546133035262473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196249777457697422023508315 294374666186546133035262473)
    ·
      refine ⟨220780999639909599776446855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294374666186546133035262473 220780999639909599776446855)
      ·
        refine ⟨331171499459864399664670283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220780999639909599776446855 331171499459864399664670283)
        ·
          refine ⟨496757249189796599497005425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331171499459864399664670283 496757249189796599497005425)
          ·
            refine ⟨372567936892347449622754069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496757249189796599497005425 372567936892347449622754069)
            ·
              refine ⟨17464122041828786701066597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 372567936892347449622754069 17464122041828786701066597)
              ·
                refine ⟨3274522882842897506449987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17464122041828786701066597 3274522882842897506449987)
                ·
                  refine ⟨4911784324264346259674981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3274522882842897506449987 4911784324264346259674981)
                  ·
                    refine ⟨920959560799564923689059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4911784324264346259674981 920959560799564923689059)
                    ·
                      rfl

theorem cell23_5380687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 1, 4].length) (baseStart_5380687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380687 prefixEnd_5380687 := by exact prefixLift 5380687
  have htrace : WordTrace (prefixWord ++ tailWord_5380687) baseStart_5380687 baseEnd_5380687 := by
    simpa [prefixWord, tailWord_5380687, baseEnd_5380687] using wordTrace_append hprefix tailTrace_5380687
  have hstable : (prefixWord ++ tailWord_5380687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380687).length < 2 ^ (prefixWord ++ tailWord_5380687).sum := by decide
  have hdescent : baseEnd_5380687 < baseStart_5380687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380753 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_5380753 : Nat := 118140960795 + 5380753 * 2 ^ 59
def prefixEnd_5380753 : Nat := 4983230072969 + 3 ^ 40 * 5380753 * 2
def baseEnd_5380753 : Nat := 2762912572121891512841873

theorem tailTrace_5380753 : CollatzResearch.WordTrace tailWord_5380753 prefixEnd_5380753 2762912572121891512841873 := by
  unfold tailWord_5380753
  simp only [CollatzResearch.WordTrace]
  refine ⟨196252184675458315295410913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130834789783638876863607275 196252184675458315295410913)
  ·
    refine ⟨147189138506593736471558185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196252184675458315295410913 147189138506593736471558185)
    ·
      refine ⟨110391853879945302353668639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147189138506593736471558185 110391853879945302353668639)
      ·
        refine ⟨165587780819917953530502959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110391853879945302353668639 165587780819917953530502959)
        ·
          refine ⟨248381671229876930295754439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165587780819917953530502959 248381671229876930295754439)
          ·
            refine ⟨372572506844815395443631659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248381671229876930295754439 372572506844815395443631659)
            ·
              refine ⟨558858760267223093165447489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372572506844815395443631659 558858760267223093165447489)
              ·
                refine ⟨419144070200417319874085617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558858760267223093165447489 419144070200417319874085617)
                ·
                  refine ⟨314358052650312989905564213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419144070200417319874085617 314358052650312989905564213)
                  ·
                    refine ⟨29471067435966842803646645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 314358052650312989905564213 29471067435966842803646645)
                    ·
                      refine ⟨2762912572121891512841873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29471067435966842803646645 2762912572121891512841873)
                      ·
                        rfl

theorem cell23_5380753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_5380753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380753 prefixEnd_5380753 := by exact prefixLift 5380753
  have htrace : WordTrace (prefixWord ++ tailWord_5380753) baseStart_5380753 baseEnd_5380753 := by
    simpa [prefixWord, tailWord_5380753, baseEnd_5380753] using wordTrace_append hprefix tailTrace_5380753
  have hstable : (prefixWord ++ tailWord_5380753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380753).length < 2 ^ (prefixWord ++ tailWord_5380753).sum := by decide
  have hdescent : baseEnd_5380753 < baseStart_5380753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5380760 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_5380760 : Nat := 118140960795 + 5380760 * 2 ^ 59
def prefixEnd_5380760 : Nat := 4983230072969 + 3 ^ 40 * 5380760 * 2
def baseEnd_5380760 : Nat := 920972055495490995151447

theorem tailTrace_5380760 : CollatzResearch.WordTrace tailWord_5380760 prefixEnd_5380760 920972055495490995151447 := by
  unfold tailWord_5380760
  simp only [CollatzResearch.WordTrace]
  refine ⟨98126219993216477745457867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130834959990955303660610489 98126219993216477745457867)
  ·
    refine ⟨147189329989824716618186801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98126219993216477745457867 147189329989824716618186801)
    ·
      refine ⟨110391997492368537463640101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147189329989824716618186801 110391997492368537463640101)
      ·
        refine ⟨20698499529819100774432519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110391997492368537463640101 20698499529819100774432519)
        ·
          refine ⟨31047749294728651161648779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20698499529819100774432519 31047749294728651161648779)
          ·
            refine ⟨46571623942092976742473169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31047749294728651161648779 46571623942092976742473169)
            ·
              refine ⟨34928717956569732556854877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46571623942092976742473169 34928717956569732556854877)
              ·
                refine ⟨13098269233713649708820579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34928717956569732556854877 13098269233713649708820579)
                ·
                  refine ⟨19647403850570474563230869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13098269233713649708820579 19647403850570474563230869)
                  ·
                    refine ⟨920972055495490995151447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19647403850570474563230869 920972055495490995151447)
                    ·
                      rfl

theorem cell23_5380760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_5380760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5380760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5380760 prefixEnd_5380760 := by exact prefixLift 5380760
  have htrace : WordTrace (prefixWord ++ tailWord_5380760) baseStart_5380760 baseEnd_5380760 := by
    simpa [prefixWord, tailWord_5380760, baseEnd_5380760] using wordTrace_append hprefix tailTrace_5380760
  have hstable : (prefixWord ++ tailWord_5380760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5380760).length < 2 ^ (prefixWord ++ tailWord_5380760).sum := by decide
  have hdescent : baseEnd_5380760 < baseStart_5380760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5380760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
