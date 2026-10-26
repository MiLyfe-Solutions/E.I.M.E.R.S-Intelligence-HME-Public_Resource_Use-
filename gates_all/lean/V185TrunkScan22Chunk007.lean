import V185TrunkScan22Chunk006

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_62383 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 6, 4]
def baseStart_62383 : Nat := 118140960795 + 62383 * 2 ^ 59
def prefixEnd_62383 : Nat := 4983230072969 + 3 ^ 40 * 62383 * 2
def baseEnd_62383 : Nat := 21354975779689773283741

theorem tailTrace_62383 : CollatzResearch.WordTrace tailWord_62383 prefixEnd_62383 21354975779689773283741 := by
  unfold tailWord_62383
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275294933004520013287803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1516863288669680008858535 2275294933004520013287803)
  ·
    refine ⟨3412942399506780019931705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2275294933004520013287803 3412942399506780019931705)
    ·
      refine ⟨2559706799630085014948779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3412942399506780019931705 2559706799630085014948779)
      ·
        refine ⟨3839560199445127522423169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559706799630085014948779 3839560199445127522423169)
        ·
          refine ⟨2879670149583845641817377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839560199445127522423169 2879670149583845641817377)
          ·
            refine ⟨2159752612187884231363033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2879670149583845641817377 2159752612187884231363033)
            ·
              refine ⟨1619814459140913173522275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2159752612187884231363033 1619814459140913173522275)
              ·
                refine ⟨2429721688711369760283413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619814459140913173522275 2429721688711369760283413)
                ·
                  refine ⟨113893204158345457513285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2429721688711369760283413 113893204158345457513285)
                  ·
                    refine ⟨21354975779689773283741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113893204158345457513285 21354975779689773283741)
                    ·
                      rfl

theorem cell22_62383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_62383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62383 prefixEnd_62383 := by exact prefixLift 62383
  have htrace : WordTrace (prefixWord ++ tailWord_62383) baseStart_62383 baseEnd_62383 := by
    simpa [prefixWord, tailWord_62383, baseEnd_62383] using wordTrace_append hprefix tailTrace_62383
  have hstable : (prefixWord ++ tailWord_62383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62383).length < 2 ^ (prefixWord ++ tailWord_62383).sum := by decide
  have hdescent : baseEnd_62383 < baseStart_62383 := by decide
  rcases family_descends (prefixWord ++ tailWord_62383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62490 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_62490 : Nat := 118140960795 + 62490 * 2 ^ 59
def prefixEnd_62490 : Nat := 4983230072969 + 3 ^ 40 * 62490 * 2
def baseEnd_62490 : Nat := 21391604066377160858413

theorem tailTrace_62490 : CollatzResearch.WordTrace tailWord_62490 prefixEnd_62490 21391604066377160858413 := by
  unfold tailWord_62490
  simp only [CollatzResearch.WordTrace]
  refine ⟨569799385904219321858231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1519465029077918191621949 569799385904219321858231)
  ·
    refine ⟨854699078856328982787347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569799385904219321858231 854699078856328982787347)
    ·
      refine ⟨1282048618284493474181021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854699078856328982787347 1282048618284493474181021)
      ·
        refine ⟨480768231856685052817883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1282048618284493474181021 480768231856685052817883)
        ·
          refine ⟨721152347785027579226825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480768231856685052817883 721152347785027579226825)
          ·
            refine ⟨540864260838770684420119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721152347785027579226825 540864260838770684420119)
            ·
              refine ⟨811296391258156026630179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540864260838770684420119 811296391258156026630179)
              ·
                refine ⟨1216944586887234039945269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811296391258156026630179 1216944586887234039945269)
                ·
                  refine ⟨114088555020678191244869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1216944586887234039945269 114088555020678191244869)
                  ·
                    refine ⟨21391604066377160858413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114088555020678191244869 21391604066377160858413)
                    ·
                      rfl

theorem cell22_62490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_62490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62490 prefixEnd_62490 := by exact prefixLift 62490
  have htrace : WordTrace (prefixWord ++ tailWord_62490) baseStart_62490 baseEnd_62490 := by
    simpa [prefixWord, tailWord_62490, baseEnd_62490] using wordTrace_append hprefix tailTrace_62490
  have hstable : (prefixWord ++ tailWord_62490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62490).length < 2 ^ (prefixWord ++ tailWord_62490).sum := by decide
  have hdescent : baseEnd_62490 < baseStart_62490 := by decide
  rcases family_descends (prefixWord ++ tailWord_62490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62492 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_62492 : Nat := 118140960795 + 62492 * 2 ^ 59
def prefixEnd_62492 : Nat := 4983230072969 + 3 ^ 40 * 62492 * 2
def baseEnd_62492 : Nat := 21392288707249822308407

theorem tailTrace_62492 : CollatzResearch.WordTrace tailWord_62492 prefixEnd_62492 21392288707249822308407 := by
  unfold tailWord_62492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139635244804815814502865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1519513659739754419337153 1139635244804815814502865)
  ·
    refine ⟨854726433603611860877149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1139635244804815814502865 854726433603611860877149)
    ·
      refine ⟨320522412601354447828931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 854726433603611860877149 320522412601354447828931)
      ·
        refine ⟨480783618902031671743397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320522412601354447828931 480783618902031671743397)
        ·
          refine ⟨90146928544130938451887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480783618902031671743397 90146928544130938451887)
          ·
            refine ⟨135220392816196407677831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90146928544130938451887 135220392816196407677831)
            ·
              refine ⟨202830589224294611516747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135220392816196407677831 202830589224294611516747)
              ·
                refine ⟨304245883836441917275121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202830589224294611516747 304245883836441917275121)
                ·
                  refine ⟨228184412877331437956341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304245883836441917275121 228184412877331437956341)
                  ·
                    refine ⟨21392288707249822308407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 228184412877331437956341 21392288707249822308407)
                    ·
                      rfl

theorem cell22_62492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_62492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62492 prefixEnd_62492 := by exact prefixLift 62492
  have htrace : WordTrace (prefixWord ++ tailWord_62492) baseStart_62492 baseEnd_62492 := by
    simpa [prefixWord, tailWord_62492, baseEnd_62492] using wordTrace_append hprefix tailTrace_62492
  have hstable : (prefixWord ++ tailWord_62492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62492).length < 2 ^ (prefixWord ++ tailWord_62492).sum := by decide
  have hdescent : baseEnd_62492 < baseStart_62492 := by decide
  rcases family_descends (prefixWord ++ tailWord_62492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62522 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_62522 : Nat := 118140960795 + 62522 * 2 ^ 59
def prefixEnd_62522 : Nat := 4983230072969 + 3 ^ 40 * 62522 * 2
def baseEnd_62522 : Nat := 7134186106779914686105

theorem tailTrace_62522 : CollatzResearch.WordTrace tailWord_62522 prefixEnd_62522 7134186106779914686105 := by
  unfold tailWord_62522
  simp only [CollatzResearch.WordTrace]
  refine ⟨570091169875236688149455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1520243119667297835065213 570091169875236688149455)
  ·
    refine ⟨855136754812855032224183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 570091169875236688149455 855136754812855032224183)
    ·
      refine ⟨1282705132219282548336275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855136754812855032224183 1282705132219282548336275)
      ·
        refine ⟨1924057698328923822504413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282705132219282548336275 1924057698328923822504413)
        ·
          refine ⟨721521636873346433439155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1924057698328923822504413 721521636873346433439155)
          ·
            refine ⟨1082282455310019650158733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721521636873346433439155 1082282455310019650158733)
            ·
              refine ⟨405855920741257368809525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1082282455310019650158733 405855920741257368809525)
              ·
                refine ⟨38048992569492878325893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405855920741257368809525 38048992569492878325893)
                ·
                  refine ⟨7134186106779914686105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38048992569492878325893 7134186106779914686105)
                  ·
                    rfl

theorem cell22_62522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_62522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62522 prefixEnd_62522 := by exact prefixLift 62522
  have htrace : WordTrace (prefixWord ++ tailWord_62522) baseStart_62522 baseEnd_62522 := by
    simpa [prefixWord, tailWord_62522, baseEnd_62522] using wordTrace_append hprefix tailTrace_62522
  have hstable : (prefixWord ++ tailWord_62522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62522).length < 2 ^ (prefixWord ++ tailWord_62522).sum := by decide
  have hdescent : baseEnd_62522 < baseStart_62522 := by decide
  rcases family_descends (prefixWord ++ tailWord_62522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62524 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_62524 : Nat := 118140960795 + 62524 * 2 ^ 59
def prefixEnd_62524 : Nat := 4983230072969 + 3 ^ 40 * 62524 * 2
def baseEnd_62524 : Nat := 21403242961212405508309

theorem tailTrace_62524 : CollatzResearch.WordTrace tailWord_62524 prefixEnd_62524 21403242961212405508309 := by
  unfold tailWord_62524
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140218812746850547085313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1520291750329134062780417 1140218812746850547085313)
  ·
    refine ⟨855164109560137910313985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1140218812746850547085313 855164109560137910313985)
    ·
      refine ⟨641373082170103432735489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 855164109560137910313985 641373082170103432735489)
      ·
        refine ⟨481029811627577574551617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641373082170103432735489 481029811627577574551617)
        ·
          refine ⟨360772358720683180913713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481029811627577574551617 360772358720683180913713)
          ·
            refine ⟨270579269040512385685285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360772358720683180913713 270579269040512385685285)
            ·
              refine ⟨50733612945096072315991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270579269040512385685285 50733612945096072315991)
              ·
                refine ⟨76100419417644108473987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50733612945096072315991 76100419417644108473987)
                ·
                  refine ⟨114150629126466162710981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76100419417644108473987 114150629126466162710981)
                  ·
                    refine ⟨21403242961212405508309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114150629126466162710981 21403242961212405508309)
                    ·
                      rfl

theorem cell22_62524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_62524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62524 prefixEnd_62524 := by exact prefixLift 62524
  have htrace : WordTrace (prefixWord ++ tailWord_62524) baseStart_62524 baseEnd_62524 := by
    simpa [prefixWord, tailWord_62524, baseEnd_62524] using wordTrace_append hprefix tailTrace_62524
  have hstable : (prefixWord ++ tailWord_62524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62524).length < 2 ^ (prefixWord ++ tailWord_62524).sum := by decide
  have hdescent : baseEnd_62524 < baseStart_62524 := by decide
  rcases family_descends (prefixWord ++ tailWord_62524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62537 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 2, 3]
def baseStart_62537 : Nat := 118140960795 + 62537 * 2 ^ 59
def prefixEnd_62537 : Nat := 4983230072969 + 3 ^ 40 * 62537 * 2
def baseEnd_62537 : Nat := 21407693126884704933269

theorem tailTrace_62537 : CollatzResearch.WordTrace tailWord_62537 prefixEnd_62537 21407693126884704933269 := by
  unfold tailWord_62537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280911774446604314393865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1520607849631069542929243 2280911774446604314393865)
  ·
    refine ⟨1710683830834953235795399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2280911774446604314393865 1710683830834953235795399)
    ·
      refine ⟨2566025746252429853693099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710683830834953235795399 2566025746252429853693099)
      ·
        refine ⟨3849038619378644780539649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566025746252429853693099 3849038619378644780539649)
        ·
          refine ⟨2886778964533983585404737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849038619378644780539649 2886778964533983585404737)
          ·
            refine ⟨2165084223400487689053553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886778964533983585404737 2165084223400487689053553)
            ·
              refine ⟨1623813167550365766790165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2165084223400487689053553 1623813167550365766790165)
              ·
                refine ⟨76116242228923395318289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1623813167550365766790165 76116242228923395318289)
                ·
                  refine ⟨57087181671692546488717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76116242228923395318289 57087181671692546488717)
                  ·
                    refine ⟨21407693126884704933269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57087181671692546488717 21407693126884704933269)
                    ·
                      rfl

theorem cell22_62537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_62537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62537 prefixEnd_62537 := by exact prefixLift 62537
  have htrace : WordTrace (prefixWord ++ tailWord_62537) baseStart_62537 baseEnd_62537 := by
    simpa [prefixWord, tailWord_62537, baseEnd_62537] using wordTrace_append hprefix tailTrace_62537
  have hstable : (prefixWord ++ tailWord_62537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62537).length < 2 ^ (prefixWord ++ tailWord_62537).sum := by decide
  have hdescent : baseEnd_62537 < baseStart_62537 := by decide
  rcases family_descends (prefixWord ++ tailWord_62537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62558 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_62558 : Nat := 118140960795 + 62558 * 2 ^ 59
def prefixEnd_62558 : Nat := 4983230072969 + 3 ^ 40 * 62558 * 2
def baseEnd_62558 : Nat := 21414881856047650158205

theorem tailTrace_62558 : CollatzResearch.WordTrace tailWord_62558 prefixEnd_62558 21414881856047650158205 := by
  unfold tailWord_62558
  simp only [CollatzResearch.WordTrace]
  refine ⟨285209713421315612613541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1521118471580349933938885 285209713421315612613541)
  ·
    refine ⟨53476821266496677365039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285209713421315612613541 53476821266496677365039)
    ·
      refine ⟨80215231899745016047559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53476821266496677365039 80215231899745016047559)
      ·
        refine ⟨120322847849617524071339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80215231899745016047559 120322847849617524071339)
        ·
          refine ⟨180484271774426286107009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120322847849617524071339 180484271774426286107009)
          ·
            refine ⟨135363203830819714580257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180484271774426286107009 135363203830819714580257)
            ·
              refine ⟨101522402873114785935193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135363203830819714580257 101522402873114785935193)
              ·
                refine ⟨76141802154836089451395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101522402873114785935193 76141802154836089451395)
                ·
                  refine ⟨114212703232254134177093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76141802154836089451395 114212703232254134177093)
                  ·
                    refine ⟨21414881856047650158205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114212703232254134177093 21414881856047650158205)
                    ·
                      rfl

theorem cell22_62558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_62558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62558 prefixEnd_62558 := by exact prefixLift 62558
  have htrace : WordTrace (prefixWord ++ tailWord_62558) baseStart_62558 baseEnd_62558 := by
    simpa [prefixWord, tailWord_62558, baseEnd_62558] using wordTrace_append hprefix tailTrace_62558
  have hstable : (prefixWord ++ tailWord_62558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62558).length < 2 ^ (prefixWord ++ tailWord_62558).sum := by decide
  have hdescent : baseEnd_62558 < baseStart_62558 := by decide
  rcases family_descends (prefixWord ++ tailWord_62558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62565 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_62565 : Nat := 118140960795 + 62565 * 2 ^ 59
def prefixEnd_62565 : Nat := 4983230072969 + 3 ^ 40 * 62565 * 2
def baseEnd_62565 : Nat := 21417278099101965233183

theorem tailTrace_62565 : CollatzResearch.WordTrace tailWord_62565 prefixEnd_62565 21417278099101965233183 := by
  unfold tailWord_62565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281933018345165096413149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1521288678896776730942099 2281933018345165096413149)
  ·
    refine ⟨855724881879436911154931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2281933018345165096413149 855724881879436911154931)
    ·
      refine ⟨1283587322819155366732397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855724881879436911154931 1283587322819155366732397)
      ·
        refine ⟨481345246057183262524649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1283587322819155366732397 481345246057183262524649)
        ·
          refine ⟨361008934542887446893487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481345246057183262524649 361008934542887446893487)
          ·
            refine ⟨541513401814331170340231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361008934542887446893487 541513401814331170340231)
            ·
              refine ⟨812270102721496755510347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541513401814331170340231 812270102721496755510347)
              ·
                refine ⟨1218405154082245133265521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812270102721496755510347 1218405154082245133265521)
                ·
                  refine ⟨913803865561683849949141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218405154082245133265521 913803865561683849949141)
                  ·
                    refine ⟨21417278099101965233183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 913803865561683849949141 21417278099101965233183)
                    ·
                      rfl

theorem cell22_62565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_62565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62565 prefixEnd_62565 := by exact prefixLift 62565
  have htrace : WordTrace (prefixWord ++ tailWord_62565) baseStart_62565 baseEnd_62565 := by
    simpa [prefixWord, tailWord_62565, baseEnd_62565] using wordTrace_append hprefix tailTrace_62565
  have hstable : (prefixWord ++ tailWord_62565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62565).length < 2 ^ (prefixWord ++ tailWord_62565).sum := by decide
  have hdescent : baseEnd_62565 < baseStart_62565 := by decide
  rcases family_descends (prefixWord ++ tailWord_62565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62567 : List Nat := [1, 1, 5, 1, 1, 3, 4, 6]
def baseStart_62567 : Nat := 118140960795 + 62567 * 2 ^ 59
def prefixEnd_62567 : Nat := 4983230072969 + 3 ^ 40 * 62567 * 2
def baseEnd_62567 : Nat := 2379773637774958520353

theorem tailTrace_62567 : CollatzResearch.WordTrace tailWord_62567 prefixEnd_62567 2379773637774958520353 := by
  unfold tailWord_62567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282005964337919437985955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1521337309558612958657303 2282005964337919437985955)
  ·
    refine ⟨3423008946506879156978933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2282005964337919437985955 3423008946506879156978933)
    ·
      refine ⟨320907088735019920966775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3423008946506879156978933 320907088735019920966775)
      ·
        refine ⟨481360633102529881450163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320907088735019920966775 481360633102529881450163)
        ·
          refine ⟨722040949653794822175245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481360633102529881450163 722040949653794822175245)
          ·
            refine ⟨270765356120173058315717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722040949653794822175245 270765356120173058315717)
            ·
              refine ⟨50768504272532448434197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270765356120173058315717 50768504272532448434197)
              ·
                refine ⟨2379773637774958520353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50768504272532448434197 2379773637774958520353)
                ·
                  rfl

theorem cell22_62567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 6].length) (baseStart_62567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62567 prefixEnd_62567 := by exact prefixLift 62567
  have htrace : WordTrace (prefixWord ++ tailWord_62567) baseStart_62567 baseEnd_62567 := by
    simpa [prefixWord, tailWord_62567, baseEnd_62567] using wordTrace_append hprefix tailTrace_62567
  have hstable : (prefixWord ++ tailWord_62567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62567).length < 2 ^ (prefixWord ++ tailWord_62567).sum := by decide
  have hdescent : baseEnd_62567 < baseStart_62567 := by decide
  rcases family_descends (prefixWord ++ tailWord_62567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62590 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_62590 : Nat := 118140960795 + 62590 * 2 ^ 59
def prefixEnd_62590 : Nat := 4983230072969 + 3 ^ 40 * 62590 * 2
def baseEnd_62590 : Nat := 7141945370003411119369

theorem tailTrace_62590 : CollatzResearch.WordTrace tailWord_62590 prefixEnd_62590 7141945370003411119369 := by
  unfold tailWord_62590
  simp only [CollatzResearch.WordTrace]
  refine ⟨285355605406824295759153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1521896562169729577382149 285355605406824295759153)
  ·
    refine ⟨214016704055118221819365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285355605406824295759153 214016704055118221819365)
    ·
      refine ⟨40128132010334666591131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214016704055118221819365 40128132010334666591131)
      ·
        refine ⟨60192198015501999886697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40128132010334666591131 60192198015501999886697)
        ·
          refine ⟨45144148511626499915023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60192198015501999886697 45144148511626499915023)
          ·
            refine ⟨67716222767439749872535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45144148511626499915023 67716222767439749872535)
            ·
              refine ⟨101574334151159624808803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67716222767439749872535 101574334151159624808803)
              ·
                refine ⟨152361501226739437213205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101574334151159624808803 152361501226739437213205)
                ·
                  refine ⟨7141945370003411119369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152361501226739437213205 7141945370003411119369)
                  ·
                    rfl

theorem cell22_62590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_62590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62590 prefixEnd_62590 := by exact prefixLift 62590
  have htrace : WordTrace (prefixWord ++ tailWord_62590) baseStart_62590 baseEnd_62590 := by
    simpa [prefixWord, tailWord_62590, baseEnd_62590] using wordTrace_append hprefix tailTrace_62590
  have hstable : (prefixWord ++ tailWord_62590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62590).length < 2 ^ (prefixWord ++ tailWord_62590).sum := by decide
  have hdescent : baseEnd_62590 < baseStart_62590 := by decide
  rcases family_descends (prefixWord ++ tailWord_62590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62595 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 7]
def baseStart_62595 : Nat := 118140960795 + 62595 * 2 ^ 59
def prefixEnd_62595 : Nat := 4983230072969 + 3 ^ 40 * 62595 * 2
def baseEnd_62595 : Nat := 7142515904063962327697

theorem tailTrace_62595 : CollatzResearch.WordTrace tailWord_62595 prefixEnd_62595 7142515904063962327697 := by
  unfold tailWord_62595
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283027208236480220005239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1522018138824320146670159 2283027208236480220005239)
  ·
    refine ⟨3424540812354720330007859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283027208236480220005239 3424540812354720330007859)
    ·
      refine ⟨5136811218532080495011789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3424540812354720330007859 5136811218532080495011789)
      ·
        refine ⟨1926304206949530185629421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5136811218532080495011789 1926304206949530185629421)
        ·
          refine ⟨722364077606073819611033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1926304206949530185629421 722364077606073819611033)
          ·
            refine ⟨541773058204555364708275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722364077606073819611033 541773058204555364708275)
            ·
              refine ⟨812659587306833047062413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541773058204555364708275 812659587306833047062413)
              ·
                refine ⟨304747345240062392648405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812659587306833047062413 304747345240062392648405)
                ·
                  refine ⟨7142515904063962327697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304747345240062392648405 7142515904063962327697)
                  ·
                    rfl

theorem cell22_62595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_62595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62595 prefixEnd_62595 := by exact prefixLift 62595
  have htrace : WordTrace (prefixWord ++ tailWord_62595) baseStart_62595 baseEnd_62595 := by
    simpa [prefixWord, tailWord_62595, baseEnd_62595] using wordTrace_append hprefix tailTrace_62595
  have hstable : (prefixWord ++ tailWord_62595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62595).length < 2 ^ (prefixWord ++ tailWord_62595).sum := by decide
  have hdescent : baseEnd_62595 < baseStart_62595 := by decide
  rcases family_descends (prefixWord ++ tailWord_62595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62640 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_62640 : Nat := 118140960795 + 62640 * 2 ^ 59
def prefixEnd_62640 : Nat := 4983230072969 + 3 ^ 40 * 62640 * 2
def baseEnd_62640 : Nat := 7147650710608923202651

theorem tailTrace_62640 : CollatzResearch.WordTrace tailWord_62640 prefixEnd_62640 7147650710608923202651 := by
  unfold tailWord_62640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142334246536726452696687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1523112328715635270262249 1142334246536726452696687)
  ·
    refine ⟨1713501369805089679045031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142334246536726452696687 1713501369805089679045031)
    ·
      refine ⟨2570252054707634518567547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713501369805089679045031 2570252054707634518567547)
      ·
        refine ⟨3855378082061451777851321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570252054707634518567547 3855378082061451777851321)
        ·
          refine ⟨2891533561546088833388491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3855378082061451777851321 2891533561546088833388491)
          ·
            refine ⟨4337300342319133250082737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891533561546088833388491 4337300342319133250082737)
            ·
              refine ⟨3252975256739349937562053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4337300342319133250082737 3252975256739349937562053)
              ·
                refine ⟨609932860638628113292885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3252975256739349937562053 609932860638628113292885)
                ·
                  refine ⟨7147650710608923202651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 609932860638628113292885 7147650710608923202651)
                  ·
                    rfl

theorem cell22_62640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_62640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62640 prefixEnd_62640 := by exact prefixLift 62640
  have htrace : WordTrace (prefixWord ++ tailWord_62640) baseStart_62640 baseEnd_62640 := by
    simpa [prefixWord, tailWord_62640, baseEnd_62640] using wordTrace_append hprefix tailTrace_62640
  have hstable : (prefixWord ++ tailWord_62640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62640).length < 2 ^ (prefixWord ++ tailWord_62640).sum := by decide
  have hdescent : baseEnd_62640 < baseStart_62640 := by decide
  rcases family_descends (prefixWord ++ tailWord_62640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62693 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_62693 : Nat := 118140960795 + 62693 * 2 ^ 59
def prefixEnd_62693 : Nat := 4983230072969 + 3 ^ 40 * 62693 * 2
def baseEnd_62693 : Nat := 21461095114952298032791

theorem tailTrace_62693 : CollatzResearch.WordTrace tailWord_62693 prefixEnd_62693 21461095114952298032791 := by
  unfold tailWord_62693
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286601561881442957072733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1524401041254295304715155 2286601561881442957072733)
  ·
    refine ⟨857475585705541108902275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2286601561881442957072733 857475585705541108902275)
    ·
      refine ⟨1286213378558311663353413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857475585705541108902275 1286213378558311663353413)
      ·
        refine ⟨241165008479683436878765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1286213378558311663353413 241165008479683436878765)
        ·
          refine ⟨90436878179881288829537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241165008479683436878765 90436878179881288829537)
          ·
            refine ⟨67827658634910966622153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90436878179881288829537 67827658634910966622153)
            ·
              refine ⟨50870743976183224966615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67827658634910966622153 50870743976183224966615)
              ·
                refine ⟨76306115964274837449923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50870743976183224966615 76306115964274837449923)
                ·
                  refine ⟨114459173946412256174885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76306115964274837449923 114459173946412256174885)
                  ·
                    refine ⟨21461095114952298032791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114459173946412256174885 21461095114952298032791)
                    ·
                      rfl

theorem cell22_62693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_62693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62693 prefixEnd_62693 := by exact prefixLift 62693
  have htrace : WordTrace (prefixWord ++ tailWord_62693) baseStart_62693 baseEnd_62693 := by
    simpa [prefixWord, tailWord_62693, baseEnd_62693] using wordTrace_append hprefix tailTrace_62693
  have hstable : (prefixWord ++ tailWord_62693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62693).length < 2 ^ (prefixWord ++ tailWord_62693).sum := by decide
  have hdescent : baseEnd_62693 < baseStart_62693 := by decide
  rcases family_descends (prefixWord ++ tailWord_62693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62706 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_62706 : Nat := 118140960795 + 62706 * 2 ^ 59
def prefixEnd_62706 : Nat := 4983230072969 + 3 ^ 40 * 62706 * 2
def baseEnd_62706 : Nat := 21465545280624597457751

theorem tailTrace_62706 : CollatzResearch.WordTrace tailWord_62706 prefixEnd_62706 21465545280624597457751 := by
  unfold tailWord_62706
  simp only [CollatzResearch.WordTrace]
  refine ⟨571768927708586544323993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1524717140556230784863981 571768927708586544323993)
  ·
    refine ⟨428826695781439908242995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 571768927708586544323993 428826695781439908242995)
    ·
      refine ⟨643240043672159862364493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428826695781439908242995 643240043672159862364493)
      ·
        refine ⟨241215016377059948386685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 643240043672159862364493 241215016377059948386685)
        ·
          refine ⟨90455631141397480645007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241215016377059948386685 90455631141397480645007)
          ·
            refine ⟨135683446712096220967511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90455631141397480645007 135683446712096220967511)
            ·
              refine ⟨203525170068144331451267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135683446712096220967511 203525170068144331451267)
              ·
                refine ⟨305287755102216497176901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203525170068144331451267 305287755102216497176901)
                ·
                  refine ⟨57241454081665593220669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305287755102216497176901 57241454081665593220669)
                  ·
                    refine ⟨21465545280624597457751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57241454081665593220669 21465545280624597457751)
                    ·
                      rfl

theorem cell22_62706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_62706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62706 prefixEnd_62706 := by exact prefixLift 62706
  have htrace : WordTrace (prefixWord ++ tailWord_62706) baseStart_62706 baseEnd_62706 := by
    simpa [prefixWord, tailWord_62706, baseEnd_62706] using wordTrace_append hprefix tailTrace_62706
  have hstable : (prefixWord ++ tailWord_62706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62706).length < 2 ^ (prefixWord ++ tailWord_62706).sum := by decide
  have hdescent : baseEnd_62706 < baseStart_62706 := by decide
  rcases family_descends (prefixWord ++ tailWord_62706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62768 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 1, 3]
def baseStart_62768 : Nat := 118140960795 + 62768 * 2 ^ 59
def prefixEnd_62768 : Nat := 4983230072969 + 3 ^ 40 * 62768 * 2
def baseEnd_62768 : Nat := 21486769147677102407561

theorem tailTrace_62768 : CollatzResearch.WordTrace tailWord_62768 prefixEnd_62768 21486769147677102407561 := by
  unfold tailWord_62768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1144668518304865383026479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1526224691073153844035305 1144668518304865383026479)
  ·
    refine ⟨1717002777457298074539719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1144668518304865383026479 1717002777457298074539719)
    ·
      refine ⟨2575504166185947111809579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717002777457298074539719 2575504166185947111809579)
      ·
        refine ⟨3863256249278920667714369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575504166185947111809579 3863256249278920667714369)
        ·
          refine ⟨2897442186959190500785777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3863256249278920667714369 2897442186959190500785777)
          ·
            refine ⟨2173081640219392875589333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897442186959190500785777 2173081640219392875589333)
            ·
              refine ⟨50931600942642020521625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2173081640219392875589333 50931600942642020521625)
              ·
                refine ⟨38198700706981515391219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50931600942642020521625 38198700706981515391219)
                ·
                  refine ⟨57298051060472273086829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38198700706981515391219 57298051060472273086829)
                  ·
                    refine ⟨21486769147677102407561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57298051060472273086829 21486769147677102407561)
                    ·
                      rfl

theorem cell22_62768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_62768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62768 prefixEnd_62768 := by exact prefixLift 62768
  have htrace : WordTrace (prefixWord ++ tailWord_62768) baseStart_62768 baseEnd_62768 := by
    simpa [prefixWord, tailWord_62768, baseEnd_62768] using wordTrace_append hprefix tailTrace_62768
  have hstable : (prefixWord ++ tailWord_62768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62768).length < 2 ^ (prefixWord ++ tailWord_62768).sum := by decide
  have hdescent : baseEnd_62768 < baseStart_62768 := by decide
  rcases family_descends (prefixWord ++ tailWord_62768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62774 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_62774 : Nat := 118140960795 + 62774 * 2 ^ 59
def prefixEnd_62774 : Nat := 4983230072969 + 3 ^ 40 * 62774 * 2
def baseEnd_62774 : Nat := 21488823070295086757543

theorem tailTrace_62774 : CollatzResearch.WordTrace tailWord_62774 prefixEnd_62774 21488823070295086757543 := by
  unfold tailWord_62774
  simp only [CollatzResearch.WordTrace]
  refine ⟨143097242161749611923211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1526370583058662527180917 143097242161749611923211)
  ·
    refine ⟨214645863242624417884817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143097242161749611923211 214645863242624417884817)
    ·
      refine ⟨160984397431968313413613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214645863242624417884817 160984397431968313413613)
      ·
        refine ⟨60369149036988117530105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160984397431968313413613 60369149036988117530105)
        ·
          refine ⟨45276861777741088147579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60369149036988117530105 45276861777741088147579)
          ·
            refine ⟨67915292666611632221369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45276861777741088147579 67915292666611632221369)
            ·
              refine ⟨50936469499958724166027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67915292666611632221369 50936469499958724166027)
              ·
                refine ⟨76404704249938086249041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50936469499958724166027 76404704249938086249041)
                ·
                  refine ⟨57303528187453564686781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76404704249938086249041 57303528187453564686781)
                  ·
                    refine ⟨21488823070295086757543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57303528187453564686781 21488823070295086757543)
                    ·
                      rfl

theorem cell22_62774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_62774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62774 prefixEnd_62774 := by exact prefixLift 62774
  have htrace : WordTrace (prefixWord ++ tailWord_62774) baseStart_62774 baseEnd_62774 := by
    simpa [prefixWord, tailWord_62774, baseEnd_62774] using wordTrace_append hprefix tailTrace_62774
  have hstable : (prefixWord ++ tailWord_62774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62774).length < 2 ^ (prefixWord ++ tailWord_62774).sum := by decide
  have hdescent : baseEnd_62774 < baseStart_62774 := by decide
  rcases family_descends (prefixWord ++ tailWord_62774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62792 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_62792 : Nat := 118140960795 + 62792 * 2 ^ 59
def prefixEnd_62792 : Nat := 4983230072969 + 3 ^ 40 * 62792 * 2
def baseEnd_62792 : Nat := 7164994946049679935829

theorem tailTrace_62792 : CollatzResearch.WordTrace tailWord_62792 prefixEnd_62792 7164994946049679935829 := by
  unfold tailWord_62792
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145106194261391432463315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1526808259015188576617753 1145106194261391432463315)
  ·
    refine ⟨1717659291392087148694973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145106194261391432463315 1717659291392087148694973)
    ·
      refine ⟨644122234272032680760615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1717659291392087148694973 644122234272032680760615)
      ·
        refine ⟨966183351408049021140923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644122234272032680760615 966183351408049021140923)
        ·
          refine ⟨1449275027112073531711385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966183351408049021140923 1449275027112073531711385)
          ·
            refine ⟨1086956270334055148783539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449275027112073531711385 1086956270334055148783539)
            ·
              refine ⟨1630434405501082723175309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086956270334055148783539 1630434405501082723175309)
              ·
                refine ⟨611412902062906021190741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1630434405501082723175309 611412902062906021190741)
                ·
                  refine ⟨7164994946049679935829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 611412902062906021190741 7164994946049679935829)
                  ·
                    rfl

theorem cell22_62792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_62792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62792 prefixEnd_62792 := by exact prefixLift 62792
  have htrace : WordTrace (prefixWord ++ tailWord_62792) baseStart_62792 baseEnd_62792 := by
    simpa [prefixWord, tailWord_62792, baseEnd_62792] using wordTrace_append hprefix tailTrace_62792
  have hstable : (prefixWord ++ tailWord_62792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62792).length < 2 ^ (prefixWord ++ tailWord_62792).sum := by decide
  have hdescent : baseEnd_62792 < baseStart_62792 := by decide
  rcases family_descends (prefixWord ++ tailWord_62792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62841 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_62841 : Nat := 118140960795 + 62841 * 2 ^ 59
def prefixEnd_62841 : Nat := 4983230072969 + 3 ^ 40 * 62841 * 2
def baseEnd_62841 : Nat := 21511758539529245332337

theorem tailTrace_62841 : CollatzResearch.WordTrace tailWord_62841 prefixEnd_62841 21511758539529245332337 := by
  unfold tailWord_62841
  simp only [CollatzResearch.WordTrace]
  refine ⟨2291999565345264233460377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1527999710230176155640251 2291999565345264233460377)
  ·
    refine ⟨1718999674008948175095283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2291999565345264233460377 1718999674008948175095283)
    ·
      refine ⟨2578499511013422262642925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718999674008948175095283 2578499511013422262642925)
      ·
        refine ⟨966937316630033348491097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2578499511013422262642925 966937316630033348491097)
        ·
          refine ⟨725202987472525011368323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966937316630033348491097 725202987472525011368323)
          ·
            refine ⟨1087804481208787517052485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725202987472525011368323 1087804481208787517052485)
            ·
              refine ⟨203963340226647659447341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1087804481208787517052485 203963340226647659447341)
              ·
                refine ⟨76486252584992872292753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203963340226647659447341 76486252584992872292753)
                ·
                  refine ⟨57364689438744654219565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76486252584992872292753 57364689438744654219565)
                  ·
                    refine ⟨21511758539529245332337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57364689438744654219565 21511758539529245332337)
                    ·
                      rfl

theorem cell22_62841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_62841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62841 prefixEnd_62841 := by exact prefixLift 62841
  have htrace : WordTrace (prefixWord ++ tailWord_62841) baseStart_62841 baseEnd_62841 := by
    simpa [prefixWord, tailWord_62841, baseEnd_62841] using wordTrace_append hprefix tailTrace_62841
  have hstable : (prefixWord ++ tailWord_62841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62841).length < 2 ^ (prefixWord ++ tailWord_62841).sum := by decide
  have hdescent : baseEnd_62841 < baseStart_62841 := by decide
  rcases family_descends (prefixWord ++ tailWord_62841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62856 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_62856 : Nat := 118140960795 + 62856 * 2 ^ 59
def prefixEnd_62856 : Nat := 4983230072969 + 3 ^ 40 * 62856 * 2
def baseEnd_62856 : Nat := 21516893346074206207291

theorem tailTrace_62856 : CollatzResearch.WordTrace tailWord_62856 prefixEnd_62856 21516893346074206207291 := by
  unfold tailWord_62856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146273330145460897628211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1528364440193947863504281 1146273330145460897628211)
  ·
    refine ⟨1719409995218191346442317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146273330145460897628211 1719409995218191346442317)
    ·
      refine ⟨644778748206821754915869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1719409995218191346442317 644778748206821754915869)
      ·
        refine ⟨241792030577558158093451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644778748206821754915869 241792030577558158093451)
        ·
          refine ⟨362688045866337237140177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241792030577558158093451 362688045866337237140177)
          ·
            refine ⟨272016034399752927855133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362688045866337237140177 272016034399752927855133)
            ·
              refine ⟨102006012899907347945675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272016034399752927855133 102006012899907347945675)
              ·
                refine ⟨153009019349861021918513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102006012899907347945675 153009019349861021918513)
                ·
                  refine ⟨114756764512395766438885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153009019349861021918513 114756764512395766438885)
                  ·
                    refine ⟨21516893346074206207291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114756764512395766438885 21516893346074206207291)
                    ·
                      rfl

theorem cell22_62856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_62856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62856 prefixEnd_62856 := by exact prefixLift 62856
  have htrace : WordTrace (prefixWord ++ tailWord_62856) baseStart_62856 baseEnd_62856 := by
    simpa [prefixWord, tailWord_62856, baseEnd_62856] using wordTrace_append hprefix tailTrace_62856
  have hstable : (prefixWord ++ tailWord_62856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62856).length < 2 ^ (prefixWord ++ tailWord_62856).sum := by decide
  have hdescent : baseEnd_62856 < baseStart_62856 := by decide
  rcases family_descends (prefixWord ++ tailWord_62856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62862 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_62862 : Nat := 118140960795 + 62862 * 2 ^ 59
def prefixEnd_62862 : Nat := 4983230072969 + 3 ^ 40 * 62862 * 2
def baseEnd_62862 : Nat := 21518947268692190557273

theorem tailTrace_62862 : CollatzResearch.WordTrace tailWord_62862 prefixEnd_62862 21518947268692190557273 := by
  unfold tailWord_62862
  simp only [CollatzResearch.WordTrace]
  refine ⟨286595687283648102496855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1528510332179456546649893 286595687283648102496855)
  ·
    refine ⟨429893530925472153745283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286595687283648102496855 429893530925472153745283)
    ·
      refine ⟨644840296388208230617925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429893530925472153745283 644840296388208230617925)
      ·
        refine ⟨120907555572789043240861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 644840296388208230617925 120907555572789043240861)
        ·
          refine ⟨45340333339795891215323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120907555572789043240861 45340333339795891215323)
          ·
            refine ⟨68010500009693836822985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45340333339795891215323 68010500009693836822985)
            ·
              refine ⟨51007875007270377617239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68010500009693836822985 51007875007270377617239)
              ·
                refine ⟨76511812510905566425859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51007875007270377617239 76511812510905566425859)
                ·
                  refine ⟨114767718766358349638789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76511812510905566425859 114767718766358349638789)
                  ·
                    refine ⟨21518947268692190557273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114767718766358349638789 21518947268692190557273)
                    ·
                      rfl

theorem cell22_62862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_62862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62862 prefixEnd_62862 := by exact prefixLift 62862
  have htrace : WordTrace (prefixWord ++ tailWord_62862) baseStart_62862 baseEnd_62862 := by
    simpa [prefixWord, tailWord_62862, baseEnd_62862] using wordTrace_append hprefix tailTrace_62862
  have hstable : (prefixWord ++ tailWord_62862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62862).length < 2 ^ (prefixWord ++ tailWord_62862).sum := by decide
  have hdescent : baseEnd_62862 < baseStart_62862 := by decide
  rcases family_descends (prefixWord ++ tailWord_62862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62899 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 5]
def baseStart_62899 : Nat := 118140960795 + 62899 * 2 ^ 59
def prefixEnd_62899 : Nat := 4983230072969 + 3 ^ 40 * 62899 * 2
def baseEnd_62899 : Nat := 7177204374945475794053

theorem tailTrace_62899 : CollatzResearch.WordTrace tailWord_62899 prefixEnd_62899 7177204374945475794053 := by
  unfold tailWord_62899
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294114999135140139071751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1529409999423426759381167 2294114999135140139071751)
  ·
    refine ⟨3441172498702710208607627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2294114999135140139071751 3441172498702710208607627)
    ·
      refine ⟨5161758748054065312911441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3441172498702710208607627 5161758748054065312911441)
      ·
        refine ⟨3871319061040548984683581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5161758748054065312911441 3871319061040548984683581)
        ·
          refine ⟨1451744647890205869256343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3871319061040548984683581 1451744647890205869256343)
          ·
            refine ⟨2177616971835308803884515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451744647890205869256343 2177616971835308803884515)
            ·
              refine ⟨3266425457752963205826773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177616971835308803884515 3266425457752963205826773)
              ·
                refine ⟨76556846666085075136565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3266425457752963205826773 76556846666085075136565)
                ·
                  refine ⟨7177204374945475794053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76556846666085075136565 7177204374945475794053)
                  ·
                    rfl

theorem cell22_62899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 5].length) (baseStart_62899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62899 prefixEnd_62899 := by exact prefixLift 62899
  have htrace : WordTrace (prefixWord ++ tailWord_62899) baseStart_62899 baseEnd_62899 := by
    simpa [prefixWord, tailWord_62899, baseEnd_62899] using wordTrace_append hprefix tailTrace_62899
  have hstable : (prefixWord ++ tailWord_62899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62899).length < 2 ^ (prefixWord ++ tailWord_62899).sum := by decide
  have hdescent : baseEnd_62899 < baseStart_62899 := by decide
  rcases family_descends (prefixWord ++ tailWord_62899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62916 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_62916 : Nat := 118140960795 + 62916 * 2 ^ 59
def prefixEnd_62916 : Nat := 4983230072969 + 3 ^ 40 * 62916 * 2
def baseEnd_62916 : Nat := 7179144190751349902369

theorem tailTrace_62916 : CollatzResearch.WordTrace tailWord_62916 prefixEnd_62916 7179144190751349902369 := by
  unfold tailWord_62916
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147367520036776021220301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1529823360049034694960401 1147367520036776021220301)
  ·
    refine ⟨430262820013791007957613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1147367520036776021220301 430262820013791007957613)
    ·
      refine ⟨161348557505171627984105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430262820013791007957613 161348557505171627984105)
      ·
        refine ⟨121011418128878720988079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161348557505171627984105 121011418128878720988079)
        ·
          refine ⟨181517127193318081482119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121011418128878720988079 181517127193318081482119)
          ·
            refine ⟨272275690789977122223179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181517127193318081482119 272275690789977122223179)
            ·
              refine ⟨408413536184965683334769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272275690789977122223179 408413536184965683334769)
              ·
                refine ⟨306310152138724262501077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408413536184965683334769 306310152138724262501077)
                ·
                  refine ⟨7179144190751349902369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 306310152138724262501077 7179144190751349902369)
                  ·
                    rfl

theorem cell22_62916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_62916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62916 prefixEnd_62916 := by exact prefixLift 62916
  have htrace : WordTrace (prefixWord ++ tailWord_62916) baseStart_62916 baseEnd_62916 := by
    simpa [prefixWord, tailWord_62916, baseEnd_62916] using wordTrace_append hprefix tailTrace_62916
  have hstable : (prefixWord ++ tailWord_62916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62916).length < 2 ^ (prefixWord ++ tailWord_62916).sum := by decide
  have hdescent : baseEnd_62916 < baseStart_62916 := by decide
  rcases family_descends (prefixWord ++ tailWord_62916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62929 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_62929 : Nat := 118140960795 + 62929 * 2 ^ 59
def prefixEnd_62929 : Nat := 4983230072969 + 3 ^ 40 * 62929 * 2
def baseEnd_62929 : Nat := 21541882737926349132067

theorem tailTrace_62929 : CollatzResearch.WordTrace tailWord_62929 prefixEnd_62929 21541882737926349132067 := by
  unfold tailWord_62929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295209189026455262663841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1530139459350970175109227 2295209189026455262663841)
  ·
    refine ⟨1721406891769841446997881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2295209189026455262663841 1721406891769841446997881)
    ·
      refine ⟨1291055168827381085248411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1721406891769841446997881 1291055168827381085248411)
      ·
        refine ⟨1936582753241071627872617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291055168827381085248411 1936582753241071627872617)
        ·
          refine ⟨1452437064930803720904463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936582753241071627872617 1452437064930803720904463)
          ·
            refine ⟨2178655597396205581356695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452437064930803720904463 2178655597396205581356695)
            ·
              refine ⟨3267983396094308372035043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178655597396205581356695 3267983396094308372035043)
              ·
                refine ⟨4901975094141462558052565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267983396094308372035043 4901975094141462558052565)
                ·
                  refine ⟨114890041268940528704357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4901975094141462558052565 114890041268940528704357)
                  ·
                    refine ⟨21541882737926349132067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114890041268940528704357 21541882737926349132067)
                    ·
                      rfl

theorem cell22_62929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_62929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62929 prefixEnd_62929 := by exact prefixLift 62929
  have htrace : WordTrace (prefixWord ++ tailWord_62929) baseStart_62929 baseEnd_62929 := by
    simpa [prefixWord, tailWord_62929, baseEnd_62929] using wordTrace_append hprefix tailTrace_62929
  have hstable : (prefixWord ++ tailWord_62929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62929).length < 2 ^ (prefixWord ++ tailWord_62929).sum := by decide
  have hdescent : baseEnd_62929 < baseStart_62929 := by decide
  rcases family_descends (prefixWord ++ tailWord_62929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62944 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_62944 : Nat := 118140960795 + 62944 * 2 ^ 59
def prefixEnd_62944 : Nat := 4983230072969 + 3 ^ 40 * 62944 * 2
def baseEnd_62944 : Nat := 7182339181490436669007

theorem tailTrace_62944 : CollatzResearch.WordTrace tailWord_62944 prefixEnd_62944 7182339181490436669007 := by
  unfold tailWord_62944
  simp only [CollatzResearch.WordTrace]
  refine ⟨1147878141986056412229943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1530504189314741882973257 1147878141986056412229943)
  ·
    refine ⟨1721817212979084618344915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1147878141986056412229943 1721817212979084618344915)
    ·
      refine ⟨2582725819468626927517373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721817212979084618344915 2582725819468626927517373)
      ·
        refine ⟨968522182300735097819015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2582725819468626927517373 968522182300735097819015)
        ·
          refine ⟨1452783273451102646728523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968522182300735097819015 1452783273451102646728523)
          ·
            refine ⟨2179174910176653970092785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452783273451102646728523 2179174910176653970092785)
            ·
              refine ⟨1634381182632490477569589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179174910176653970092785 1634381182632490477569589)
              ·
                refine ⟨153223235871795982272149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1634381182632490477569589 153223235871795982272149)
                ·
                  refine ⟨7182339181490436669007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 153223235871795982272149 7182339181490436669007)
                  ·
                    rfl

theorem cell22_62944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_62944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62944 prefixEnd_62944 := by exact prefixLift 62944
  have htrace : WordTrace (prefixWord ++ tailWord_62944) baseStart_62944 baseEnd_62944 := by
    simpa [prefixWord, tailWord_62944, baseEnd_62944] using wordTrace_append hprefix tailTrace_62944
  have hstable : (prefixWord ++ tailWord_62944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62944).length < 2 ^ (prefixWord ++ tailWord_62944).sum := by decide
  have hdescent : baseEnd_62944 < baseStart_62944 := by decide
  rcases family_descends (prefixWord ++ tailWord_62944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62993 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_62993 : Nat := 118140960795 + 62993 * 2 ^ 59
def prefixEnd_62993 : Nat := 4983230072969 + 3 ^ 40 * 62993 * 2
def baseEnd_62993 : Nat := 21563791245851515531871

theorem tailTrace_62993 : CollatzResearch.WordTrace tailWord_62993 prefixEnd_62993 21563791245851515531871 := by
  unfold tailWord_62993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297543460794594192993633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1531695640529729461995755 2297543460794594192993633)
  ·
    refine ⟨1723157595595945644745225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2297543460794594192993633 1723157595595945644745225)
    ·
      refine ⟨1292368196696959233558919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1723157595595945644745225 1292368196696959233558919)
      ·
        refine ⟨1938552295045438850338379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292368196696959233558919 1938552295045438850338379)
        ·
          refine ⟨2907828442568158275507569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938552295045438850338379 2907828442568158275507569)
          ·
            refine ⟨2180871331926118706630677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907828442568158275507569 2180871331926118706630677)
            ·
              refine ⟨102228343684036814373313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2180871331926118706630677 102228343684036814373313)
              ·
                refine ⟨76671257763027610779985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102228343684036814373313 76671257763027610779985)
                ·
                  refine ⟨57503443322270708084989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76671257763027610779985 57503443322270708084989)
                  ·
                    refine ⟨21563791245851515531871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57503443322270708084989 21563791245851515531871)
                    ·
                      rfl

theorem cell22_62993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_62993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62993 prefixEnd_62993 := by exact prefixLift 62993
  have htrace : WordTrace (prefixWord ++ tailWord_62993) baseStart_62993 baseEnd_62993 := by
    simpa [prefixWord, tailWord_62993, baseEnd_62993] using wordTrace_append hprefix tailTrace_62993
  have hstable : (prefixWord ++ tailWord_62993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62993).length < 2 ^ (prefixWord ++ tailWord_62993).sum := by decide
  have hdescent : baseEnd_62993 < baseStart_62993 := by decide
  rcases family_descends (prefixWord ++ tailWord_62993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62995 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 4]
def baseStart_62995 : Nat := 118140960795 + 62995 * 2 ^ 59
def prefixEnd_62995 : Nat := 4983230072969 + 3 ^ 40 * 62995 * 2
def baseEnd_62995 : Nat := 7188158628908058993955

theorem tailTrace_62995 : CollatzResearch.WordTrace tailWord_62995 prefixEnd_62995 7188158628908058993955 := by
  unfold tailWord_62995
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297616406787348534566439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1531744271191565689710959 2297616406787348534566439)
  ·
    refine ⟨3446424610181022801849659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2297616406787348534566439 3446424610181022801849659)
    ·
      refine ⟨5169636915271534202774489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3446424610181022801849659 5169636915271534202774489)
      ·
        refine ⟨3877227686453650652080867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5169636915271534202774489 3877227686453650652080867)
        ·
          refine ⟨5815841529680475978121301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877227686453650652080867 5815841529680475978121301)
          ·
            refine ⟨68154392925943077868609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 5815841529680475978121301 68154392925943077868609)
            ·
              refine ⟨51115794694457308401457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68154392925943077868609 51115794694457308401457)
              ·
                refine ⟨38336846020842981301093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51115794694457308401457 38336846020842981301093)
                ·
                  refine ⟨7188158628908058993955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38336846020842981301093 7188158628908058993955)
                  ·
                    rfl

theorem cell22_62995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 4].length) (baseStart_62995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_62995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_62995 prefixEnd_62995 := by exact prefixLift 62995
  have htrace : WordTrace (prefixWord ++ tailWord_62995) baseStart_62995 baseEnd_62995 := by
    simpa [prefixWord, tailWord_62995, baseEnd_62995] using wordTrace_append hprefix tailTrace_62995
  have hstable : (prefixWord ++ tailWord_62995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62995).length < 2 ^ (prefixWord ++ tailWord_62995).sum := by decide
  have hdescent : baseEnd_62995 < baseStart_62995 := by decide
  rcases family_descends (prefixWord ++ tailWord_62995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63081 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_63081 : Nat := 118140960795 + 63081 * 2 ^ 59
def prefixEnd_63081 : Nat := 4983230072969 + 3 ^ 40 * 63081 * 2
def baseEnd_63081 : Nat := 21593915444248619331601

theorem tailTrace_63081 : CollatzResearch.WordTrace tailWord_63081 prefixEnd_63081 21593915444248619331601 := by
  unfold tailWord_63081
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300753084475785222197097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1533835389650523481464731 2300753084475785222197097)
  ·
    refine ⟨1725564813356838916647823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2300753084475785222197097 1725564813356838916647823)
    ·
      refine ⟨2588347220035258374971735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725564813356838916647823 2588347220035258374971735)
      ·
        refine ⟨3882520830052887562457603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588347220035258374971735 3882520830052887562457603)
        ·
          refine ⟨5823781245079331343686405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882520830052887562457603 5823781245079331343686405)
          ·
            refine ⟨1091958983452374626941201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5823781245079331343686405 1091958983452374626941201)
            ·
              refine ⟨818969237589280970205901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091958983452374626941201 818969237589280970205901)
              ·
                refine ⟨307113464095980363827213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818969237589280970205901 307113464095980363827213)
                ·
                  refine ⟨115167549035992636435205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 307113464095980363827213 115167549035992636435205)
                  ·
                    refine ⟨21593915444248619331601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115167549035992636435205 21593915444248619331601)
                    ·
                      rfl

theorem cell22_63081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_63081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63081 prefixEnd_63081 := by exact prefixLift 63081
  have htrace : WordTrace (prefixWord ++ tailWord_63081) baseStart_63081 baseEnd_63081 := by
    simpa [prefixWord, tailWord_63081, baseEnd_63081] using wordTrace_append hprefix tailTrace_63081
  have hstable : (prefixWord ++ tailWord_63081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63081).length < 2 ^ (prefixWord ++ tailWord_63081).sum := by decide
  have hdescent : baseEnd_63081 < baseStart_63081 := by decide
  rcases family_descends (prefixWord ++ tailWord_63081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63113 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 4]
def baseStart_63113 : Nat := 118140960795 + 63113 * 2 ^ 59
def prefixEnd_63113 : Nat := 4983230072969 + 3 ^ 40 * 63113 * 2
def baseEnd_63113 : Nat := 7201623232737067510501

theorem tailTrace_63113 : CollatzResearch.WordTrace tailWord_63113 prefixEnd_63113 7201623232737067510501 := by
  unfold tailWord_63113
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301920220359854687361993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1534613480239903124907995 2301920220359854687361993)
  ·
    refine ⟨1726440165269891015521495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2301920220359854687361993 1726440165269891015521495)
    ·
      refine ⟨2589660247904836523282243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726440165269891015521495 2589660247904836523282243)
      ·
        refine ⟨3884490371857254784923365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589660247904836523282243 3884490371857254784923365)
        ·
          refine ⟨728341944723235272173131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3884490371857254784923365 728341944723235272173131)
          ·
            refine ⟨1092512917084852908259697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728341944723235272173131 1092512917084852908259697)
            ·
              refine ⟨819384687813639681194773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092512917084852908259697 819384687813639681194773)
              ·
                refine ⟨38408657241264360056005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 819384687813639681194773 38408657241264360056005)
                ·
                  refine ⟨7201623232737067510501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38408657241264360056005 7201623232737067510501)
                  ·
                    rfl

theorem cell22_63113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_63113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63113 prefixEnd_63113 := by exact prefixLift 63113
  have htrace : WordTrace (prefixWord ++ tailWord_63113) baseStart_63113 baseEnd_63113 := by
    simpa [prefixWord, tailWord_63113, baseEnd_63113] using wordTrace_append hprefix tailTrace_63113
  have hstable : (prefixWord ++ tailWord_63113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63113).length < 2 ^ (prefixWord ++ tailWord_63113).sum := by decide
  have hdescent : baseEnd_63113 < baseStart_63113 := by decide
  rcases family_descends (prefixWord ++ tailWord_63113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63132 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_63132 : Nat := 118140960795 + 63132 * 2 ^ 59
def prefixEnd_63132 : Nat := 4983230072969 + 3 ^ 40 * 63132 * 2
def baseEnd_63132 : Nat := 21611373786501486306445

theorem tailTrace_63132 : CollatzResearch.WordTrace tailWord_63132 prefixEnd_63132 21611373786501486306445 := by
  unfold tailWord_63132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151306603645510466151825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1535075471527347288202433 1151306603645510466151825)
  ·
    refine ⟨863479952734132849613869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1151306603645510466151825 863479952734132849613869)
    ·
      refine ⟨323804982275299818605201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 863479952734132849613869 323804982275299818605201)
      ·
        refine ⟨242853736706474863953901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323804982275299818605201 242853736706474863953901)
        ·
          refine ⟨91070151264928073982713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 242853736706474863953901 91070151264928073982713)
          ·
            refine ⟨68302613448696055487035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91070151264928073982713 68302613448696055487035)
            ·
              refine ⟨102453920173044083230553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68302613448696055487035 102453920173044083230553)
              ·
                refine ⟨76840440129783062422915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102453920173044083230553 76840440129783062422915)
                ·
                  refine ⟨115260660194674593634373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76840440129783062422915 115260660194674593634373)
                  ·
                    refine ⟨21611373786501486306445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115260660194674593634373 21611373786501486306445)
                    ·
                      rfl

theorem cell22_63132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_63132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63132 prefixEnd_63132 := by exact prefixLift 63132
  have htrace : WordTrace (prefixWord ++ tailWord_63132) baseStart_63132 baseEnd_63132 := by
    simpa [prefixWord, tailWord_63132, baseEnd_63132] using wordTrace_append hprefix tailTrace_63132
  have hstable : (prefixWord ++ tailWord_63132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63132).length < 2 ^ (prefixWord ++ tailWord_63132).sum := by decide
  have hdescent : baseEnd_63132 < baseStart_63132 := by decide
  rcases family_descends (prefixWord ++ tailWord_63132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63141 : List Nat := [1, 3, 1, 2, 1, 2, 4, 8]
def baseStart_63141 : Nat := 118140960795 + 63141 * 2 ^ 59
def prefixEnd_63141 : Nat := 4983230072969 + 3 ^ 40 * 63141 * 2
def baseEnd_63141 : Nat := 2401606074492051425713

theorem tailTrace_63141 : CollatzResearch.WordTrace tailWord_63141 prefixEnd_63141 2401606074492051425713 := by
  unfold tailWord_63141
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302941464258415469381277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1535294309505610312920851 2302941464258415469381277)
  ·
    refine ⟨863603049096905801017979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2302941464258415469381277 863603049096905801017979)
    ·
      refine ⟨1295404573645358701526969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863603049096905801017979 1295404573645358701526969)
      ·
        refine ⟨971553430234019026145227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295404573645358701526969 971553430234019026145227)
        ·
          refine ⟨1457330145351028539217841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971553430234019026145227 1457330145351028539217841)
          ·
            refine ⟨1092997609013271404413381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457330145351028539217841 1092997609013271404413381)
            ·
              refine ⟨204937051689988388327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1092997609013271404413381 204937051689988388327509)
              ·
                refine ⟨2401606074492051425713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 204937051689988388327509 2401606074492051425713)
                ·
                  rfl

theorem cell22_63141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 8].length) (baseStart_63141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63141 prefixEnd_63141 := by exact prefixLift 63141
  have htrace : WordTrace (prefixWord ++ tailWord_63141) baseStart_63141 baseEnd_63141 := by
    simpa [prefixWord, tailWord_63141, baseEnd_63141] using wordTrace_append hprefix tailTrace_63141
  have hstable : (prefixWord ++ tailWord_63141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63141).length < 2 ^ (prefixWord ++ tailWord_63141).sum := by decide
  have hdescent : baseEnd_63141 < baseStart_63141 := by decide
  rcases family_descends (prefixWord ++ tailWord_63141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63218 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_63218 : Nat := 118140960795 + 63218 * 2 ^ 59
def prefixEnd_63218 : Nat := 4983230072969 + 3 ^ 40 * 63218 * 2
def baseEnd_63218 : Nat := 21640813344025928656181

theorem tailTrace_63218 : CollatzResearch.WordTrace tailWord_63218 prefixEnd_63218 21640813344025928656181 := by
  unfold tailWord_63218
  simp only [CollatzResearch.WordTrace]
  refine ⟨576437471244864404983577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1537166589986305079956205 576437471244864404983577)
  ·
    refine ⟨432328103433648303737683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 576437471244864404983577 432328103433648303737683)
    ·
      refine ⟨648492155150472455606525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432328103433648303737683 648492155150472455606525)
      ·
        refine ⟨243184558181427170852447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648492155150472455606525 243184558181427170852447)
        ·
          refine ⟨364776837272140756278671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243184558181427170852447 364776837272140756278671)
          ·
            refine ⟨547165255908211134418007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364776837272140756278671 547165255908211134418007)
            ·
              refine ⟨820747883862316701627011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547165255908211134418007 820747883862316701627011)
              ·
                refine ⟨1231121825793475052440517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820747883862316701627011 1231121825793475052440517)
                ·
                  refine ⟨230835342336276572332597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231121825793475052440517 230835342336276572332597)
                  ·
                    refine ⟨21640813344025928656181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230835342336276572332597 21640813344025928656181)
                    ·
                      rfl

theorem cell22_63218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_63218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63218 prefixEnd_63218 := by exact prefixLift 63218
  have htrace : WordTrace (prefixWord ++ tailWord_63218) baseStart_63218 baseEnd_63218 := by
    simpa [prefixWord, tailWord_63218, baseEnd_63218] using wordTrace_append hprefix tailTrace_63218
  have hstable : (prefixWord ++ tailWord_63218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63218).length < 2 ^ (prefixWord ++ tailWord_63218).sum := by decide
  have hdescent : baseEnd_63218 < baseStart_63218 := by decide
  rcases family_descends (prefixWord ++ tailWord_63218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63233 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_63233 : Nat := 118140960795 + 63233 * 2 ^ 59
def prefixEnd_63233 : Nat := 4983230072969 + 3 ^ 40 * 63233 * 2
def baseEnd_63233 : Nat := 21645948150570889531135

theorem tailTrace_63233 : CollatzResearch.WordTrace tailWord_63233 prefixEnd_63233 21645948150570889531135 := by
  unfold tailWord_63233
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306296979925115181730353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1537531319950076787820235 2306296979925115181730353)
  ·
    refine ⟨1729722734943836386297765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2306296979925115181730353 1729722734943836386297765)
    ·
      refine ⟨324323012801969322430831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1729722734943836386297765 324323012801969322430831)
      ·
        refine ⟨486484519202953983646247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324323012801969322430831 486484519202953983646247)
        ·
          refine ⟨729726778804430975469371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486484519202953983646247 729726778804430975469371)
          ·
            refine ⟨1094590168206646463204057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729726778804430975469371 1094590168206646463204057)
            ·
              refine ⟨820942626154984847403043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094590168206646463204057 820942626154984847403043)
              ·
                refine ⟨1231413939232477271104565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820942626154984847403043 1231413939232477271104565)
                ·
                  refine ⟨115445056803044744166053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1231413939232477271104565 115445056803044744166053)
                  ·
                    refine ⟨21645948150570889531135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115445056803044744166053 21645948150570889531135)
                    ·
                      rfl

theorem cell22_63233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_63233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63233 prefixEnd_63233 := by exact prefixLift 63233
  have htrace : WordTrace (prefixWord ++ tailWord_63233) baseStart_63233 baseEnd_63233 := by
    simpa [prefixWord, tailWord_63233, baseEnd_63233] using wordTrace_append hprefix tailTrace_63233
  have hstable : (prefixWord ++ tailWord_63233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63233).length < 2 ^ (prefixWord ++ tailWord_63233).sum := by decide
  have hdescent : baseEnd_63233 < baseStart_63233 := by decide
  rcases family_descends (prefixWord ++ tailWord_63233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63263 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_63263 : Nat := 118140960795 + 63263 * 2 ^ 59
def prefixEnd_63263 : Nat := 4983230072969 + 3 ^ 40 * 63263 * 2
def baseEnd_63263 : Nat := 21656217763660811281043

theorem tailTrace_63263 : CollatzResearch.WordTrace tailWord_63263 prefixEnd_63263 21656217763660811281043 := by
  unfold tailWord_63263
  simp only [CollatzResearch.WordTrace]
  refine ⟨2307391169816430305322443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1538260779877620203548295 2307391169816430305322443)
  ·
    refine ⟨3461086754724645457983665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2307391169816430305322443 3461086754724645457983665)
    ·
      refine ⟨2595815066043484093487749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3461086754724645457983665 2595815066043484093487749)
      ·
        refine ⟨486715324883153267528953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2595815066043484093487749 486715324883153267528953)
        ·
          refine ⟨365036493662364950646715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 486715324883153267528953 365036493662364950646715)
          ·
            refine ⟨547554740493547425970073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365036493662364950646715 547554740493547425970073)
            ·
              refine ⟨410666055370160569477555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547554740493547425970073 410666055370160569477555)
              ·
                refine ⟨615999083055240854216333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410666055370160569477555 615999083055240854216333)
                ·
                  refine ⟨230999656145715320331125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615999083055240854216333 230999656145715320331125)
                  ·
                    refine ⟨21656217763660811281043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230999656145715320331125 21656217763660811281043)
                    ·
                      rfl

theorem cell22_63263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_63263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63263 prefixEnd_63263 := by exact prefixLift 63263
  have htrace : WordTrace (prefixWord ++ tailWord_63263) baseStart_63263 baseEnd_63263 := by
    simpa [prefixWord, tailWord_63263, baseEnd_63263] using wordTrace_append hprefix tailTrace_63263
  have hstable : (prefixWord ++ tailWord_63263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63263).length < 2 ^ (prefixWord ++ tailWord_63263).sum := by decide
  have hdescent : baseEnd_63263 < baseStart_63263 := by decide
  rcases family_descends (prefixWord ++ tailWord_63263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63432 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_63432 : Nat := 118140960795 + 63432 * 2 ^ 59
def prefixEnd_63432 : Nat := 4983230072969 + 3 ^ 40 * 63432 * 2
def baseEnd_63432 : Nat := 21714069917400703805525

theorem tailTrace_63432 : CollatzResearch.WordTrace tailWord_63432 prefixEnd_63432 21714069917400703805525 := by
  unfold tailWord_63432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156777553102086084112275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1542370070802781445483033 1156777553102086084112275)
  ·
    refine ⟨1735166329653129126168413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1156777553102086084112275 1735166329653129126168413)
    ·
      refine ⟨650687373619923422313155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1735166329653129126168413 650687373619923422313155)
      ·
        refine ⟨976031060429885133469733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650687373619923422313155 976031060429885133469733)
        ·
          refine ⟨183005823830603462525575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 976031060429885133469733 183005823830603462525575)
          ·
            refine ⟨274508735745905193788363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183005823830603462525575 274508735745905193788363)
            ·
              refine ⟨411763103618857790682545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274508735745905193788363 411763103618857790682545)
              ·
                refine ⟨308822327714143343011909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411763103618857790682545 308822327714143343011909)
                ·
                  refine ⟨57904186446401876814733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 308822327714143343011909 57904186446401876814733)
                  ·
                    refine ⟨21714069917400703805525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57904186446401876814733 21714069917400703805525)
                    ·
                      rfl

theorem cell22_63432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_63432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63432 prefixEnd_63432 := by exact prefixLift 63432
  have htrace : WordTrace (prefixWord ++ tailWord_63432) baseStart_63432 baseEnd_63432 := by
    simpa [prefixWord, tailWord_63432, baseEnd_63432] using wordTrace_append hprefix tailTrace_63432
  have hstable : (prefixWord ++ tailWord_63432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63432).length < 2 ^ (prefixWord ++ tailWord_63432).sum := by decide
  have hdescent : baseEnd_63432 < baseStart_63432 := by decide
  rcases family_descends (prefixWord ++ tailWord_63432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63445 : List Nat := [1, 3, 2, 3, 2, 1, 10]
def baseStart_63445 : Nat := 118140960795 + 63445 * 2 ^ 59
def prefixEnd_63445 : Nat := 4983230072969 + 3 ^ 40 * 63445 * 2
def baseEnd_63445 : Nat := 804389632706407527055

theorem tailTrace_63445 : CollatzResearch.WordTrace tailWord_63445 prefixEnd_63445 804389632706407527055 := by
  unfold tailWord_63445
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314029255157075388447789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1542686170104716925631859 2314029255157075388447789)
  ·
    refine ⟨867760970683903270667921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2314029255157075388447789 867760970683903270667921)
    ·
      refine ⟨650820728012927453000941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867760970683903270667921 650820728012927453000941)
      ·
        refine ⟨244057773004847794875353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 650820728012927453000941 244057773004847794875353)
        ·
          refine ⟨183043329753635846156515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244057773004847794875353 183043329753635846156515)
          ·
            refine ⟨274564994630453769234773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183043329753635846156515 274564994630453769234773)
            ·
              refine ⟨804389632706407527055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 274564994630453769234773 804389632706407527055)
              ·
                rfl

theorem cell22_63445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 10].length) (baseStart_63445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63445 prefixEnd_63445 := by exact prefixLift 63445
  have htrace : WordTrace (prefixWord ++ tailWord_63445) baseStart_63445 baseEnd_63445 := by
    simpa [prefixWord, tailWord_63445, baseEnd_63445] using wordTrace_append hprefix tailTrace_63445
  have hstable : (prefixWord ++ tailWord_63445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63445).length < 2 ^ (prefixWord ++ tailWord_63445).sum := by decide
  have hdescent : baseEnd_63445 < baseStart_63445 := by decide
  rcases family_descends (prefixWord ++ tailWord_63445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63522 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_63522 : Nat := 118140960795 + 63522 * 2 ^ 59
def prefixEnd_63522 : Nat := 4983230072969 + 3 ^ 40 * 63522 * 2
def baseEnd_63522 : Nat := 21744878756670469055249

theorem tailTrace_63522 : CollatzResearch.WordTrace tailWord_63522 prefixEnd_63522 21744878756670469055249 := by
  unfold tailWord_63522
  simp only [CollatzResearch.WordTrace]
  refine ⟨579209418969529384750205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1544558450585411692667213 579209418969529384750205)
  ·
    refine ⟨217203532113573519281327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 579209418969529384750205 217203532113573519281327)
    ·
      refine ⟨325805298170360278921991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217203532113573519281327 325805298170360278921991)
      ·
        refine ⟨488707947255540418382987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325805298170360278921991 488707947255540418382987)
        ·
          refine ⟨733061920883310627574481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488707947255540418382987 733061920883310627574481)
          ·
            refine ⟨549796440662482970680861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733061920883310627574481 549796440662482970680861)
            ·
              refine ⟨206173665248431114005323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 549796440662482970680861 206173665248431114005323)
              ·
                refine ⟨309260497872646671007985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206173665248431114005323 309260497872646671007985)
                ·
                  refine ⟨231945373404485003255989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309260497872646671007985 231945373404485003255989)
                  ·
                    refine ⟨21744878756670469055249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231945373404485003255989 21744878756670469055249)
                    ·
                      rfl

theorem cell22_63522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_63522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63522 prefixEnd_63522 := by exact prefixLift 63522
  have htrace : WordTrace (prefixWord ++ tailWord_63522) baseStart_63522 baseEnd_63522 := by
    simpa [prefixWord, tailWord_63522, baseEnd_63522] using wordTrace_append hprefix tailTrace_63522
  have hstable : (prefixWord ++ tailWord_63522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63522).length < 2 ^ (prefixWord ++ tailWord_63522).sum := by decide
  have hdescent : baseEnd_63522 < baseStart_63522 := by decide
  rcases family_descends (prefixWord ++ tailWord_63522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63537 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_63537 : Nat := 118140960795 + 63537 * 2 ^ 59
def prefixEnd_63537 : Nat := 4983230072969 + 3 ^ 40 * 63537 * 2
def baseEnd_63537 : Nat := 21750013563215429930203

theorem tailTrace_63537 : CollatzResearch.WordTrace tailWord_63537 prefixEnd_63537 21750013563215429930203 := by
  unfold tailWord_63537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317384770823775100796865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1544923180549183400531243 2317384770823775100796865)
  ·
    refine ⟨1738038578117831325597649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2317384770823775100796865 1738038578117831325597649)
    ·
      refine ⟨1303528933588373494198237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1738038578117831325597649 1303528933588373494198237)
      ·
        refine ⟨488823350095640060324339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1303528933588373494198237 488823350095640060324339)
        ·
          refine ⟨733235025143460090486509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488823350095640060324339 733235025143460090486509)
          ·
            refine ⟨274963134428797533932441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733235025143460090486509 274963134428797533932441)
            ·
              refine ⟨206222350821598150449331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274963134428797533932441 206222350821598150449331)
              ·
                refine ⟨309333526232397225673997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206222350821598150449331 309333526232397225673997)
                ·
                  refine ⟨116000072337148959627749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309333526232397225673997 116000072337148959627749)
                  ·
                    refine ⟨21750013563215429930203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116000072337148959627749 21750013563215429930203)
                    ·
                      rfl

theorem cell22_63537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_63537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63537 prefixEnd_63537 := by exact prefixLift 63537
  have htrace : WordTrace (prefixWord ++ tailWord_63537) baseStart_63537 baseEnd_63537 := by
    simpa [prefixWord, tailWord_63537, baseEnd_63537] using wordTrace_append hprefix tailTrace_63537
  have hstable : (prefixWord ++ tailWord_63537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63537).length < 2 ^ (prefixWord ++ tailWord_63537).sum := by decide
  have hdescent : baseEnd_63537 < baseStart_63537 := by decide
  rcases family_descends (prefixWord ++ tailWord_63537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63567 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 4, 3]
def baseStart_63567 : Nat := 118140960795 + 63567 * 2 ^ 59
def prefixEnd_63567 : Nat := 4983230072969 + 3 ^ 40 * 63567 * 2
def baseEnd_63567 : Nat := 21760283176305351680111

theorem tailTrace_63567 : CollatzResearch.WordTrace tailWord_63567 prefixEnd_63567 21760283176305351680111 := by
  unfold tailWord_63567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2318478960715090224388955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1545652640476726816259303 2318478960715090224388955)
  ·
    refine ⟨3477718441072635336583433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2318478960715090224388955 3477718441072635336583433)
    ·
      refine ⟨2608288830804476502437575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3477718441072635336583433 2608288830804476502437575)
      ·
        refine ⟨3912433246206714753656363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2608288830804476502437575 3912433246206714753656363)
        ·
          refine ⟨5868649869310072130484545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3912433246206714753656363 5868649869310072130484545)
          ·
            refine ⟨4401487401982554097863409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5868649869310072130484545 4401487401982554097863409)
            ·
              refine ⟨3301115551486915573397557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401487401982554097863409 3301115551486915573397557)
              ·
                refine ⟨309479582951898335006021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3301115551486915573397557 309479582951898335006021)
                ·
                  refine ⟨58027421803480937813629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 309479582951898335006021 58027421803480937813629)
                  ·
                    refine ⟨21760283176305351680111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58027421803480937813629 21760283176305351680111)
                    ·
                      rfl

theorem cell22_63567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_63567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63567 prefixEnd_63567 := by exact prefixLift 63567
  have htrace : WordTrace (prefixWord ++ tailWord_63567) baseStart_63567 baseEnd_63567 := by
    simpa [prefixWord, tailWord_63567, baseEnd_63567] using wordTrace_append hprefix tailTrace_63567
  have hstable : (prefixWord ++ tailWord_63567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63567).length < 2 ^ (prefixWord ++ tailWord_63567).sum := by decide
  have hdescent : baseEnd_63567 < baseStart_63567 := by decide
  rcases family_descends (prefixWord ++ tailWord_63567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63584 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_63584 : Nat := 118140960795 + 63584 * 2 ^ 59
def prefixEnd_63584 : Nat := 4983230072969 + 3 ^ 40 * 63584 * 2
def baseEnd_63584 : Nat := 21766102623722974005059

theorem tailTrace_63584 : CollatzResearch.WordTrace tailWord_63584 prefixEnd_63584 21766102623722974005059 := by
  unfold tailWord_63584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159549500826751063878903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1546066001102334751838537 1159549500826751063878903)
  ·
    refine ⟨1739324251240126595818355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1159549500826751063878903 1739324251240126595818355)
    ·
      refine ⟨2608986376860189893727533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739324251240126595818355 2608986376860189893727533)
      ·
        refine ⟨978369891322571210147825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2608986376860189893727533 978369891322571210147825)
        ·
          refine ⟨733777418491928407610869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978369891322571210147825 733777418491928407610869)
          ·
            refine ⟨68791632983618288213519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 733777418491928407610869 68791632983618288213519)
            ·
              refine ⟨103187449475427432320279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68791632983618288213519 103187449475427432320279)
              ·
                refine ⟨154781174213141148480419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103187449475427432320279 154781174213141148480419)
                ·
                  refine ⟨232171761319711722720629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154781174213141148480419 232171761319711722720629)
                  ·
                    refine ⟨21766102623722974005059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 232171761319711722720629 21766102623722974005059)
                    ·
                      rfl

theorem cell22_63584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_63584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63584 prefixEnd_63584 := by exact prefixLift 63584
  have htrace : WordTrace (prefixWord ++ tailWord_63584) baseStart_63584 baseEnd_63584 := by
    simpa [prefixWord, tailWord_63584, baseEnd_63584] using wordTrace_append hprefix tailTrace_63584
  have hstable : (prefixWord ++ tailWord_63584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63584).length < 2 ^ (prefixWord ++ tailWord_63584).sum := by decide
  have hdescent : baseEnd_63584 < baseStart_63584 := by decide
  rcases family_descends (prefixWord ++ tailWord_63584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63597 : List Nat := [1, 5, 1, 1, 2, 1, 3, 8]
def baseStart_63597 : Nat := 118140960795 + 63597 * 2 ^ 59
def prefixEnd_63597 : Nat := 4983230072969 + 3 ^ 40 * 63597 * 2
def baseEnd_63597 : Nat := 2418950309932808158891

theorem tailTrace_63597 : CollatzResearch.WordTrace tailWord_63597 prefixEnd_63597 2418950309932808158891 := by
  unfold tailWord_63597
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319573150606405347981045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1546382100404270231987363 2319573150606405347981045)
  ·
    refine ⟨217459982869350501373223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2319573150606405347981045 217459982869350501373223)
    ·
      refine ⟨326189974304025752059835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217459982869350501373223 326189974304025752059835)
      ·
        refine ⟨489284961456038628089753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326189974304025752059835 489284961456038628089753)
        ·
          refine ⟨366963721092028971067315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489284961456038628089753 366963721092028971067315)
          ·
            refine ⟨550445581638043456600973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366963721092028971067315 550445581638043456600973)
            ·
              refine ⟨206417093114266296225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550445581638043456600973 206417093114266296225365)
              ·
                refine ⟨2418950309932808158891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 206417093114266296225365 2418950309932808158891)
                ·
                  rfl

theorem cell22_63597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 8].length) (baseStart_63597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63597 prefixEnd_63597 := by exact prefixLift 63597
  have htrace : WordTrace (prefixWord ++ tailWord_63597) baseStart_63597 baseEnd_63597 := by
    simpa [prefixWord, tailWord_63597, baseEnd_63597] using wordTrace_append hprefix tailTrace_63597
  have hstable : (prefixWord ++ tailWord_63597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63597).length < 2 ^ (prefixWord ++ tailWord_63597).sum := by decide
  have hdescent : baseEnd_63597 < baseStart_63597 := by decide
  rcases family_descends (prefixWord ++ tailWord_63597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63676 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_63676 : Nat := 118140960795 + 63676 * 2 ^ 59
def prefixEnd_63676 : Nat := 4983230072969 + 3 ^ 40 * 63676 * 2
def baseEnd_63676 : Nat := 7265865367955133568259

theorem tailTrace_63676 : CollatzResearch.WordTrace tailWord_63676 prefixEnd_63676 7265865367955133568259 := by
  unfold tailWord_63676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161227258660100920053441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1548303011546801226737921 1161227258660100920053441)
  ·
    refine ⟨870920443995075690040081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1161227258660100920053441 870920443995075690040081)
    ·
      refine ⟨653190332996306767530061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 870920443995075690040081 653190332996306767530061)
      ·
        refine ⟨244946374873615037823773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653190332996306767530061 244946374873615037823773)
        ·
          refine ⟨91854890577605639183915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244946374873615037823773 91854890577605639183915)
          ·
            refine ⟨137782335866408458775873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91854890577605639183915 137782335866408458775873)
            ·
              refine ⟨103336751899806344081905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137782335866408458775873 103336751899806344081905)
              ·
                refine ⟨77502563924854758061429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103336751899806344081905 77502563924854758061429)
                ·
                  refine ⟨7265865367955133568259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77502563924854758061429 7265865367955133568259)
                  ·
                    rfl

theorem cell22_63676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_63676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63676 prefixEnd_63676 := by exact prefixLift 63676
  have htrace : WordTrace (prefixWord ++ tailWord_63676) baseStart_63676 baseEnd_63676 := by
    simpa [prefixWord, tailWord_63676, baseEnd_63676] using wordTrace_append hprefix tailTrace_63676
  have hstable : (prefixWord ++ tailWord_63676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63676).length < 2 ^ (prefixWord ++ tailWord_63676).sum := by decide
  have hdescent : baseEnd_63676 < baseStart_63676 := by decide
  rcases family_descends (prefixWord ++ tailWord_63676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63680 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 1, 3]
def baseStart_63680 : Nat := 118140960795 + 63680 * 2 ^ 59
def prefixEnd_63680 : Nat := 4983230072969 + 3 ^ 40 * 63680 * 2
def baseEnd_63680 : Nat := 21798965385610723604765

theorem tailTrace_63680 : CollatzResearch.WordTrace tailWord_63680 prefixEnd_63680 21798965385610723604765 := by
  unfold tailWord_63680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161300204652855261626247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1548400272870473682168329 1161300204652855261626247)
  ·
    refine ⟨1741950306979282892439371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161300204652855261626247 1741950306979282892439371)
    ·
      refine ⟨2612925460468924338659057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1741950306979282892439371 2612925460468924338659057)
      ·
        refine ⟨1959694095351693253994293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2612925460468924338659057 1959694095351693253994293)
        ·
          refine ⟨183721321439221242561965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1959694095351693253994293 183721321439221242561965)
          ·
            refine ⟨68895495539707965960737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183721321439221242561965 68895495539707965960737)
            ·
              refine ⟨51671621654780974470553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68895495539707965960737 51671621654780974470553)
              ·
                refine ⟨38753716241085730852915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51671621654780974470553 38753716241085730852915)
                ·
                  refine ⟨58130574361628596279373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38753716241085730852915 58130574361628596279373)
                  ·
                    refine ⟨21798965385610723604765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58130574361628596279373 21798965385610723604765)
                    ·
                      rfl

theorem cell22_63680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_63680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63680 prefixEnd_63680 := by exact prefixLift 63680
  have htrace : WordTrace (prefixWord ++ tailWord_63680) baseStart_63680 baseEnd_63680 := by
    simpa [prefixWord, tailWord_63680, baseEnd_63680] using wordTrace_append hprefix tailTrace_63680
  have hstable : (prefixWord ++ tailWord_63680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63680).length < 2 ^ (prefixWord ++ tailWord_63680).sum := by decide
  have hdescent : baseEnd_63680 < baseStart_63680 := by decide
  rcases family_descends (prefixWord ++ tailWord_63680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63704 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_63704 : Nat := 118140960795 + 63704 * 2 ^ 59
def prefixEnd_63704 : Nat := 4983230072969 + 3 ^ 40 * 63704 * 2
def baseEnd_63704 : Nat := 7269060358694220334897

theorem tailTrace_63704 : CollatzResearch.WordTrace tailWord_63704 prefixEnd_63704 7269060358694220334897 := by
  unfold tailWord_63704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161737880609381311063083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1548983840812508414750777 1161737880609381311063083)
  ·
    refine ⟨1742606820914071966594625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161737880609381311063083 1742606820914071966594625)
    ·
      refine ⟨1306955115685553974945969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1742606820914071966594625 1306955115685553974945969)
      ·
        refine ⟨980216336764165481209477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306955115685553974945969 980216336764165481209477)
        ·
          refine ⟨183790563143281027726777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 980216336764165481209477 183790563143281027726777)
          ·
            refine ⟨137842922357460770795083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183790563143281027726777 137842922357460770795083)
            ·
              refine ⟨206764383536191156192625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137842922357460770795083 206764383536191156192625)
              ·
                refine ⟨155073287652143367144469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206764383536191156192625 155073287652143367144469)
                ·
                  refine ⟨7269060358694220334897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155073287652143367144469 7269060358694220334897)
                  ·
                    rfl

theorem cell22_63704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_63704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63704 prefixEnd_63704 := by exact prefixLift 63704
  have htrace : WordTrace (prefixWord ++ tailWord_63704) baseStart_63704 baseEnd_63704 := by
    simpa [prefixWord, tailWord_63704, baseEnd_63704] using wordTrace_append hprefix tailTrace_63704
  have hstable : (prefixWord ++ tailWord_63704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63704).length < 2 ^ (prefixWord ++ tailWord_63704).sum := by decide
  have hdescent : baseEnd_63704 < baseStart_63704 := by decide
  rcases family_descends (prefixWord ++ tailWord_63704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63714 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_63714 : Nat := 118140960795 + 63714 * 2 ^ 59
def prefixEnd_63714 : Nat := 4983230072969 + 3 ^ 40 * 63714 * 2
def baseEnd_63714 : Nat := 21810604280445968254661

theorem tailTrace_63714 : CollatzResearch.WordTrace tailWord_63714 prefixEnd_63714 21810604280445968254661 := by
  unfold tailWord_63714
  simp only [CollatzResearch.WordTrace]
  refine ⟨580960122795633582497549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1549226994121689553326797 580960122795633582497549)
  ·
    refine ⟨217860046048362593436581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 580960122795633582497549 217860046048362593436581)
    ·
      refine ⟨40848758634067986269359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217860046048362593436581 40848758634067986269359)
      ·
        refine ⟨61273137951101979404039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40848758634067986269359 61273137951101979404039)
        ·
          refine ⟨91909706926652969106059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61273137951101979404039 91909706926652969106059)
          ·
            refine ⟨137864560389979453659089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91909706926652969106059 137864560389979453659089)
            ·
              refine ⟨103398420292484590244317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137864560389979453659089 103398420292484590244317)
              ·
                refine ⟨38774407609681721341619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103398420292484590244317 38774407609681721341619)
                ·
                  refine ⟨58161611414522582012429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38774407609681721341619 58161611414522582012429)
                  ·
                    refine ⟨21810604280445968254661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58161611414522582012429 21810604280445968254661)
                    ·
                      rfl

theorem cell22_63714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_63714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63714 prefixEnd_63714 := by exact prefixLift 63714
  have htrace : WordTrace (prefixWord ++ tailWord_63714) baseStart_63714 baseEnd_63714 := by
    simpa [prefixWord, tailWord_63714, baseEnd_63714] using wordTrace_append hprefix tailTrace_63714
  have hstable : (prefixWord ++ tailWord_63714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63714).length < 2 ^ (prefixWord ++ tailWord_63714).sum := by decide
  have hdescent : baseEnd_63714 < baseStart_63714 := by decide
  rcases family_descends (prefixWord ++ tailWord_63714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63753 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 2, 3]
def baseStart_63753 : Nat := 118140960795 + 63753 * 2 ^ 59
def prefixEnd_63753 : Nat := 4983230072969 + 3 ^ 40 * 63753 * 2
def baseEnd_63753 : Nat := 21823954777462866529541

theorem tailTrace_63753 : CollatzResearch.WordTrace tailWord_63753 prefixEnd_63753 21823954777462866529541 := by
  unfold tailWord_63753
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325262938041243990659913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1550175292027495993773275 2325262938041243990659913)
  ·
    refine ⟨1743947203530932992994935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2325262938041243990659913 1743947203530932992994935)
    ·
      refine ⟨2615920805296399489492403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743947203530932992994935 2615920805296399489492403)
      ·
        refine ⟨3923881207944599234238605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615920805296399489492403 3923881207944599234238605)
        ·
          refine ⟨1471455452979224712839477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3923881207944599234238605 1471455452979224712839477)
          ·
            refine ⟨137948948716802316828701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1471455452979224712839477 137948948716802316828701)
            ·
              refine ⟨51730855768800868810763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137948948716802316828701 51730855768800868810763)
              ·
                refine ⟨77596283653201303216145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51730855768800868810763 77596283653201303216145)
                ·
                  refine ⟨58197212739900977412109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77596283653201303216145 58197212739900977412109)
                  ·
                    refine ⟨21823954777462866529541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58197212739900977412109 21823954777462866529541)
                    ·
                      rfl

theorem cell22_63753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_63753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63753 prefixEnd_63753 := by exact prefixLift 63753
  have htrace : WordTrace (prefixWord ++ tailWord_63753) baseStart_63753 baseEnd_63753 := by
    simpa [prefixWord, tailWord_63753, baseEnd_63753] using wordTrace_append hprefix tailTrace_63753
  have hstable : (prefixWord ++ tailWord_63753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63753).length < 2 ^ (prefixWord ++ tailWord_63753).sum := by decide
  have hdescent : baseEnd_63753 < baseStart_63753 := by decide
  rcases family_descends (prefixWord ++ tailWord_63753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63811 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 5]
def baseStart_63811 : Nat := 118140960795 + 63811 * 2 ^ 59
def prefixEnd_63811 : Nat := 4983230072969 + 3 ^ 40 * 63811 * 2
def baseEnd_63811 : Nat := 7281269787590016193121

theorem tailTrace_63811 : CollatzResearch.WordTrace tailWord_63811 prefixEnd_63811 7281269787590016193121 := by
  unfold tailWord_63811
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327378371831119896271287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1551585581220746597514191 2327378371831119896271287)
  ·
    refine ⟨3491067557746679844406931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2327378371831119896271287 3491067557746679844406931)
    ·
      refine ⟨5236601336620019766610397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491067557746679844406931 5236601336620019766610397)
      ·
        refine ⟨1963725501232507412478899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5236601336620019766610397 1963725501232507412478899)
        ·
          refine ⟨2945588251848761118718349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963725501232507412478899 2945588251848761118718349)
          ·
            refine ⟨1104595594443285419519381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2945588251848761118718349 1104595594443285419519381)
            ·
              refine ⟨51777918489529004039971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1104595594443285419519381 51777918489529004039971)
              ·
                refine ⟨77666877734293506059957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51777918489529004039971 77666877734293506059957)
                ·
                  refine ⟨7281269787590016193121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77666877734293506059957 7281269787590016193121)
                  ·
                    rfl

theorem cell22_63811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 5].length) (baseStart_63811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63811 prefixEnd_63811 := by exact prefixLift 63811
  have htrace : WordTrace (prefixWord ++ tailWord_63811) baseStart_63811 baseEnd_63811 := by
    simpa [prefixWord, tailWord_63811, baseEnd_63811] using wordTrace_append hprefix tailTrace_63811
  have hstable : (prefixWord ++ tailWord_63811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63811).length < 2 ^ (prefixWord ++ tailWord_63811).sum := by decide
  have hdescent : baseEnd_63811 < baseStart_63811 := by decide
  rcases family_descends (prefixWord ++ tailWord_63811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63892 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_63892 : Nat := 118140960795 + 63892 * 2 ^ 59
def prefixEnd_63892 : Nat := 4983230072969 + 3 ^ 40 * 63892 * 2
def baseEnd_63892 : Nat := 21871537318112837304115

theorem tailTrace_63892 : CollatzResearch.WordTrace tailWord_63892 prefixEnd_63892 21871537318112837304115 := by
  unfold tailWord_63892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1165166342268835364984965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1553555123025113819979953 1165166342268835364984965)
  ·
    refine ⟨218468689175406630934681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1165166342268835364984965 218468689175406630934681)
    ·
      refine ⟨163851516881554973201011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218468689175406630934681 163851516881554973201011)
      ·
        refine ⟨245777275322332459801517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163851516881554973201011 245777275322332459801517)
        ·
          refine ⟨92166478245874672425569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245777275322332459801517 92166478245874672425569)
          ·
            refine ⟨69124858684406004319177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92166478245874672425569 69124858684406004319177)
            ·
              refine ⟨51843644013304503239383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69124858684406004319177 51843644013304503239383)
              ·
                refine ⟨77765466019956754859075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51843644013304503239383 77765466019956754859075)
                ·
                  refine ⟨116648199029935132288613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77765466019956754859075 116648199029935132288613)
                  ·
                    refine ⟨21871537318112837304115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116648199029935132288613 21871537318112837304115)
                    ·
                      rfl

theorem cell22_63892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_63892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63892 prefixEnd_63892 := by exact prefixLift 63892
  have htrace : WordTrace (prefixWord ++ tailWord_63892) baseStart_63892 baseEnd_63892 := by
    simpa [prefixWord, tailWord_63892, baseEnd_63892] using wordTrace_append hprefix tailTrace_63892
  have hstable : (prefixWord ++ tailWord_63892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63892).length < 2 ^ (prefixWord ++ tailWord_63892).sum := by decide
  have hdescent : baseEnd_63892 < baseStart_63892 := by decide
  rcases family_descends (prefixWord ++ tailWord_63892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63901 : List Nat := [1, 4, 2, 1, 4, 1, 9]
def baseStart_63901 : Nat := 118140960795 + 63901 * 2 ^ 59
def prefixEnd_63901 : Nat := 4983230072969 + 3 ^ 40 * 63901 * 2
def baseEnd_63901 : Nat := 810171044519993104781

theorem tailTrace_63901 : CollatzResearch.WordTrace tailWord_63901 prefixEnd_63901 810171044519993104781 := by
  unfold tailWord_63901
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330660941505065267047557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1553773961003376844698371 2330660941505065267047557)
  ·
    refine ⟨436998926532199737571417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2330660941505065267047557 436998926532199737571417)
    ·
      refine ⟨327749194899149803178563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436998926532199737571417 327749194899149803178563)
      ·
        refine ⟨491623792348724704767845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327749194899149803178563 491623792348724704767845)
        ·
          refine ⟨92179461065385882143971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 491623792348724704767845 92179461065385882143971)
          ·
            refine ⟨138269191598078823215957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92179461065385882143971 138269191598078823215957)
            ·
              refine ⟨810171044519993104781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 138269191598078823215957 810171044519993104781)
              ·
                rfl

theorem cell22_63901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 9].length) (baseStart_63901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63901 prefixEnd_63901 := by exact prefixLift 63901
  have htrace : WordTrace (prefixWord ++ tailWord_63901) baseStart_63901 baseEnd_63901 := by
    simpa [prefixWord, tailWord_63901, baseEnd_63901] using wordTrace_append hprefix tailTrace_63901
  have hstable : (prefixWord ++ tailWord_63901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63901).length < 2 ^ (prefixWord ++ tailWord_63901).sum := by decide
  have hdescent : baseEnd_63901 < baseStart_63901 := by decide
  rcases family_descends (prefixWord ++ tailWord_63901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63905 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_63905 : Nat := 118140960795 + 63905 * 2 ^ 59
def prefixEnd_63905 : Nat := 4983230072969 + 3 ^ 40 * 63905 * 2
def baseEnd_63905 : Nat := 21875987483785136729075

theorem tailTrace_63905 : CollatzResearch.WordTrace tailWord_63905 prefixEnd_63905 21875987483785136729075 := by
  unfold tailWord_63905
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330806833490573950193169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1553871222327049300128779 2330806833490573950193169)
  ·
    refine ⟨1748105125117930462644877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2330806833490573950193169 1748105125117930462644877)
    ·
      refine ⟨655539421919223923491829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1748105125117930462644877 655539421919223923491829)
      ·
        refine ⟨61456820804927242827359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 655539421919223923491829 61456820804927242827359)
        ·
          refine ⟨92185231207390864241039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61456820804927242827359 92185231207390864241039)
          ·
            refine ⟨138277846811086296361559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92185231207390864241039 138277846811086296361559)
            ·
              refine ⟨207416770216629444542339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138277846811086296361559 207416770216629444542339)
              ·
                refine ⟨311125155324944166813509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207416770216629444542339 311125155324944166813509)
                ·
                  refine ⟨58335966623427031277533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311125155324944166813509 58335966623427031277533)
                  ·
                    refine ⟨21875987483785136729075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58335966623427031277533 21875987483785136729075)
                    ·
                      rfl

theorem cell22_63905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_63905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63905 prefixEnd_63905 := by exact prefixLift 63905
  have htrace : WordTrace (prefixWord ++ tailWord_63905) baseStart_63905 baseEnd_63905 := by
    simpa [prefixWord, tailWord_63905, baseEnd_63905] using wordTrace_append hprefix tailTrace_63905
  have hstable : (prefixWord ++ tailWord_63905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63905).length < 2 ^ (prefixWord ++ tailWord_63905).sum := by decide
  have hdescent : baseEnd_63905 < baseStart_63905 := by decide
  rcases family_descends (prefixWord ++ tailWord_63905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63933 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_63933 : Nat := 118140960795 + 63933 * 2 ^ 59
def prefixEnd_63933 : Nat := 4983230072969 + 3 ^ 40 * 63933 * 2
def baseEnd_63933 : Nat := 21885572456002397028989

theorem tailTrace_63933 : CollatzResearch.WordTrace tailWord_63933 prefixEnd_63933 21885572456002397028989 := by
  unfold tailWord_63933
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331828077389134732212453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1554552051592756488141635 2331828077389134732212453)
  ·
    refine ⟨437217764510462762289835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2331828077389134732212453 437217764510462762289835)
    ·
      refine ⟨655826646765694143434753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437217764510462762289835 655826646765694143434753)
      ·
        refine ⟨491869985074270607576065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 655826646765694143434753 491869985074270607576065)
        ·
          refine ⟨368902488805702955682049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491869985074270607576065 368902488805702955682049)
          ·
            refine ⟨276676866604277216761537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368902488805702955682049 276676866604277216761537)
            ·
              refine ⟨207507649953207912571153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276676866604277216761537 207507649953207912571153)
              ·
                refine ⟨155630737464905934428365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207507649953207912571153 155630737464905934428365)
                ·
                  refine ⟨58361526549339725410637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155630737464905934428365 58361526549339725410637)
                  ·
                    refine ⟨21885572456002397028989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58361526549339725410637 21885572456002397028989)
                    ·
                      rfl

theorem cell22_63933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_63933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63933 prefixEnd_63933 := by exact prefixLift 63933
  have htrace : WordTrace (prefixWord ++ tailWord_63933) baseStart_63933 baseEnd_63933 := by
    simpa [prefixWord, tailWord_63933, baseEnd_63933] using wordTrace_append hprefix tailTrace_63933
  have hstable : (prefixWord ++ tailWord_63933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63933).length < 2 ^ (prefixWord ++ tailWord_63933).sum := by decide
  have hdescent : baseEnd_63933 < baseStart_63933 := by decide
  rcases family_descends (prefixWord ++ tailWord_63933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63967 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 1, 3]
def baseStart_63967 : Nat := 118140960795 + 63967 * 2 ^ 59
def prefixEnd_63967 : Nat := 4983230072969 + 3 ^ 40 * 63967 * 2
def baseEnd_63967 : Nat := 21897211350837641678885

theorem tailTrace_63967 : CollatzResearch.WordTrace tailWord_63967 prefixEnd_63967 21897211350837641678885 := by
  unfold tailWord_63967
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333068159265958538950155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1555378772843972359300103 2333068159265958538950155)
  ·
    refine ⟨3499602238898937808425233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333068159265958538950155 3499602238898937808425233)
    ·
      refine ⟨2624701679174203356318925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499602238898937808425233 2624701679174203356318925)
      ·
        refine ⟨984263129690326258619597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2624701679174203356318925 984263129690326258619597)
        ·
          refine ⟨369098673633872346982349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 984263129690326258619597 369098673633872346982349)
          ·
            refine ⟨138412002612702130118381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369098673633872346982349 138412002612702130118381)
            ·
              refine ⟨51904500979763298794393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138412002612702130118381 51904500979763298794393)
              ·
                refine ⟨38928375734822474095795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51904500979763298794393 38928375734822474095795)
                ·
                  refine ⟨58392563602233711143693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38928375734822474095795 58392563602233711143693)
                  ·
                    refine ⟨21897211350837641678885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58392563602233711143693 21897211350837641678885)
                    ·
                      rfl

theorem cell22_63967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_63967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63967 prefixEnd_63967 := by exact prefixLift 63967
  have htrace : WordTrace (prefixWord ++ tailWord_63967) baseStart_63967 baseEnd_63967 := by
    simpa [prefixWord, tailWord_63967, baseEnd_63967] using wordTrace_append hprefix tailTrace_63967
  have hstable : (prefixWord ++ tailWord_63967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63967).length < 2 ^ (prefixWord ++ tailWord_63967).sum := by decide
  have hdescent : baseEnd_63967 < baseStart_63967 := by decide
  rcases family_descends (prefixWord ++ tailWord_63967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63993 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_63993 : Nat := 118140960795 + 63993 * 2 ^ 59
def prefixEnd_63993 : Nat := 4983230072969 + 3 ^ 40 * 63993 * 2
def baseEnd_63993 : Nat := 21906111682182240528805

theorem tailTrace_63993 : CollatzResearch.WordTrace tailWord_63993 prefixEnd_63993 21906111682182240528805 := by
  unfold tailWord_63993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334016457171764979396633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1556010971447843319597755 2334016457171764979396633)
  ·
    refine ⟨1750512342878823734547475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2334016457171764979396633 1750512342878823734547475)
    ·
      refine ⟨2625768514318235601821213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750512342878823734547475 2625768514318235601821213)
      ·
        refine ⟨984663192869338350682955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2625768514318235601821213 984663192869338350682955)
        ·
          refine ⟨1476994789304007526024433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984663192869338350682955 1476994789304007526024433)
          ·
            refine ⟨1107746091978005644518325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1476994789304007526024433 1107746091978005644518325)
            ·
              refine ⟨103851196122938029173593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1107746091978005644518325 103851196122938029173593)
              ·
                refine ⟨77888397092203521880195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103851196122938029173593 77888397092203521880195)
                ·
                  refine ⟨116832595638305282820293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77888397092203521880195 116832595638305282820293)
                  ·
                    refine ⟨21906111682182240528805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116832595638305282820293 21906111682182240528805)
                    ·
                      rfl

theorem cell22_63993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_63993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_63993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_63993 prefixEnd_63993 := by exact prefixLift 63993
  have htrace : WordTrace (prefixWord ++ tailWord_63993) baseStart_63993 baseEnd_63993 := by
    simpa [prefixWord, tailWord_63993, baseEnd_63993] using wordTrace_append hprefix tailTrace_63993
  have hstable : (prefixWord ++ tailWord_63993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63993).length < 2 ^ (prefixWord ++ tailWord_63993).sum := by decide
  have hdescent : baseEnd_63993 < baseStart_63993 := by decide
  rcases family_descends (prefixWord ++ tailWord_63993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64008 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 4]
def baseStart_64008 : Nat := 118140960795 + 64008 * 2 ^ 59
def prefixEnd_64008 : Nat := 4983230072969 + 3 ^ 40 * 64008 * 2
def baseEnd_64008 : Nat := 7303748829575733801253

theorem tailTrace_64008 : CollatzResearch.WordTrace tailWord_64008 prefixEnd_64008 7303748829575733801253 := by
  unfold tailWord_64008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167281776058711270596339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1556375701411615027461785 1167281776058711270596339)
  ·
    refine ⟨1750922664088066905894509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1167281776058711270596339 1750922664088066905894509)
    ·
      refine ⟨656595999033025089710441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1750922664088066905894509 656595999033025089710441)
      ·
        refine ⟨492446999274768817282831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656595999033025089710441 492446999274768817282831)
        ·
          refine ⟨738670498912153225924247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492446999274768817282831 738670498912153225924247)
          ·
            refine ⟨1108005748368229838886371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738670498912153225924247 1108005748368229838886371)
            ·
              refine ⟨1662008622552344758329557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108005748368229838886371 1662008622552344758329557)
              ·
                refine ⟨38953327091070580273349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1662008622552344758329557 38953327091070580273349)
                ·
                  refine ⟨7303748829575733801253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38953327091070580273349 7303748829575733801253)
                  ·
                    rfl

theorem cell22_64008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_64008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64008 prefixEnd_64008 := by exact prefixLift 64008
  have htrace : WordTrace (prefixWord ++ tailWord_64008) baseStart_64008 baseEnd_64008 := by
    simpa [prefixWord, tailWord_64008, baseEnd_64008] using wordTrace_append hprefix tailTrace_64008
  have hstable : (prefixWord ++ tailWord_64008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64008).length < 2 ^ (prefixWord ++ tailWord_64008).sum := by decide
  have hdescent : baseEnd_64008 < baseStart_64008 := by decide
  rcases family_descends (prefixWord ++ tailWord_64008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64010 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_64010 : Nat := 118140960795 + 64010 * 2 ^ 59
def prefixEnd_64010 : Nat := 4983230072969 + 3 ^ 40 * 64010 * 2
def baseEnd_64010 : Nat := 21911931129599862853753

theorem tailTrace_64010 : CollatzResearch.WordTrace tailWord_64010 prefixEnd_64010 21911931129599862853753 := by
  unfold tailWord_64010
  simp only [CollatzResearch.WordTrace]
  refine ⟨583659124527544220691371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1556424332073451255176989 583659124527544220691371)
  ·
    refine ⟨875488686791316331037057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583659124527544220691371 875488686791316331037057)
    ·
      refine ⟨656616515093487248277793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 875488686791316331037057 656616515093487248277793)
      ·
        refine ⟨492462386320115436208345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656616515093487248277793 492462386320115436208345)
        ·
          refine ⟨369346789740086577156259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492462386320115436208345 369346789740086577156259)
          ·
            refine ⟨554020184610129865734389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369346789740086577156259 554020184610129865734389)
            ·
              refine ⟨51939392307199674912599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 554020184610129865734389 51939392307199674912599)
              ·
                refine ⟨77909088460799512368899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51939392307199674912599 77909088460799512368899)
                ·
                  refine ⟨116863632691199268553349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77909088460799512368899 116863632691199268553349)
                  ·
                    refine ⟨21911931129599862853753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116863632691199268553349 21911931129599862853753)
                    ·
                      rfl

theorem cell22_64010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_64010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64010 prefixEnd_64010 := by exact prefixLift 64010
  have htrace : WordTrace (prefixWord ++ tailWord_64010) baseStart_64010 baseEnd_64010 := by
    simpa [prefixWord, tailWord_64010, baseEnd_64010] using wordTrace_append hprefix tailTrace_64010
  have hstable : (prefixWord ++ tailWord_64010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64010).length < 2 ^ (prefixWord ++ tailWord_64010).sum := by decide
  have hdescent : baseEnd_64010 < baseStart_64010 := by decide
  rcases family_descends (prefixWord ++ tailWord_64010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64040 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_64040 : Nat := 118140960795 + 64040 * 2 ^ 59
def prefixEnd_64040 : Nat := 4983230072969 + 3 ^ 40 * 64040 * 2
def baseEnd_64040 : Nat := 21922200742689784603661

theorem tailTrace_64040 : CollatzResearch.WordTrace tailWord_64040 prefixEnd_64040 21922200742689784603661 := by
  unfold tailWord_64040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167865344000746003178787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1557153792000994670905049 1167865344000746003178787)
  ·
    refine ⟨1751798016001119004768181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1167865344000746003178787 1751798016001119004768181)
    ·
      refine ⟨164231064000104906697017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1751798016001119004768181 164231064000104906697017)
      ·
        refine ⟨123173298000078680022763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164231064000104906697017 123173298000078680022763)
        ·
          refine ⟨184759947000118020034145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123173298000078680022763 184759947000118020034145)
          ·
            refine ⟨138569960250088515025609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184759947000118020034145 138569960250088515025609)
            ·
              refine ⟨103927470187566386269207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138569960250088515025609 103927470187566386269207)
              ·
                refine ⟨155891205281349579403811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103927470187566386269207 155891205281349579403811)
                ·
                  refine ⟨233836807922024369105717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155891205281349579403811 233836807922024369105717)
                  ·
                    refine ⟨21922200742689784603661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233836807922024369105717 21922200742689784603661)
                    ·
                      rfl

theorem cell22_64040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_64040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64040 prefixEnd_64040 := by exact prefixLift 64040
  have htrace : WordTrace (prefixWord ++ tailWord_64040) baseStart_64040 baseEnd_64040 := by
    simpa [prefixWord, tailWord_64040, baseEnd_64040] using wordTrace_append hprefix tailTrace_64040
  have hstable : (prefixWord ++ tailWord_64040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64040).length < 2 ^ (prefixWord ++ tailWord_64040).sum := by decide
  have hdescent : baseEnd_64040 < baseStart_64040 := by decide
  rcases family_descends (prefixWord ++ tailWord_64040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64053 : List Nat := [1, 3, 3, 1, 1, 2, 5, 6]
def baseStart_64053 : Nat := 118140960795 + 64053 * 2 ^ 59
def prefixEnd_64053 : Nat := 4983230072969 + 3 ^ 40 * 64053 * 2
def baseEnd_64053 : Nat := 2436294545373564892069

theorem tailTrace_64053 : CollatzResearch.WordTrace tailWord_64053 prefixEnd_64053 2436294545373564892069 := by
  unfold tailWord_64053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2336204836954395226580813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1557469891302930151053875 2336204836954395226580813)
  ·
    refine ⟨876076813857898209967805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2336204836954395226580813 876076813857898209967805)
    ·
      refine ⟨328528805196711828737927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 876076813857898209967805 328528805196711828737927)
      ·
        refine ⟨492793207795067743106891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328528805196711828737927 492793207795067743106891)
        ·
          refine ⟨739189811692601614660337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492793207795067743106891 739189811692601614660337)
          ·
            refine ⟨554392358769451210995253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739189811692601614660337 554392358769451210995253)
            ·
              refine ⟨51974283634636051030805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 554392358769451210995253 51974283634636051030805)
              ·
                refine ⟨2436294545373564892069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51974283634636051030805 2436294545373564892069)
                ·
                  rfl

theorem cell22_64053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 6].length) (baseStart_64053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64053 prefixEnd_64053 := by exact prefixLift 64053
  have htrace : WordTrace (prefixWord ++ tailWord_64053) baseStart_64053 baseEnd_64053 := by
    simpa [prefixWord, tailWord_64053, baseEnd_64053] using wordTrace_append hprefix tailTrace_64053
  have hstable : (prefixWord ++ tailWord_64053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64053).length < 2 ^ (prefixWord ++ tailWord_64053).sum := by decide
  have hdescent : baseEnd_64053 < baseStart_64053 := by decide
  rcases family_descends (prefixWord ++ tailWord_64053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64070 : List Nat := [6, 1, 1, 1, 2, 2, 9]
def baseStart_64070 : Nat := 118140960795 + 64070 * 2 ^ 59
def prefixEnd_64070 : Nat := 4983230072969 + 3 ^ 40 * 64070 * 2
def baseEnd_64070 : Nat := 812313716880729864947

theorem tailTrace_64070 : CollatzResearch.WordTrace tailWord_64070 prefixEnd_64070 812313716880729864947 := by
  unfold tailWord_64070
  simp only [CollatzResearch.WordTrace]
  refine ⟨73025777434150222810927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1557883251928538086633109 73025777434150222810927)
  ·
    refine ⟨109538666151225334216391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73025777434150222810927 109538666151225334216391)
    ·
      refine ⟨164307999226838001324587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109538666151225334216391 164307999226838001324587)
      ·
        refine ⟨246461998840257001986881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164307999226838001324587 246461998840257001986881)
        ·
          refine ⟨184846499130192751490161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246461998840257001986881 184846499130192751490161)
          ·
            refine ⟨138634874347644563617621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184846499130192751490161 138634874347644563617621)
            ·
              refine ⟨812313716880729864947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 138634874347644563617621 812313716880729864947)
              ·
                rfl

theorem cell22_64070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 9].length) (baseStart_64070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64070 prefixEnd_64070 := by exact prefixLift 64070
  have htrace : WordTrace (prefixWord ++ tailWord_64070) baseStart_64070 baseEnd_64070 := by
    simpa [prefixWord, tailWord_64070, baseEnd_64070] using wordTrace_append hprefix tailTrace_64070
  have hstable : (prefixWord ++ tailWord_64070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64070).length < 2 ^ (prefixWord ++ tailWord_64070).sum := by decide
  have hdescent : baseEnd_64070 < baseStart_64070 := by decide
  rcases family_descends (prefixWord ++ tailWord_64070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64190 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_64190 : Nat := 118140960795 + 64190 * 2 ^ 59
def prefixEnd_64190 : Nat := 4983230072969 + 3 ^ 40 * 64190 * 2
def baseEnd_64190 : Nat := 21973548808139393353201

theorem tailTrace_64190 : CollatzResearch.WordTrace tailWord_64190 prefixEnd_64190 21973548808139393353201 := by
  unfold tailWord_64190
  simp only [CollatzResearch.WordTrace]
  refine ⟨292650204682258453039753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1560801091638711749545349 292650204682258453039753)
  ·
    refine ⟨219487653511693839779815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292650204682258453039753 219487653511693839779815)
    ·
      refine ⟨329231480267540759669723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219487653511693839779815 329231480267540759669723)
      ·
        refine ⟨493847220401311139504585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329231480267540759669723 493847220401311139504585)
        ·
          refine ⟨370385415300983354628439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 493847220401311139504585 370385415300983354628439)
          ·
            refine ⟨555578122951475031942659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370385415300983354628439 555578122951475031942659)
            ·
              refine ⟨833367184427212547913989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555578122951475031942659 833367184427212547913989)
              ·
                refine ⟨156256347080102352733873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 833367184427212547913989 156256347080102352733873)
                ·
                  refine ⟨117192260310076764550405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156256347080102352733873 117192260310076764550405)
                  ·
                    refine ⟨21973548808139393353201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117192260310076764550405 21973548808139393353201)
                    ·
                      rfl

theorem cell22_64190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_64190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64190 prefixEnd_64190 := by exact prefixLift 64190
  have htrace : WordTrace (prefixWord ++ tailWord_64190) baseStart_64190 baseEnd_64190 := by
    simpa [prefixWord, tailWord_64190, baseEnd_64190] using wordTrace_append hprefix tailTrace_64190
  have hstable : (prefixWord ++ tailWord_64190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64190).length < 2 ^ (prefixWord ++ tailWord_64190).sum := by decide
  have hdescent : baseEnd_64190 < baseStart_64190 := by decide
  rcases family_descends (prefixWord ++ tailWord_64190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64192 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_64192 : Nat := 118140960795 + 64192 * 2 ^ 59
def prefixEnd_64192 : Nat := 4983230072969 + 3 ^ 40 * 64192 * 2
def baseEnd_64192 : Nat := 21974233449012054803195

theorem tailTrace_64192 : CollatzResearch.WordTrace tailWord_64192 prefixEnd_64192 21974233449012054803195 := by
  unfold tailWord_64192
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170637291725410982945415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1560849722300547977260553 1170637291725410982945415)
  ·
    refine ⟨1755955937588116474418123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1170637291725410982945415 1755955937588116474418123)
    ·
      refine ⟨2633933906382174711627185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755955937588116474418123 2633933906382174711627185)
      ·
        refine ⟨1975450429786631033720389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2633933906382174711627185 1975450429786631033720389)
        ·
          refine ⟨370396955584993318822573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1975450429786631033720389 370396955584993318822573)
          ·
            refine ⟨138898858344372494558465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370396955584993318822573 138898858344372494558465)
            ·
              refine ⟨104174143758279370918849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138898858344372494558465 104174143758279370918849)
              ·
                refine ⟨78130607818709528189137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104174143758279370918849 78130607818709528189137)
                ·
                  refine ⟨58597955864032146141853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78130607818709528189137 58597955864032146141853)
                  ·
                    refine ⟨21974233449012054803195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58597955864032146141853 21974233449012054803195)
                    ·
                      rfl

theorem cell22_64192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_64192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64192 prefixEnd_64192 := by exact prefixLift 64192
  have htrace : WordTrace (prefixWord ++ tailWord_64192) baseStart_64192 baseEnd_64192 := by
    simpa [prefixWord, tailWord_64192, baseEnd_64192] using wordTrace_append hprefix tailTrace_64192
  have hstable : (prefixWord ++ tailWord_64192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64192).length < 2 ^ (prefixWord ++ tailWord_64192).sum := by decide
  have hdescent : baseEnd_64192 < baseStart_64192 := by decide
  rcases family_descends (prefixWord ++ tailWord_64192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64218 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_64218 : Nat := 118140960795 + 64218 * 2 ^ 59
def prefixEnd_64218 : Nat := 4983230072969 + 3 ^ 40 * 64218 * 2
def baseEnd_64218 : Nat := 21983133780356653653115

theorem tailTrace_64218 : CollatzResearch.WordTrace tailWord_64218 prefixEnd_64218 21983133780356653653115 := by
  unfold tailWord_64218
  simp only [CollatzResearch.WordTrace]
  refine ⟨585555720339157101584327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1561481920904418937558205 585555720339157101584327)
  ·
    refine ⟨878333580508735652376491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585555720339157101584327 878333580508735652376491)
    ·
      refine ⟨1317500370763103478564737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878333580508735652376491 1317500370763103478564737)
      ·
        refine ⟨988125278072327608923553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1317500370763103478564737 988125278072327608923553)
        ·
          refine ⟨741093958554245706692665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988125278072327608923553 741093958554245706692665)
          ·
            refine ⟨555820468915684280019499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741093958554245706692665 555820468915684280019499)
            ·
              refine ⟨833730703373526420029249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555820468915684280019499 833730703373526420029249)
              ·
                refine ⟨625298027530144815021937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 833730703373526420029249 625298027530144815021937)
                ·
                  refine ⟨468973520647608611266453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625298027530144815021937 468973520647608611266453)
                  ·
                    refine ⟨21983133780356653653115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 468973520647608611266453 21983133780356653653115)
                    ·
                      rfl

theorem cell22_64218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_64218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64218 prefixEnd_64218 := by exact prefixLift 64218
  have htrace : WordTrace (prefixWord ++ tailWord_64218) baseStart_64218 baseEnd_64218 := by
    simpa [prefixWord, tailWord_64218, baseEnd_64218] using wordTrace_append hprefix tailTrace_64218
  have hstable : (prefixWord ++ tailWord_64218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64218).length < 2 ^ (prefixWord ++ tailWord_64218).sum := by decide
  have hdescent : baseEnd_64218 < baseStart_64218 := by decide
  rcases family_descends (prefixWord ++ tailWord_64218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64248 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_64248 : Nat := 118140960795 + 64248 * 2 ^ 59
def prefixEnd_64248 : Nat := 4983230072969 + 3 ^ 40 * 64248 * 2
def baseEnd_64248 : Nat := 21993403393446575403023

theorem tailTrace_64248 : CollatzResearch.WordTrace tailWord_64248 prefixEnd_64248 21993403393446575403023 := by
  unfold tailWord_64248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171658535623971764964699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1562211380831962353286265 1171658535623971764964699)
  ·
    refine ⟨1757487803435957647447049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171658535623971764964699 1757487803435957647447049)
    ·
      refine ⟨1318115852576968235585287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757487803435957647447049 1318115852576968235585287)
      ·
        refine ⟨1977173778865452353377931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318115852576968235585287 1977173778865452353377931)
        ·
          refine ⟨2965760668298178530066897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977173778865452353377931 2965760668298178530066897)
          ·
            refine ⟨2224320501223633897550173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965760668298178530066897 2224320501223633897550173)
            ·
              refine ⟨834120187958862711581315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2224320501223633897550173 834120187958862711581315)
              ·
                refine ⟨1251180281938294067371973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834120187958862711581315 1251180281938294067371973)
                ·
                  refine ⟨234596302863430137632245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1251180281938294067371973 234596302863430137632245)
                  ·
                    refine ⟨21993403393446575403023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234596302863430137632245 21993403393446575403023)
                    ·
                      rfl

theorem cell22_64248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_64248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64248 prefixEnd_64248 := by exact prefixLift 64248
  have htrace : WordTrace (prefixWord ++ tailWord_64248) baseStart_64248 baseEnd_64248 := by
    simpa [prefixWord, tailWord_64248, baseEnd_64248] using wordTrace_append hprefix tailTrace_64248
  have hstable : (prefixWord ++ tailWord_64248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64248).length < 2 ^ (prefixWord ++ tailWord_64248).sum := by decide
  have hdescent : baseEnd_64248 < baseStart_64248 := by decide
  rcases family_descends (prefixWord ++ tailWord_64248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64250 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_64250 : Nat := 118140960795 + 64250 * 2 ^ 59
def prefixEnd_64250 : Nat := 4983230072969 + 3 ^ 40 * 64250 * 2
def baseEnd_64250 : Nat := 7331362678106412284339

theorem tailTrace_64250 : CollatzResearch.WordTrace tailWord_64250 prefixEnd_64250 7331362678106412284339 := by
  unfold tailWord_64250
  simp only [CollatzResearch.WordTrace]
  refine ⟨585847504310174467875551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1562260011493798581001469 585847504310174467875551)
  ·
    refine ⟨878771256465261701813327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585847504310174467875551 878771256465261701813327)
    ·
      refine ⟨1318156884697892552719991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878771256465261701813327 1318156884697892552719991)
      ·
        refine ⟨1977235327046838829079987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318156884697892552719991 1977235327046838829079987)
        ·
          refine ⟨2965852990570258243619981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977235327046838829079987 2965852990570258243619981)
          ·
            refine ⟨1112194871463846841357493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2965852990570258243619981 1112194871463846841357493)
            ·
              refine ⟨104268269199735641377265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1112194871463846841357493 104268269199735641377265)
              ·
                refine ⟨78201201899801731032949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104268269199735641377265 78201201899801731032949)
                ·
                  refine ⟨7331362678106412284339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78201201899801731032949 7331362678106412284339)
                  ·
                    rfl

theorem cell22_64250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_64250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64250 prefixEnd_64250 := by exact prefixLift 64250
  have htrace : WordTrace (prefixWord ++ tailWord_64250) baseStart_64250 baseEnd_64250 := by
    simpa [prefixWord, tailWord_64250, baseEnd_64250] using wordTrace_append hprefix tailTrace_64250
  have hstable : (prefixWord ++ tailWord_64250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64250).length < 2 ^ (prefixWord ++ tailWord_64250).sum := by decide
  have hdescent : baseEnd_64250 < baseStart_64250 := by decide
  rcases family_descends (prefixWord ++ tailWord_64250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64254 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_64254 : Nat := 118140960795 + 64254 * 2 ^ 59
def prefixEnd_64254 : Nat := 4983230072969 + 3 ^ 40 * 64254 * 2
def baseEnd_64254 : Nat := 21995457316064559753005

theorem tailTrace_64254 : CollatzResearch.WordTrace tailWord_64254 prefixEnd_64254 21995457316064559753005 := by
  unfold tailWord_64254
  simp only [CollatzResearch.WordTrace]
  refine ⟨292941988653275819330977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1562357272817471036431877 292941988653275819330977)
  ·
    refine ⟨219706491489956864498233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292941988653275819330977 219706491489956864498233)
    ·
      refine ⟨164779868617467648373675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219706491489956864498233 164779868617467648373675)
      ·
        refine ⟨247169802926201472560513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164779868617467648373675 247169802926201472560513)
        ·
          refine ⟨185377352194651104420385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247169802926201472560513 185377352194651104420385)
          ·
            refine ⟨139033014145988328315289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185377352194651104420385 139033014145988328315289)
            ·
              refine ⟨104274760609491246236467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139033014145988328315289 104274760609491246236467)
              ·
                refine ⟨156412140914236869354701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104274760609491246236467 156412140914236869354701)
                ·
                  refine ⟨58654552842838826008013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156412140914236869354701 58654552842838826008013)
                  ·
                    refine ⟨21995457316064559753005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58654552842838826008013 21995457316064559753005)
                    ·
                      rfl

theorem cell22_64254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_64254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64254 prefixEnd_64254 := by exact prefixLift 64254
  have htrace : WordTrace (prefixWord ++ tailWord_64254) baseStart_64254 baseEnd_64254 := by
    simpa [prefixWord, tailWord_64254, baseEnd_64254] using wordTrace_append hprefix tailTrace_64254
  have hstable : (prefixWord ++ tailWord_64254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64254).length < 2 ^ (prefixWord ++ tailWord_64254).sum := by decide
  have hdescent : baseEnd_64254 < baseStart_64254 := by decide
  rcases family_descends (prefixWord ++ tailWord_64254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64370 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_64370 : Nat := 118140960795 + 64370 * 2 ^ 59
def prefixEnd_64370 : Nat := 4983230072969 + 3 ^ 40 * 64370 * 2
def baseEnd_64370 : Nat := 22035166486678923852649

theorem tailTrace_64370 : CollatzResearch.WordTrace tailWord_64370 prefixEnd_64370 22035166486678923852649 := by
  unfold tailWord_64370
  simp only [CollatzResearch.WordTrace]
  refine ⟨586941694201489591467641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1565177851203972243913709 586941694201489591467641)
  ·
    refine ⟨440206270651117193600731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 586941694201489591467641 440206270651117193600731)
    ·
      refine ⟨660309405976675790401097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440206270651117193600731 660309405976675790401097)
      ·
        refine ⟨495232054482506842800823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660309405976675790401097 495232054482506842800823)
        ·
          refine ⟨742848081723760264201235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495232054482506842800823 742848081723760264201235)
          ·
            refine ⟨1114272122585640396301853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742848081723760264201235 1114272122585640396301853)
            ·
              refine ⟨417852045969615148613195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114272122585640396301853 417852045969615148613195)
              ·
                refine ⟨626778068954422722919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417852045969615148613195 626778068954422722919793)
                ·
                  refine ⟨470083551715817042189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626778068954422722919793 470083551715817042189845)
                  ·
                    refine ⟨22035166486678923852649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 470083551715817042189845 22035166486678923852649)
                    ·
                      rfl

theorem cell22_64370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_64370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64370 prefixEnd_64370 := by exact prefixLift 64370
  have htrace : WordTrace (prefixWord ++ tailWord_64370) baseStart_64370 baseEnd_64370 := by
    simpa [prefixWord, tailWord_64370, baseEnd_64370] using wordTrace_append hprefix tailTrace_64370
  have hstable : (prefixWord ++ tailWord_64370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64370).length < 2 ^ (prefixWord ++ tailWord_64370).sum := by decide
  have hdescent : baseEnd_64370 < baseStart_64370 := by decide
  rcases family_descends (prefixWord ++ tailWord_64370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64374 : List Nat := [5, 1, 1, 3, 1, 3, 1, 7]
def baseStart_64374 : Nat := 118140960795 + 64374 * 2 ^ 59
def prefixEnd_64374 : Nat := 4983230072969 + 3 ^ 40 * 64374 * 2
def baseEnd_64374 : Nat := 2448503974269360750293

theorem tailTrace_64374 : CollatzResearch.WordTrace tailWord_64374 prefixEnd_64374 2448503974269360750293 := by
  unfold tailWord_64374
  simp only [CollatzResearch.WordTrace]
  refine ⟨146744541799466690563511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1565275112527644699344117 146744541799466690563511)
  ·
    refine ⟨220116812699200035845267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146744541799466690563511 220116812699200035845267)
    ·
      refine ⟨330175219048800053767901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220116812699200035845267 330175219048800053767901)
      ·
        refine ⟨123815707143300020162963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330175219048800053767901 123815707143300020162963)
        ·
          refine ⟨185723560714950030244445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123815707143300020162963 185723560714950030244445)
          ·
            refine ⟨69646335268106261341667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185723560714950030244445 69646335268106261341667)
            ·
              refine ⟨104469502902159392012501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69646335268106261341667 104469502902159392012501)
              ·
                refine ⟨2448503974269360750293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104469502902159392012501 2448503974269360750293)
                ·
                  rfl

theorem cell22_64374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_64374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64374 prefixEnd_64374 := by exact prefixLift 64374
  have htrace : WordTrace (prefixWord ++ tailWord_64374) baseStart_64374 baseEnd_64374 := by
    simpa [prefixWord, tailWord_64374, baseEnd_64374] using wordTrace_append hprefix tailTrace_64374
  have hstable : (prefixWord ++ tailWord_64374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64374).length < 2 ^ (prefixWord ++ tailWord_64374).sum := by decide
  have hdescent : baseEnd_64374 < baseStart_64374 := by decide
  rcases family_descends (prefixWord ++ tailWord_64374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64417 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_64417 : Nat := 118140960795 + 64417 * 2 ^ 59
def prefixEnd_64417 : Nat := 4983230072969 + 3 ^ 40 * 64417 * 2
def baseEnd_64417 : Nat := 22051255547186467927505

theorem tailTrace_64417 : CollatzResearch.WordTrace tailWord_64417 prefixEnd_64417 22051255547186467927505 := by
  unfold tailWord_64417
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349481007635685392831505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1566320671757123595221003 2349481007635685392831505)
  ·
    refine ⟨1762110755726764044623629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2349481007635685392831505 1762110755726764044623629)
    ·
      refine ⟨660791533397536516733861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1762110755726764044623629 660791533397536516733861)
      ·
        refine ⟨123898412512038096887599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 660791533397536516733861 123898412512038096887599)
        ·
          refine ⟨185847618768057145331399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123898412512038096887599 185847618768057145331399)
          ·
            refine ⟨278771428152085717997099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185847618768057145331399 278771428152085717997099)
            ·
              refine ⟨418157142228128576995649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278771428152085717997099 418157142228128576995649)
              ·
                refine ⟨313617856671096432746737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418157142228128576995649 313617856671096432746737)
                ·
                  refine ⟨235213392503322324560053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313617856671096432746737 235213392503322324560053)
                  ·
                    refine ⟨22051255547186467927505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 235213392503322324560053 22051255547186467927505)
                    ·
                      rfl

theorem cell22_64417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_64417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64417 prefixEnd_64417 := by exact prefixLift 64417
  have htrace : WordTrace (prefixWord ++ tailWord_64417) baseStart_64417 baseEnd_64417 := by
    simpa [prefixWord, tailWord_64417, baseEnd_64417] using wordTrace_append hprefix tailTrace_64417
  have hstable : (prefixWord ++ tailWord_64417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64417).length < 2 ^ (prefixWord ++ tailWord_64417).sum := by decide
  have hdescent : baseEnd_64417 < baseStart_64417 := by decide
  rcases family_descends (prefixWord ++ tailWord_64417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64500 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_64500 : Nat := 118140960795 + 64500 * 2 ^ 59
def prefixEnd_64500 : Nat := 4983230072969 + 3 ^ 40 * 64500 * 2
def baseEnd_64500 : Nat := 22079668143401918102251

theorem tailTrace_64500 : CollatzResearch.WordTrace tailWord_64500 prefixEnd_64500 22079668143401918102251 := by
  unfold tailWord_64500
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176254133167495284051477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1568338844223327045401969 1176254133167495284051477)
  ·
    refine ⟨55136912492226341439913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1176254133167495284051477 55136912492226341439913)
    ·
      refine ⟨41352684369169756079935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55136912492226341439913 41352684369169756079935)
      ·
        refine ⟨62029026553754634119903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41352684369169756079935 62029026553754634119903)
        ·
          refine ⟨93043539830631951179855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62029026553754634119903 93043539830631951179855)
          ·
            refine ⟨139565309745947926769783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93043539830631951179855 139565309745947926769783)
            ·
              refine ⟨209347964618921890154675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139565309745947926769783 209347964618921890154675)
              ·
                refine ⟨314021946928382835232013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209347964618921890154675 314021946928382835232013)
                ·
                  refine ⟨117758230098143563212005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314021946928382835232013 117758230098143563212005)
                  ·
                    refine ⟨22079668143401918102251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117758230098143563212005 22079668143401918102251)
                    ·
                      rfl

theorem cell22_64500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_64500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64500 prefixEnd_64500 := by exact prefixLift 64500
  have htrace : WordTrace (prefixWord ++ tailWord_64500) baseStart_64500 baseEnd_64500 := by
    simpa [prefixWord, tailWord_64500, baseEnd_64500] using wordTrace_append hprefix tailTrace_64500
  have hstable : (prefixWord ++ tailWord_64500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64500).length < 2 ^ (prefixWord ++ tailWord_64500).sum := by decide
  have hdescent : baseEnd_64500 < baseStart_64500 := by decide
  rcases family_descends (prefixWord ++ tailWord_64500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64507 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 5, 3]
def baseStart_64507 : Nat := 118140960795 + 64507 * 2 ^ 59
def prefixEnd_64507 : Nat := 4983230072969 + 3 ^ 40 * 64507 * 2
def baseEnd_64507 : Nat := 22082064386456233177229

theorem tailTrace_64507 : CollatzResearch.WordTrace tailWord_64507 prefixEnd_64507 22082064386456233177229 := by
  unfold tailWord_64507
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352763577309630763607775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1568509051539753842405183 2352763577309630763607775)
  ·
    refine ⟨3529145365964446145411663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2352763577309630763607775 3529145365964446145411663)
    ·
      refine ⟨5293718048946669218117495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3529145365964446145411663 5293718048946669218117495)
      ·
        refine ⟨7940577073420003827176243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5293718048946669218117495 7940577073420003827176243)
        ·
          refine ⟨11910865610130005740764365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940577073420003827176243 11910865610130005740764365)
          ·
            refine ⟨4466574603798752152786637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11910865610130005740764365 4466574603798752152786637)
            ·
              refine ⟨1674965476424532057294989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4466574603798752152786637 1674965476424532057294989)
              ·
                refine ⟨628112053659199521485621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1674965476424532057294989 628112053659199521485621)
                ·
                  refine ⟨58885505030549955139277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 628112053659199521485621 58885505030549955139277)
                  ·
                    refine ⟨22082064386456233177229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58885505030549955139277 22082064386456233177229)
                    ·
                      rfl

theorem cell22_64507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 3].length) (baseStart_64507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64507 prefixEnd_64507 := by exact prefixLift 64507
  have htrace : WordTrace (prefixWord ++ tailWord_64507) baseStart_64507 baseEnd_64507 := by
    simpa [prefixWord, tailWord_64507, baseEnd_64507] using wordTrace_append hprefix tailTrace_64507
  have hstable : (prefixWord ++ tailWord_64507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64507).length < 2 ^ (prefixWord ++ tailWord_64507).sum := by decide
  have hdescent : baseEnd_64507 < baseStart_64507 := by decide
  rcases family_descends (prefixWord ++ tailWord_64507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64537 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 5]
def baseStart_64537 : Nat := 118140960795 + 64537 * 2 ^ 59
def prefixEnd_64537 : Nat := 4983230072969 + 3 ^ 40 * 64537 * 2
def baseEnd_64537 : Nat := 7364111333182051642379

theorem tailTrace_64537 : CollatzResearch.WordTrace tailWord_64537 prefixEnd_64537 7364111333182051642379 := by
  unfold tailWord_64537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353857767200945887199865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1569238511467297258133243 2353857767200945887199865)
  ·
    refine ⟨1765393325400709415399899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2353857767200945887199865 1765393325400709415399899)
    ·
      refine ⟨2648089988101064123099849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1765393325400709415399899 2648089988101064123099849)
      ·
        refine ⟨1986067491075798092324887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2648089988101064123099849 1986067491075798092324887)
        ·
          refine ⟨2979101236613697138487331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986067491075798092324887 2979101236613697138487331)
          ·
            refine ⟨4468651854920545707730997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979101236613697138487331 4468651854920545707730997)
            ·
              refine ⟨418936111398801160099781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4468651854920545707730997 418936111398801160099781)
              ·
                refine ⟨78550520887275217518709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418936111398801160099781 78550520887275217518709)
                ·
                  refine ⟨7364111333182051642379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78550520887275217518709 7364111333182051642379)
                  ·
                    rfl

theorem cell22_64537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_64537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64537 prefixEnd_64537 := by exact prefixLift 64537
  have htrace : WordTrace (prefixWord ++ tailWord_64537) baseStart_64537 baseEnd_64537 := by
    simpa [prefixWord, tailWord_64537, baseEnd_64537] using wordTrace_append hprefix tailTrace_64537
  have hstable : (prefixWord ++ tailWord_64537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64537).length < 2 ^ (prefixWord ++ tailWord_64537).sum := by decide
  have hdescent : baseEnd_64537 < baseStart_64537 := by decide
  rcases family_descends (prefixWord ++ tailWord_64537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64584 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_64584 : Nat := 118140960795 + 64584 * 2 ^ 59
def prefixEnd_64584 : Nat := 4983230072969 + 3 ^ 40 * 64584 * 2
def baseEnd_64584 : Nat := 22108423060053699001993

theorem tailTrace_64584 : CollatzResearch.WordTrace tailWord_64584 prefixEnd_64584 22108423060053699001993 := by
  unfold tailWord_64584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177785999015336457080403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1570381332020448609440537 1177785999015336457080403)
  ·
    refine ⟨1766678998523004685620605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177785999015336457080403 1766678998523004685620605)
    ·
      refine ⟨662504624446126757107727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1766678998523004685620605 662504624446126757107727)
      ·
        refine ⟨993756936669190135661591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662504624446126757107727 993756936669190135661591)
        ·
          refine ⟨1490635405003785203492387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993756936669190135661591 1490635405003785203492387)
          ·
            refine ⟨2235953107505677805238581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490635405003785203492387 2235953107505677805238581)
            ·
              refine ⟨209620603828657294241117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2235953107505677805238581 209620603828657294241117)
              ·
                refine ⟨78607726435746485340419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209620603828657294241117 78607726435746485340419)
                ·
                  refine ⟨117911589653619728010629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78607726435746485340419 117911589653619728010629)
                  ·
                    refine ⟨22108423060053699001993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117911589653619728010629 22108423060053699001993)
                    ·
                      rfl

theorem cell22_64584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_64584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64584 prefixEnd_64584 := by exact prefixLift 64584
  have htrace : WordTrace (prefixWord ++ tailWord_64584) baseStart_64584 baseEnd_64584 := by
    simpa [prefixWord, tailWord_64584, baseEnd_64584] using wordTrace_append hprefix tailTrace_64584
  have hstable : (prefixWord ++ tailWord_64584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64584).length < 2 ^ (prefixWord ++ tailWord_64584).sum := by decide
  have hdescent : baseEnd_64584 < baseStart_64584 := by decide
  rcases family_descends (prefixWord ++ tailWord_64584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64633 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 4]
def baseStart_64633 : Nat := 118140960795 + 64633 * 2 ^ 59
def prefixEnd_64633 : Nat := 4983230072969 + 3 ^ 40 * 64633 * 2
def baseEnd_64633 : Nat := 7375065587144634842281

theorem tailTrace_64633 : CollatzResearch.WordTrace tailWord_64633 prefixEnd_64633 7375065587144634842281 := by
  unfold tailWord_64633
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357359174853154282694553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1571572783235436188463035 2357359174853154282694553)
  ·
    refine ⟨1768019381139865712020915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2357359174853154282694553 1768019381139865712020915)
    ·
      refine ⟨2652029071709798568031373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768019381139865712020915 2652029071709798568031373)
      ·
        refine ⟨994510901891174463011765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2652029071709798568031373 994510901891174463011765)
        ·
          refine ⟨93235397052297605907353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 994510901891174463011765 93235397052297605907353)
          ·
            refine ⟨69926547789223204430515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93235397052297605907353 69926547789223204430515)
            ·
              refine ⟨104889821683834806645773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69926547789223204430515 104889821683834806645773)
              ·
                refine ⟨39333683131438052492165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104889821683834806645773 39333683131438052492165)
                ·
                  refine ⟨7375065587144634842281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39333683131438052492165 7375065587144634842281)
                  ·
                    rfl

theorem cell22_64633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_64633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64633 prefixEnd_64633 := by exact prefixLift 64633
  have htrace : WordTrace (prefixWord ++ tailWord_64633) baseStart_64633 baseEnd_64633 := by
    simpa [prefixWord, tailWord_64633, baseEnd_64633] using wordTrace_append hprefix tailTrace_64633
  have hstable : (prefixWord ++ tailWord_64633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64633).length < 2 ^ (prefixWord ++ tailWord_64633).sum := by decide
  have hdescent : baseEnd_64633 < baseStart_64633 := by decide
  rcases family_descends (prefixWord ++ tailWord_64633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64644 : List Nat := [2, 3, 2, 1, 2, 4, 8]
def baseStart_64644 : Nat := 118140960795 + 64644 * 2 ^ 59
def prefixEnd_64644 : Nat := 4983230072969 + 3 ^ 40 * 64644 * 2
def baseEnd_64644 : Nat := 819591195786427500067

theorem tailTrace_64644 : CollatzResearch.WordTrace tailWord_64644 prefixEnd_64644 819591195786427500067 := by
  unfold tailWord_64644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178880188906651580672493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1571840251875535440896657 1178880188906651580672493)
  ·
    refine ⟨442080070839994342752185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1178880188906651580672493 442080070839994342752185)
    ·
      refine ⟨331560053129995757064139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442080070839994342752185 331560053129995757064139)
      ·
        refine ⟨497340079694993635596209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331560053129995757064139 497340079694993635596209)
        ·
          refine ⟨373005059771245226697157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497340079694993635596209 373005059771245226697157)
          ·
            refine ⟨69938448707108480005717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373005059771245226697157 69938448707108480005717)
            ·
              refine ⟨819591195786427500067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 69938448707108480005717 819591195786427500067)
              ·
                rfl

theorem cell22_64644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 8].length) (baseStart_64644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64644 prefixEnd_64644 := by exact prefixLift 64644
  have htrace : WordTrace (prefixWord ++ tailWord_64644) baseStart_64644 baseEnd_64644 := by
    simpa [prefixWord, tailWord_64644, baseEnd_64644] using wordTrace_append hprefix tailTrace_64644
  have hstable : (prefixWord ++ tailWord_64644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64644).length < 2 ^ (prefixWord ++ tailWord_64644).sum := by decide
  have hdescent : baseEnd_64644 < baseStart_64644 := by decide
  rcases family_descends (prefixWord ++ tailWord_64644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64796 : List Nat := [2, 2, 3, 1, 1, 1, 6, 6]
def baseStart_64796 : Nat := 118140960795 + 64796 * 2 ^ 59
def prefixEnd_64796 : Nat := 4983230072969 + 3 ^ 40 * 64796 * 2
def baseEnd_64796 : Nat := 2464554999172868077927

theorem tailTrace_64796 : CollatzResearch.WordTrace tailWord_64796 prefixEnd_64796 2464554999172868077927 := by
  unfold tailWord_64796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181652136631316560439121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1575536182175088747252161 1181652136631316560439121)
  ·
    refine ⟨886239102473487420329341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1181652136631316560439121 886239102473487420329341)
    ·
      refine ⟨332339663427557782623503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 886239102473487420329341 332339663427557782623503)
      ·
        refine ⟨498509495141336673935255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332339663427557782623503 498509495141336673935255)
        ·
          refine ⟨747764242712005010902883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498509495141336673935255 747764242712005010902883)
          ·
            refine ⟨1121646364068007516354325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747764242712005010902883 1121646364068007516354325)
            ·
              refine ⟨52577173315687852329109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1121646364068007516354325 52577173315687852329109)
              ·
                refine ⟨2464554999172868077927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52577173315687852329109 2464554999172868077927)
                ·
                  rfl

theorem cell22_64796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 6].length) (baseStart_64796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64796 prefixEnd_64796 := by exact prefixLift 64796
  have htrace : WordTrace (prefixWord ++ tailWord_64796) baseStart_64796 baseEnd_64796 := by
    simpa [prefixWord, tailWord_64796, baseEnd_64796] using wordTrace_append hprefix tailTrace_64796
  have hstable : (prefixWord ++ tailWord_64796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64796).length < 2 ^ (prefixWord ++ tailWord_64796).sum := by decide
  have hdescent : baseEnd_64796 < baseStart_64796 := by decide
  rcases family_descends (prefixWord ++ tailWord_64796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64802 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_64802 : Nat := 118140960795 + 64802 * 2 ^ 59
def prefixEnd_64802 : Nat := 4983230072969 + 3 ^ 40 * 64802 * 2
def baseEnd_64802 : Nat := 7394349638391265683775

theorem tailTrace_64802 : CollatzResearch.WordTrace tailWord_64802 prefixEnd_64802 7394349638391265683775 := by
  unfold tailWord_64802
  simp only [CollatzResearch.WordTrace]
  refine ⟨590880777810224036399165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1575682074160597430397773 590880777810224036399165)
  ·
    refine ⟨221580291678834013649687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 590880777810224036399165 221580291678834013649687)
    ·
      refine ⟨332370437518251020474531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221580291678834013649687 332370437518251020474531)
      ·
        refine ⟨498555656277376530711797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332370437518251020474531 498555656277376530711797)
        ·
          refine ⟨46739592776004049754231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 498555656277376530711797 46739592776004049754231)
          ·
            refine ⟨70109389164006074631347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46739592776004049754231 70109389164006074631347)
            ·
              refine ⟨105164083746009111947021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70109389164006074631347 105164083746009111947021)
              ·
                refine ⟨39436531404753416980133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105164083746009111947021 39436531404753416980133)
                ·
                  refine ⟨7394349638391265683775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39436531404753416980133 7394349638391265683775)
                  ·
                    rfl

theorem cell22_64802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_64802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64802 prefixEnd_64802 := by exact prefixLift 64802
  have htrace : WordTrace (prefixWord ++ tailWord_64802) baseStart_64802 baseEnd_64802 := by
    simpa [prefixWord, tailWord_64802, baseEnd_64802] using wordTrace_append hprefix tailTrace_64802
  have hstable : (prefixWord ++ tailWord_64802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64802).length < 2 ^ (prefixWord ++ tailWord_64802).sum := by decide
  have hdescent : baseEnd_64802 < baseStart_64802 := by decide
  rcases family_descends (prefixWord ++ tailWord_64802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64813 : List Nat := [1, 5, 3, 1, 1, 3, 8]
def baseStart_64813 : Nat := 118140960795 + 64813 * 2 ^ 59
def prefixEnd_64813 : Nat := 4983230072969 + 3 ^ 40 * 64813 * 2
def baseEnd_64813 : Nat := 821733868147164260233

theorem tailTrace_64813 : CollatzResearch.WordTrace tailWord_64813 prefixEnd_64813 821733868147164260233 := by
  unfold tailWord_64813
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363924314201045024247093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1575949542800696682831395 2363924314201045024247093)
  ·
    refine ⟨221617904456347971023165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2363924314201045024247093 221617904456347971023165)
    ·
      refine ⟨83106714171130489133687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221617904456347971023165 83106714171130489133687)
      ·
        refine ⟨124660071256695733700531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83106714171130489133687 124660071256695733700531)
        ·
          refine ⟨186990106885043600550797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124660071256695733700531 186990106885043600550797)
          ·
            refine ⟨70121290081891350206549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186990106885043600550797 70121290081891350206549)
            ·
              refine ⟨821733868147164260233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 70121290081891350206549 821733868147164260233)
              ·
                rfl

theorem cell22_64813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 8].length) (baseStart_64813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64813 prefixEnd_64813 := by exact prefixLift 64813
  have htrace : WordTrace (prefixWord ++ tailWord_64813) baseStart_64813 baseEnd_64813 := by
    simpa [prefixWord, tailWord_64813, baseEnd_64813] using wordTrace_append hprefix tailTrace_64813
  have hstable : (prefixWord ++ tailWord_64813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64813).length < 2 ^ (prefixWord ++ tailWord_64813).sum := by decide
  have hdescent : baseEnd_64813 < baseStart_64813 := by decide
  rcases family_descends (prefixWord ++ tailWord_64813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64828 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_64828 : Nat := 118140960795 + 64828 * 2 ^ 59
def prefixEnd_64828 : Nat := 4983230072969 + 3 ^ 40 * 64828 * 2
def baseEnd_64828 : Nat := 22191949246518395901245

theorem tailTrace_64828 : CollatzResearch.WordTrace tailWord_64828 prefixEnd_64828 22191949246518395901245 := by
  unfold tailWord_64828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182235704573351293021569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1576314272764468390695425 1182235704573351293021569)
  ·
    refine ⟨886676778430013469766177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1182235704573351293021569 886676778430013469766177)
    ·
      refine ⟨665007583822510102324633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886676778430013469766177 665007583822510102324633)
      ·
        refine ⟨498755687866882576743475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665007583822510102324633 498755687866882576743475)
        ·
          refine ⟨748133531800323865115213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498755687866882576743475 748133531800323865115213)
          ·
            refine ⟨280550074425121449418205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748133531800323865115213 280550074425121449418205)
            ·
              refine ⟨105206277909420543531827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280550074425121449418205 105206277909420543531827)
              ·
                refine ⟨157809416864130815297741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105206277909420543531827 157809416864130815297741)
                ·
                  refine ⟨59178531324049055736653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157809416864130815297741 59178531324049055736653)
                  ·
                    refine ⟨22191949246518395901245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59178531324049055736653 22191949246518395901245)
                    ·
                      rfl

theorem cell22_64828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_64828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64828 prefixEnd_64828 := by exact prefixLift 64828
  have htrace : WordTrace (prefixWord ++ tailWord_64828) baseStart_64828 baseEnd_64828 := by
    simpa [prefixWord, tailWord_64828, baseEnd_64828] using wordTrace_append hprefix tailTrace_64828
  have hstable : (prefixWord ++ tailWord_64828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64828).length < 2 ^ (prefixWord ++ tailWord_64828).sum := by decide
  have hdescent : baseEnd_64828 < baseStart_64828 := by decide
  rcases family_descends (prefixWord ++ tailWord_64828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64901 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_64901 : Nat := 118140960795 + 64901 * 2 ^ 59
def prefixEnd_64901 : Nat := 4983230072969 + 3 ^ 40 * 64901 * 2
def baseEnd_64901 : Nat := 22216938638370538826021

theorem tailTrace_64901 : CollatzResearch.WordTrace tailWord_64901 prefixEnd_64901 22216938638370538826021 := by
  unfold tailWord_64901
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367133937882236053450557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1578089291921490702300371 2367133937882236053450557)
  ·
    refine ⟨887675226705838520043959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2367133937882236053450557 887675226705838520043959)
    ·
      refine ⟨1331512840058757780065939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887675226705838520043959 1331512840058757780065939)
      ·
        refine ⟨1997269260088136670098909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331512840058757780065939 1997269260088136670098909)
        ·
          refine ⟨748975972533051251287091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997269260088136670098909 748975972533051251287091)
          ·
            refine ⟨1123463958799576876930637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748975972533051251287091 1123463958799576876930637)
            ·
              refine ⟨421298984549841328848989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123463958799576876930637 421298984549841328848989)
              ·
                refine ⟨157987119206190498318371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421298984549841328848989 157987119206190498318371)
                ·
                  refine ⟨236980678809285747477557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157987119206190498318371 236980678809285747477557)
                  ·
                    refine ⟨22216938638370538826021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 236980678809285747477557 22216938638370538826021)
                    ·
                      rfl

theorem cell22_64901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_64901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64901 prefixEnd_64901 := by exact prefixLift 64901
  have htrace : WordTrace (prefixWord ++ tailWord_64901) baseStart_64901 baseEnd_64901 := by
    simpa [prefixWord, tailWord_64901, baseEnd_64901] using wordTrace_append hprefix tailTrace_64901
  have hstable : (prefixWord ++ tailWord_64901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64901).length < 2 ^ (prefixWord ++ tailWord_64901).sum := by decide
  have hdescent : baseEnd_64901 < baseStart_64901 := by decide
  rcases family_descends (prefixWord ++ tailWord_64901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64963 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 3, 3]
def baseStart_64963 : Nat := 118140960795 + 64963 * 2 ^ 59
def prefixEnd_64963 : Nat := 4983230072969 + 3 ^ 40 * 64963 * 2
def baseEnd_64963 : Nat := 22238162505423043775831

theorem tailTrace_64963 : CollatzResearch.WordTrace tailWord_64963 prefixEnd_64963 22238162505423043775831 := by
  unfold tailWord_64963
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369395263657620642207543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1579596842438413761471695 2369395263657620642207543)
  ·
    refine ⟨3554092895486430963311315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2369395263657620642207543 3554092895486430963311315)
    ·
      refine ⟨5331139343229646444966973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3554092895486430963311315 5331139343229646444966973)
      ·
        refine ⟨1999177253711117416862615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5331139343229646444966973 1999177253711117416862615)
        ·
          refine ⟨2998765880566676125293923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999177253711117416862615 2998765880566676125293923)
          ·
            refine ⟨4498148820850014187940885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998765880566676125293923 4498148820850014187940885)
            ·
              refine ⟨210850725977344415059729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4498148820850014187940885 210850725977344415059729)
              ·
                refine ⟨158138044483008311294797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210850725977344415059729 158138044483008311294797)
                ·
                  refine ⟨59301766681128116735549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158138044483008311294797 59301766681128116735549)
                  ·
                    refine ⟨22238162505423043775831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59301766681128116735549 22238162505423043775831)
                    ·
                      rfl

theorem cell22_64963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 3].length) (baseStart_64963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64963 prefixEnd_64963 := by exact prefixLift 64963
  have htrace : WordTrace (prefixWord ++ tailWord_64963) baseStart_64963 baseEnd_64963 := by
    simpa [prefixWord, tailWord_64963, baseEnd_64963] using wordTrace_append hprefix tailTrace_64963
  have hstable : (prefixWord ++ tailWord_64963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64963).length < 2 ^ (prefixWord ++ tailWord_64963).sum := by decide
  have hdescent : baseEnd_64963 < baseStart_64963 := by decide
  rcases family_descends (prefixWord ++ tailWord_64963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64997 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_64997 : Nat := 118140960795 + 64997 * 2 ^ 59
def prefixEnd_64997 : Nat := 4983230072969 + 3 ^ 40 * 64997 * 2
def baseEnd_64997 : Nat := 22249801400258288425727

theorem tailTrace_64997 : CollatzResearch.WordTrace tailWord_64997 prefixEnd_64997 22249801400258288425727 := by
  unfold tailWord_64997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370635345534444448945245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1580423563689629632630163 2370635345534444448945245)
  ·
    refine ⟨888988254575416668354467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2370635345534444448945245 888988254575416668354467)
    ·
      refine ⟨1333482381863125002531701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888988254575416668354467 1333482381863125002531701)
      ·
        refine ⟨125013973299667968987347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1333482381863125002531701 125013973299667968987347)
        ·
          refine ⟨187520959949501953481021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125013973299667968987347 187520959949501953481021)
          ·
            refine ⟨70320359981063232555383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187520959949501953481021 70320359981063232555383)
            ·
              refine ⟨105480539971594848833075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70320359981063232555383 105480539971594848833075)
              ·
                refine ⟨158220809957392273249613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105480539971594848833075 158220809957392273249613)
                ·
                  refine ⟨59332803734022102468605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158220809957392273249613 59332803734022102468605)
                  ·
                    refine ⟨22249801400258288425727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59332803734022102468605 22249801400258288425727)
                    ·
                      rfl

theorem cell22_64997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_64997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_64997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_64997 prefixEnd_64997 := by exact prefixLift 64997
  have htrace : WordTrace (prefixWord ++ tailWord_64997) baseStart_64997 baseEnd_64997 := by
    simpa [prefixWord, tailWord_64997, baseEnd_64997] using wordTrace_append hprefix tailTrace_64997
  have hstable : (prefixWord ++ tailWord_64997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64997).length < 2 ^ (prefixWord ++ tailWord_64997).sum := by decide
  have hdescent : baseEnd_64997 < baseStart_64997 := by decide
  rcases family_descends (prefixWord ++ tailWord_64997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65010 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_65010 : Nat := 118140960795 + 65010 * 2 ^ 59
def prefixEnd_65010 : Nat := 4983230072969 + 3 ^ 40 * 65010 * 2
def baseEnd_65010 : Nat := 7418083855310195950229

theorem tailTrace_65010 : CollatzResearch.WordTrace tailWord_65010 prefixEnd_65010 7418083855310195950229 := by
  unfold tailWord_65010
  simp only [CollatzResearch.WordTrace]
  refine ⟨592777373621836917292121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1580739662991565112778989 592777373621836917292121)
  ·
    refine ⟨444583030216377687969091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 592777373621836917292121 444583030216377687969091)
    ·
      refine ⟨666874545324566531953637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444583030216377687969091 666874545324566531953637)
      ·
        refine ⟨125038977248356224741307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 666874545324566531953637 125038977248356224741307)
        ·
          refine ⟨187558465872534337111961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125038977248356224741307 187558465872534337111961)
          ·
            refine ⟨140668849404400752833971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187558465872534337111961 140668849404400752833971)
            ·
              refine ⟨211003274106601129250957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140668849404400752833971 211003274106601129250957)
              ·
                refine ⟨79126227789975423469109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211003274106601129250957 79126227789975423469109)
                ·
                  refine ⟨7418083855310195950229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79126227789975423469109 7418083855310195950229)
                  ·
                    rfl

theorem cell22_65010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_65010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65010 prefixEnd_65010 := by exact prefixLift 65010
  have htrace : WordTrace (prefixWord ++ tailWord_65010) baseStart_65010 baseEnd_65010 := by
    simpa [prefixWord, tailWord_65010, baseEnd_65010] using wordTrace_append hprefix tailTrace_65010
  have hstable : (prefixWord ++ tailWord_65010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65010).length < 2 ^ (prefixWord ++ tailWord_65010).sum := by decide
  have hdescent : baseEnd_65010 < baseStart_65010 := by decide
  rcases family_descends (prefixWord ++ tailWord_65010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65023 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 1, 4]
def baseStart_65023 : Nat := 118140960795 + 65023 * 2 ^ 59
def prefixEnd_65023 : Nat := 4983230072969 + 3 ^ 40 * 65023 * 2
def baseEnd_65023 : Nat := 22258701731602887275647

theorem tailTrace_65023 : CollatzResearch.WordTrace tailWord_65023 prefixEnd_65023 22258701731602887275647 := by
  unfold tailWord_65023
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371583643440250889391723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1581055762293500592927815 2371583643440250889391723)
  ·
    refine ⟨3557375465160376334087585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2371583643440250889391723 3557375465160376334087585)
    ·
      refine ⟨2668031598870282250565689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3557375465160376334087585 2668031598870282250565689)
      ·
        refine ⟨2001023699152711687924267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668031598870282250565689 2001023699152711687924267)
        ·
          refine ⟨3001535548729067531886401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001023699152711687924267 3001535548729067531886401)
          ·
            refine ⟨2251151661546800648914801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3001535548729067531886401 2251151661546800648914801)
            ·
              refine ⟨1688363746160100486686101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2251151661546800648914801 1688363746160100486686101)
              ·
                refine ⟨79142050601254710313411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1688363746160100486686101 79142050601254710313411)
                ·
                  refine ⟨118713075901882065470117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79142050601254710313411 118713075901882065470117)
                  ·
                    refine ⟨22258701731602887275647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118713075901882065470117 22258701731602887275647)
                    ·
                      rfl

theorem cell22_65023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 4].length) (baseStart_65023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65023 prefixEnd_65023 := by exact prefixLift 65023
  have htrace : WordTrace (prefixWord ++ tailWord_65023) baseStart_65023 baseEnd_65023 := by
    simpa [prefixWord, tailWord_65023, baseEnd_65023] using wordTrace_append hprefix tailTrace_65023
  have hstable : (prefixWord ++ tailWord_65023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65023).length < 2 ^ (prefixWord ++ tailWord_65023).sum := by decide
  have hdescent : baseEnd_65023 < baseStart_65023 := by decide
  rcases family_descends (prefixWord ++ tailWord_65023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65053 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_65053 : Nat := 118140960795 + 65053 * 2 ^ 59
def prefixEnd_65053 : Nat := 4983230072969 + 3 ^ 40 * 65053 * 2
def baseEnd_65053 : Nat := 22268971344692809025555

theorem tailTrace_65053 : CollatzResearch.WordTrace tailWord_65053 prefixEnd_65053 22268971344692809025555 := by
  unfold tailWord_65053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372677833331566012983813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1581785222221044008655875 2372677833331566012983813)
  ·
    refine ⟨444877093749668627434465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2372677833331566012983813 444877093749668627434465)
    ·
      refine ⟨333657820312251470575849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444877093749668627434465 333657820312251470575849)
      ·
        refine ⟨250243365234188602931887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333657820312251470575849 250243365234188602931887)
        ·
          refine ⟨375365047851282904397831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250243365234188602931887 375365047851282904397831)
          ·
            refine ⟨563047571776924356596747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375365047851282904397831 563047571776924356596747)
            ·
              refine ⟨844571357665386534895121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563047571776924356596747 844571357665386534895121)
              ·
                refine ⟨633428518249039901171341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844571357665386534895121 633428518249039901171341)
                ·
                  refine ⟨237535694343389962939253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633428518249039901171341 237535694343389962939253)
                  ·
                    refine ⟨22268971344692809025555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237535694343389962939253 22268971344692809025555)
                    ·
                      rfl

theorem cell22_65053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_65053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65053 prefixEnd_65053 := by exact prefixLift 65053
  have htrace : WordTrace (prefixWord ++ tailWord_65053) baseStart_65053 baseEnd_65053 := by
    simpa [prefixWord, tailWord_65053, baseEnd_65053] using wordTrace_append hprefix tailTrace_65053
  have hstable : (prefixWord ++ tailWord_65053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65053).length < 2 ^ (prefixWord ++ tailWord_65053).sum := by decide
  have hdescent : baseEnd_65053 < baseStart_65053 := by decide
  rcases family_descends (prefixWord ++ tailWord_65053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65070 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_65070 : Nat := 118140960795 + 65070 * 2 ^ 59
def prefixEnd_65070 : Nat := 4983230072969 + 3 ^ 40 * 65070 * 2
def baseEnd_65070 : Nat := 22274790792110431350503

theorem tailTrace_65070 : CollatzResearch.WordTrace tailWord_65070 prefixEnd_65070 22274790792110431350503 := by
  unfold tailWord_65070
  simp only [CollatzResearch.WordTrace]
  refine ⟨296662234283747239544083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1582198582846651944235109 296662234283747239544083)
  ·
    refine ⟨444993351425620859316125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296662234283747239544083 444993351425620859316125)
    ·
      refine ⟨166872506784607822243547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444993351425620859316125 166872506784607822243547)
      ·
        refine ⟨250308760176911733365321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166872506784607822243547 250308760176911733365321)
        ·
          refine ⟨187731570132683800023991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250308760176911733365321 187731570132683800023991)
          ·
            refine ⟨281597355199025700035987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187731570132683800023991 281597355199025700035987)
            ·
              refine ⟨422396032798538550053981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281597355199025700035987 422396032798538550053981)
              ·
                refine ⟨158398512299451956270243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422396032798538550053981 158398512299451956270243)
                ·
                  refine ⟨237597768449177934405365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158398512299451956270243 237597768449177934405365)
                  ·
                    refine ⟨22274790792110431350503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237597768449177934405365 22274790792110431350503)
                    ·
                      rfl

theorem cell22_65070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_65070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65070 prefixEnd_65070 := by exact prefixLift 65070
  have htrace : WordTrace (prefixWord ++ tailWord_65070) baseStart_65070 baseEnd_65070 := by
    simpa [prefixWord, tailWord_65070, baseEnd_65070] using wordTrace_append hprefix tailTrace_65070
  have hstable : (prefixWord ++ tailWord_65070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65070).length < 2 ^ (prefixWord ++ tailWord_65070).sum := by decide
  have hdescent : baseEnd_65070 < baseStart_65070 := by decide
  rcases family_descends (prefixWord ++ tailWord_65070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65085 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_65085 : Nat := 118140960795 + 65085 * 2 ^ 59
def prefixEnd_65085 : Nat := 4983230072969 + 3 ^ 40 * 65085 * 2
def baseEnd_65085 : Nat := 22279925598655392225457

theorem tailTrace_65085 : CollatzResearch.WordTrace tailWord_65085 prefixEnd_65085 22279925598655392225457 := by
  unfold tailWord_65085
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373844969215635478148709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1582563312810423652099139 2373844969215635478148709)
  ·
    refine ⟨445095931727931652152883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2373844969215635478148709 445095931727931652152883)
    ·
      refine ⟨667643897591897478229325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445095931727931652152883 667643897591897478229325)
      ·
        refine ⟨250366461596961554335997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667643897591897478229325 250366461596961554335997)
        ·
          refine ⟨93887423098860582875999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250366461596961554335997 93887423098860582875999)
          ·
            refine ⟨140831134648290874313999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93887423098860582875999 140831134648290874313999)
            ·
              refine ⟨211246701972436311470999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140831134648290874313999 211246701972436311470999)
              ·
                refine ⟨316870052958654467206499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211246701972436311470999 316870052958654467206499)
                ·
                  refine ⟨475305079437981700809749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316870052958654467206499 475305079437981700809749)
                  ·
                    refine ⟨22279925598655392225457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 475305079437981700809749 22279925598655392225457)
                    ·
                      rfl

theorem cell22_65085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_65085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65085 prefixEnd_65085 := by exact prefixLift 65085
  have htrace : WordTrace (prefixWord ++ tailWord_65085) baseStart_65085 baseEnd_65085 := by
    simpa [prefixWord, tailWord_65085, baseEnd_65085] using wordTrace_append hprefix tailTrace_65085
  have hstable : (prefixWord ++ tailWord_65085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65085).length < 2 ^ (prefixWord ++ tailWord_65085).sum := by decide
  have hdescent : baseEnd_65085 < baseStart_65085 := by decide
  rcases family_descends (prefixWord ++ tailWord_65085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65134 : List Nat := [4, 1, 2, 2, 4, 1, 2, 6]
def baseStart_65134 : Nat := 118140960795 + 65134 * 2 ^ 59
def prefixEnd_65134 : Nat := 4983230072969 + 3 ^ 40 * 65134 * 2
def baseEnd_65134 : Nat := 2477411033337288638923

theorem tailTrace_65134 : CollatzResearch.WordTrace tailWord_65134 prefixEnd_65134 2477411033337288638923 := by
  unfold tailWord_65134
  simp only [CollatzResearch.WordTrace]
  refine ⟨296954018254764605835307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1583754764025411231121637 296954018254764605835307)
  ·
    refine ⟨445431027382146908752961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296954018254764605835307 445431027382146908752961)
    ·
      refine ⟨334073270536610181564721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445431027382146908752961 334073270536610181564721)
      ·
        refine ⟨250554952902457636173541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334073270536610181564721 250554952902457636173541)
        ·
          refine ⟨46979053669210806782539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250554952902457636173541 46979053669210806782539)
          ·
            refine ⟨70468580503816210173809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46979053669210806782539 70468580503816210173809)
            ·
              refine ⟨52851435377862157630357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70468580503816210173809 52851435377862157630357)
              ·
                refine ⟨2477411033337288638923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52851435377862157630357 2477411033337288638923)
                ·
                  rfl

theorem cell22_65134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_65134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65134 prefixEnd_65134 := by exact prefixLift 65134
  have htrace : WordTrace (prefixWord ++ tailWord_65134) baseStart_65134 baseEnd_65134 := by
    simpa [prefixWord, tailWord_65134, baseEnd_65134] using wordTrace_append hprefix tailTrace_65134
  have hstable : (prefixWord ++ tailWord_65134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65134).length < 2 ^ (prefixWord ++ tailWord_65134).sum := by decide
  have hdescent : baseEnd_65134 < baseStart_65134 := by decide
  rcases family_descends (prefixWord ++ tailWord_65134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65149 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_65149 : Nat := 118140960795 + 65149 * 2 ^ 59
def prefixEnd_65149 : Nat := 4983230072969 + 3 ^ 40 * 65149 * 2
def baseEnd_65149 : Nat := 22301834106580558625261

theorem tailTrace_65149 : CollatzResearch.WordTrace tailWord_65149 prefixEnd_65149 22301834106580558625261 := by
  unfold tailWord_65149
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376179240983774408478501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1584119493989182938985667 2376179240983774408478501)
  ·
    refine ⟨445533607684457701589719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2376179240983774408478501 445533607684457701589719)
    ·
      refine ⟨668300411526686552384579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445533607684457701589719 668300411526686552384579)
      ·
        refine ⟨1002450617290029828576869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668300411526686552384579 1002450617290029828576869)
        ·
          refine ⟨187959490741880592858163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1002450617290029828576869 187959490741880592858163)
          ·
            refine ⟨281939236112820889287245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187959490741880592858163 281939236112820889287245)
            ·
              refine ⟨105727213542307833482717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281939236112820889287245 105727213542307833482717)
              ·
                refine ⟨39647705078365437556019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105727213542307833482717 39647705078365437556019)
                ·
                  refine ⟨59471557617548156334029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39647705078365437556019 59471557617548156334029)
                  ·
                    refine ⟨22301834106580558625261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59471557617548156334029 22301834106580558625261)
                    ·
                      rfl

theorem cell22_65149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_65149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65149 prefixEnd_65149 := by exact prefixLift 65149
  have htrace : WordTrace (prefixWord ++ tailWord_65149) baseStart_65149 baseEnd_65149 := by
    simpa [prefixWord, tailWord_65149, baseEnd_65149] using wordTrace_append hprefix tailTrace_65149
  have hstable : (prefixWord ++ tailWord_65149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65149).length < 2 ^ (prefixWord ++ tailWord_65149).sum := by decide
  have hdescent : baseEnd_65149 < baseStart_65149 := by decide
  rcases family_descends (prefixWord ++ tailWord_65149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65166 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_65166 : Nat := 118140960795 + 65166 * 2 ^ 59
def prefixEnd_65166 : Nat := 4983230072969 + 3 ^ 40 * 65166 * 2
def baseEnd_65166 : Nat := 22307653553998180950209

theorem tailTrace_65166 : CollatzResearch.WordTrace tailWord_65166 prefixEnd_65166 22307653553998180950209 := by
  unfold tailWord_65166
  simp only [CollatzResearch.WordTrace]
  refine ⟨297099910240273288980919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1584532854614790874564901 297099910240273288980919)
  ·
    refine ⟨445649865360409933471379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297099910240273288980919 445649865360409933471379)
    ·
      refine ⟨668474798040614900207069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445649865360409933471379 668474798040614900207069)
      ·
        refine ⟨250678049265230587577651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668474798040614900207069 250678049265230587577651)
        ·
          refine ⟨376017073897845881366477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250678049265230587577651 376017073897845881366477)
          ·
            refine ⟨141006402711692205512429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376017073897845881366477 141006402711692205512429)
            ·
              refine ⟨52877401016884577067161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141006402711692205512429 52877401016884577067161)
              ·
                refine ⟨39658050762663432800371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52877401016884577067161 39658050762663432800371)
                ·
                  refine ⟨59487076143995149200557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39658050762663432800371 59487076143995149200557)
                  ·
                    refine ⟨22307653553998180950209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59487076143995149200557 22307653553998180950209)
                    ·
                      rfl

theorem cell22_65166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_65166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65166 prefixEnd_65166 := by exact prefixLift 65166
  have htrace : WordTrace (prefixWord ++ tailWord_65166) baseStart_65166 baseEnd_65166 := by
    simpa [prefixWord, tailWord_65166, baseEnd_65166] using wordTrace_append hprefix tailTrace_65166
  have hstable : (prefixWord ++ tailWord_65166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65166).length < 2 ^ (prefixWord ++ tailWord_65166).sum := by decide
  have hdescent : baseEnd_65166 < baseStart_65166 := by decide
  rcases family_descends (prefixWord ++ tailWord_65166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65284 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_65284 : Nat := 118140960795 + 65284 * 2 ^ 59
def prefixEnd_65284 : Nat := 4983230072969 + 3 ^ 40 * 65284 * 2
def baseEnd_65284 : Nat := 22348047365485206499847

theorem tailTrace_65284 : CollatzResearch.WordTrace tailWord_65284 prefixEnd_65284 22348047365485206499847 := by
  unfold tailWord_65284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190551547747346232321453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1587402063663128309761937 1190551547747346232321453)
  ·
    refine ⟨446456830405254837120545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1190551547747346232321453 446456830405254837120545)
    ·
      refine ⟨334842622803941127840409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446456830405254837120545 334842622803941127840409)
      ·
        refine ⟨251131967102955845880307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334842622803941127840409 251131967102955845880307)
        ·
          refine ⟨376697950654433768820461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251131967102955845880307 376697950654433768820461)
          ·
            refine ⟨141261731495412663307673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376697950654433768820461 141261731495412663307673)
            ·
              refine ⟨105946298621559497480755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141261731495412663307673 105946298621559497480755)
              ·
                refine ⟨158919447932339246221133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105946298621559497480755 158919447932339246221133)
                ·
                  refine ⟨59594792974627217332925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158919447932339246221133 59594792974627217332925)
                  ·
                    refine ⟨22348047365485206499847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59594792974627217332925 22348047365485206499847)
                    ·
                      rfl

theorem cell22_65284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_65284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65284 prefixEnd_65284 := by exact prefixLift 65284
  have htrace : WordTrace (prefixWord ++ tailWord_65284) baseStart_65284 baseEnd_65284 := by
    simpa [prefixWord, tailWord_65284, baseEnd_65284] using wordTrace_append hprefix tailTrace_65284
  have hstable : (prefixWord ++ tailWord_65284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65284).length < 2 ^ (prefixWord ++ tailWord_65284).sum := by decide
  have hdescent : baseEnd_65284 < baseStart_65284 := by decide
  rcases family_descends (prefixWord ++ tailWord_65284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65370 : List Nat := [3, 1, 1, 2, 1, 3, 1, 10]
def baseStart_65370 : Nat := 118140960795 + 65370 * 2 ^ 59
def prefixEnd_65370 : Nat := 4983230072969 + 3 ^ 40 * 65370 * 2
def baseEnd_65370 : Nat := 2486387435889960983287

theorem tailTrace_65370 : CollatzResearch.WordTrace tailWord_65370 prefixEnd_65370 2486387435889960983287 := by
  unfold tailWord_65370
  simp only [CollatzResearch.WordTrace]
  refine ⟨596059943295782288068391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1589493182122086101515709 596059943295782288068391)
  ·
    refine ⟨894089914943673432102587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596059943295782288068391 894089914943673432102587)
    ·
      refine ⟨1341134872415510148153881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894089914943673432102587 1341134872415510148153881)
      ·
        refine ⟨1005851154311632611115411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1341134872415510148153881 1005851154311632611115411)
        ·
          refine ⟨1508776731467448916673117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005851154311632611115411 1508776731467448916673117)
          ·
            refine ⟨565791274300293343752419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508776731467448916673117 565791274300293343752419)
            ·
              refine ⟨848686911450440015628629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565791274300293343752419 848686911450440015628629)
              ·
                refine ⟨2486387435889960983287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 848686911450440015628629 2486387435889960983287)
                ·
                  rfl

theorem cell22_65370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_65370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65370 prefixEnd_65370 := by exact prefixLift 65370
  have htrace : WordTrace (prefixWord ++ tailWord_65370) baseStart_65370 baseEnd_65370 := by
    simpa [prefixWord, tailWord_65370, baseEnd_65370] using wordTrace_append hprefix tailTrace_65370
  have hstable : (prefixWord ++ tailWord_65370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65370).length < 2 ^ (prefixWord ++ tailWord_65370).sum := by decide
  have hdescent : baseEnd_65370 < baseStart_65370 := by decide
  rcases family_descends (prefixWord ++ tailWord_65370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65511 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 6]
def baseStart_65511 : Nat := 118140960795 + 65511 * 2 ^ 59
def prefixEnd_65511 : Nat := 4983230072969 + 3 ^ 40 * 65511 * 2
def baseEnd_65511 : Nat := 7475251368177427024717

theorem tailTrace_65511 : CollatzResearch.WordTrace tailWord_65511 prefixEnd_65511 7475251368177427024717 := by
  unfold tailWord_65511
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389382465672310233156387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1592921643781540155437591 2389382465672310233156387)
  ·
    refine ⟨3584073698508465349734581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2389382465672310233156387 3584073698508465349734581)
    ·
      refine ⟨336006909235168626537617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3584073698508465349734581 336006909235168626537617)
      ·
        refine ⟨252005181926376469903213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336006909235168626537617 252005181926376469903213)
        ·
          refine ⟨94501943222391176213705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252005181926376469903213 94501943222391176213705)
          ·
            refine ⟨70876457416793382160279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94501943222391176213705 70876457416793382160279)
            ·
              refine ⟨106314686125190073240419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70876457416793382160279 106314686125190073240419)
              ·
                refine ⟨159472029187785109860629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106314686125190073240419 159472029187785109860629)
                ·
                  refine ⟨7475251368177427024717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159472029187785109860629 7475251368177427024717)
                  ·
                    rfl

theorem cell22_65511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 6].length) (baseStart_65511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65511 prefixEnd_65511 := by exact prefixLift 65511
  have htrace : WordTrace (prefixWord ++ tailWord_65511) baseStart_65511 baseEnd_65511 := by
    simpa [prefixWord, tailWord_65511, baseEnd_65511] using wordTrace_append hprefix tailTrace_65511
  have hstable : (prefixWord ++ tailWord_65511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65511).length < 2 ^ (prefixWord ++ tailWord_65511).sum := by decide
  have hdescent : baseEnd_65511 < baseStart_65511 := by decide
  rcases family_descends (prefixWord ++ tailWord_65511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65556 : List Nat := [2, 4, 3, 2, 1, 10]
def baseStart_65556 : Nat := 118140960795 + 65556 * 2 ^ 59
def prefixEnd_65556 : Nat := 4983230072969 + 3 ^ 40 * 65556 * 2
def baseEnd_65556 : Nat := 277051339804532885173

theorem tailTrace_65556 : CollatzResearch.WordTrace tailWord_65556 prefixEnd_65556 277051339804532885173 := by
  unfold tailWord_65556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195511875254641459272261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1594015833672855279029681 1195511875254641459272261)
  ·
    refine ⟨224158476610245273613549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1195511875254641459272261 224158476610245273613549)
    ·
      refine ⟨84059428728841977605081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224158476610245273613549 84059428728841977605081)
      ·
        refine ⟨63044571546631483203811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84059428728841977605081 63044571546631483203811)
        ·
          refine ⟨94566857319947224805717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63044571546631483203811 94566857319947224805717)
          ·
            refine ⟨277051339804532885173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 94566857319947224805717 277051339804532885173)
            ·
              rfl

theorem cell22_65556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 10].length) (baseStart_65556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65556 prefixEnd_65556 := by exact prefixLift 65556
  have htrace : WordTrace (prefixWord ++ tailWord_65556) baseStart_65556 baseEnd_65556 := by
    simpa [prefixWord, tailWord_65556, baseEnd_65556] using wordTrace_append hprefix tailTrace_65556
  have hstable : (prefixWord ++ tailWord_65556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65556).length < 2 ^ (prefixWord ++ tailWord_65556).sum := by decide
  have hdescent : baseEnd_65556 < baseStart_65556 := by decide
  rcases family_descends (prefixWord ++ tailWord_65556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65584 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_65584 : Nat := 118140960795 + 65584 * 2 ^ 59
def prefixEnd_65584 : Nat := 4983230072969 + 3 ^ 40 * 65584 * 2
def baseEnd_65584 : Nat := 7483581165461474666309

theorem tailTrace_65584 : CollatzResearch.WordTrace tailWord_65584 prefixEnd_65584 7483581165461474666309 := by
  unfold tailWord_65584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196022497203921850281903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1594696662938562467042537 1196022497203921850281903)
  ·
    refine ⟨1794033745805882775422855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1196022497203921850281903 1794033745805882775422855)
    ·
      refine ⟨2691050618708824163134283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794033745805882775422855 2691050618708824163134283)
      ·
        refine ⟨4036575928063236244701425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691050618708824163134283 4036575928063236244701425)
        ·
          refine ⟨3027431946047427183526069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4036575928063236244701425 3027431946047427183526069)
          ·
            refine ⟨283821744941946298455569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3027431946047427183526069 283821744941946298455569)
            ·
              refine ⟨212866308706459723841677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283821744941946298455569 212866308706459723841677)
              ·
                refine ⟨79824865764922396440629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212866308706459723841677 79824865764922396440629)
                ·
                  refine ⟨7483581165461474666309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79824865764922396440629 7483581165461474666309)
                  ·
                    rfl

theorem cell22_65584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_65584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65584 prefixEnd_65584 := by exact prefixLift 65584
  have htrace : WordTrace (prefixWord ++ tailWord_65584) baseStart_65584 baseEnd_65584 := by
    simpa [prefixWord, tailWord_65584, baseEnd_65584] using wordTrace_append hprefix tailTrace_65584
  have hstable : (prefixWord ++ tailWord_65584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65584).length < 2 ^ (prefixWord ++ tailWord_65584).sum := by decide
  have hdescent : baseEnd_65584 < baseStart_65584 := by decide
  rcases family_descends (prefixWord ++ tailWord_65584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65618 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_65618 : Nat := 118140960795 + 65618 * 2 ^ 59
def prefixEnd_65618 : Nat := 4983230072969 + 3 ^ 40 * 65618 * 2
def baseEnd_65618 : Nat := 7487460797073222882941

theorem tailTrace_65618 : CollatzResearch.WordTrace tailWord_65618 prefixEnd_65618 7487460797073222882941 := by
  unfold tailWord_65618
  simp only [CollatzResearch.WordTrace]
  refine ⟨598321269071166876825377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1595523384189778338201005 598321269071166876825377)
  ·
    refine ⟨448740951803375157619033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 598321269071166876825377 448740951803375157619033)
    ·
      refine ⟨336555713852531368214275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448740951803375157619033 336555713852531368214275)
      ·
        refine ⟨504833570778797052321413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336555713852531368214275 504833570778797052321413)
        ·
          refine ⟨94656294521024447310265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504833570778797052321413 94656294521024447310265)
          ·
            refine ⟨70992220890768335482699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94656294521024447310265 70992220890768335482699)
            ·
              refine ⟨106488331336152503224049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70992220890768335482699 106488331336152503224049)
              ·
                refine ⟨79866248502114377418037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106488331336152503224049 79866248502114377418037)
                ·
                  refine ⟨7487460797073222882941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79866248502114377418037 7487460797073222882941)
                  ·
                    rfl

theorem cell22_65618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_65618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65618 prefixEnd_65618 := by exact prefixLift 65618
  have htrace : WordTrace (prefixWord ++ tailWord_65618) baseStart_65618 baseEnd_65618 := by
    simpa [prefixWord, tailWord_65618, baseEnd_65618] using wordTrace_append hprefix tailTrace_65618
  have hstable : (prefixWord ++ tailWord_65618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65618).length < 2 ^ (prefixWord ++ tailWord_65618).sum := by decide
  have hdescent : baseEnd_65618 < baseStart_65618 := by decide
  rcases family_descends (prefixWord ++ tailWord_65618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65622 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_65622 : Nat := 118140960795 + 65622 * 2 ^ 59
def prefixEnd_65622 : Nat := 4983230072969 + 3 ^ 40 * 65622 * 2
def baseEnd_65622 : Nat := 22463751672964991548811

theorem tailTrace_65622 : CollatzResearch.WordTrace tailWord_65622 prefixEnd_65622 22463751672964991548811 := by
  unfold tailWord_65622
  simp only [CollatzResearch.WordTrace]
  refine ⟨149589435516886011902945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1595620645513450793631413 149589435516886011902945)
  ·
    refine ⟨112192076637664508927209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149589435516886011902945 112192076637664508927209)
    ·
      refine ⟨84144057478248381695407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112192076637664508927209 84144057478248381695407)
      ·
        refine ⟨126216086217372572543111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84144057478248381695407 126216086217372572543111)
        ·
          refine ⟨189324129326058858814667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126216086217372572543111 189324129326058858814667)
          ·
            refine ⟨283986193989088288222001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189324129326058858814667 283986193989088288222001)
            ·
              refine ⟨212989645491816216166501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283986193989088288222001 212989645491816216166501)
              ·
                refine ⟨39935558529715540531219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212989645491816216166501 39935558529715540531219)
                ·
                  refine ⟨59903337794573310796829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39935558529715540531219 59903337794573310796829)
                  ·
                    refine ⟨22463751672964991548811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59903337794573310796829 22463751672964991548811)
                    ·
                      rfl

theorem cell22_65622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_65622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65622 prefixEnd_65622 := by exact prefixLift 65622
  have htrace : WordTrace (prefixWord ++ tailWord_65622) baseStart_65622 baseEnd_65622 := by
    simpa [prefixWord, tailWord_65622, baseEnd_65622] using wordTrace_append hprefix tailTrace_65622
  have hstable : (prefixWord ++ tailWord_65622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65622).length < 2 ^ (prefixWord ++ tailWord_65622).sum := by decide
  have hdescent : baseEnd_65622 < baseStart_65622 := by decide
  rcases family_descends (prefixWord ++ tailWord_65622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65661 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_65661 : Nat := 118140960795 + 65661 * 2 ^ 59
def prefixEnd_65661 : Nat := 4983230072969 + 3 ^ 40 * 65661 * 2
def baseEnd_65661 : Nat := 22477102169981889823691

theorem tailTrace_65661 : CollatzResearch.WordTrace tailWord_65661 prefixEnd_65661 22477102169981889823691 := by
  unfold tailWord_65661
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394853415128885851116837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1596568943419257234077891 2394853415128885851116837)
  ·
    refine ⟨449035015336666097084407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2394853415128885851116837 449035015336666097084407)
    ·
      refine ⟨673552523004999145626611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449035015336666097084407 673552523004999145626611)
      ·
        refine ⟨1010328784507498718439917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673552523004999145626611 1010328784507498718439917)
        ·
          refine ⟨378873294190312019414969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1010328784507498718439917 378873294190312019414969)
          ·
            refine ⟨284154970642734014561227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378873294190312019414969 284154970642734014561227)
            ·
              refine ⟨426232455964101021841841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284154970642734014561227 426232455964101021841841)
              ·
                refine ⟨319674341973075766381381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426232455964101021841841 319674341973075766381381)
                ·
                  refine ⟨59938939119951706196509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319674341973075766381381 59938939119951706196509)
                  ·
                    refine ⟨22477102169981889823691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59938939119951706196509 22477102169981889823691)
                    ·
                      rfl

theorem cell22_65661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_65661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65661 prefixEnd_65661 := by exact prefixLift 65661
  have htrace : WordTrace (prefixWord ++ tailWord_65661) baseStart_65661 baseEnd_65661 := by
    simpa [prefixWord, tailWord_65661, baseEnd_65661] using wordTrace_append hprefix tailTrace_65661
  have hstable : (prefixWord ++ tailWord_65661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65661).length < 2 ^ (prefixWord ++ tailWord_65661).sum := by decide
  have hdescent : baseEnd_65661 < baseStart_65661 := by decide
  rcases family_descends (prefixWord ++ tailWord_65661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65674 : List Nat := [3, 1, 2, 3, 1, 2, 10]
def baseStart_65674 : Nat := 118140960795 + 65674 * 2 ^ 59
def prefixEnd_65674 : Nat := 4983230072969 + 3 ^ 40 * 65674 * 2
def baseEnd_65674 : Nat := 832650086505710712913

theorem tailTrace_65674 : CollatzResearch.WordTrace tailWord_65674 prefixEnd_65674 832650086505710712913 := by
  unfold tailWord_65674
  simp only [CollatzResearch.WordTrace]
  refine ⟨598831891020447267835019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1596885042721192714226717 598831891020447267835019)
  ·
    refine ⟨898247836530670901752529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598831891020447267835019 898247836530670901752529)
    ·
      refine ⟨673685877398003176314397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 898247836530670901752529 673685877398003176314397)
      ·
        refine ⟨252632204024251191117899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673685877398003176314397 252632204024251191117899)
        ·
          refine ⟨378948306036376786676849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252632204024251191117899 378948306036376786676849)
          ·
            refine ⟨284211229527282590007637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378948306036376786676849 284211229527282590007637)
            ·
              refine ⟨832650086505710712913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 284211229527282590007637 832650086505710712913)
              ·
                rfl

theorem cell22_65674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 10].length) (baseStart_65674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65674 prefixEnd_65674 := by exact prefixLift 65674
  have htrace : WordTrace (prefixWord ++ tailWord_65674) baseStart_65674 baseEnd_65674 := by
    simpa [prefixWord, tailWord_65674, baseEnd_65674] using wordTrace_append hprefix tailTrace_65674
  have hstable : (prefixWord ++ tailWord_65674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65674).length < 2 ^ (prefixWord ++ tailWord_65674).sum := by decide
  have hdescent : baseEnd_65674 < baseStart_65674 := by decide
  rcases family_descends (prefixWord ++ tailWord_65674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65686 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_65686 : Nat := 118140960795 + 65686 * 2 ^ 59
def prefixEnd_65686 : Nat := 4983230072969 + 3 ^ 40 * 65686 * 2
def baseEnd_65686 : Nat := 7495220060296719316205

theorem tailTrace_65686 : CollatzResearch.WordTrace tailWord_65686 prefixEnd_65686 7495220060296719316205 := by
  unfold tailWord_65686
  simp only [CollatzResearch.WordTrace]
  refine ⟨149735327502394695048557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1597176826692210080517941 149735327502394695048557)
  ·
    refine ⟨56150747813398010643209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149735327502394695048557 56150747813398010643209)
    ·
      refine ⟨42113060860048507982407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56150747813398010643209 42113060860048507982407)
      ·
        refine ⟨63169591290072761973611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42113060860048507982407 63169591290072761973611)
        ·
          refine ⟨94754386935109142960417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63169591290072761973611 94754386935109142960417)
          ·
            refine ⟨71065790201331857220313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94754386935109142960417 71065790201331857220313)
            ·
              refine ⟨53299342650998892915235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71065790201331857220313 53299342650998892915235)
              ·
                refine ⟨79949013976498339372853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53299342650998892915235 79949013976498339372853)
                ·
                  refine ⟨7495220060296719316205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79949013976498339372853 7495220060296719316205)
                  ·
                    rfl

theorem cell22_65686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_65686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65686 prefixEnd_65686 := by exact prefixLift 65686
  have htrace : WordTrace (prefixWord ++ tailWord_65686) baseStart_65686 baseEnd_65686 := by
    simpa [prefixWord, tailWord_65686, baseEnd_65686] using wordTrace_append hprefix tailTrace_65686
  have hstable : (prefixWord ++ tailWord_65686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65686).length < 2 ^ (prefixWord ++ tailWord_65686).sum := by decide
  have hdescent : baseEnd_65686 < baseStart_65686 := by decide
  rcases family_descends (prefixWord ++ tailWord_65686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65695 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 2, 3]
def baseStart_65695 : Nat := 118140960795 + 65695 * 2 ^ 59
def prefixEnd_65695 : Nat := 4983230072969 + 3 ^ 40 * 65695 * 2
def baseEnd_65695 : Nat := 22488741064817134473587

theorem tailTrace_65695 : CollatzResearch.WordTrace tailWord_65695 prefixEnd_65695 22488741064817134473587 := by
  unfold tailWord_65695
  simp only [CollatzResearch.WordTrace]
  refine ⟨2396093497005709657854539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1597395664670473105236359 2396093497005709657854539)
  ·
    refine ⟨3594140245508564486781809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2396093497005709657854539 3594140245508564486781809)
    ·
      refine ⟨2695605184131423365086357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3594140245508564486781809 2695605184131423365086357)
      ·
        refine ⟨126356493006160470238423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2695605184131423365086357 126356493006160470238423)
        ·
          refine ⟨189534739509240705357635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126356493006160470238423 189534739509240705357635)
          ·
            refine ⟨284302109263861058036453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189534739509240705357635 284302109263861058036453)
            ·
              refine ⟨53306645486973948381835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284302109263861058036453 53306645486973948381835)
              ·
                refine ⟨79959968230460922572753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53306645486973948381835 79959968230460922572753)
                ·
                  refine ⟨59969976172845691929565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79959968230460922572753 59969976172845691929565)
                  ·
                    refine ⟨22488741064817134473587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59969976172845691929565 22488741064817134473587)
                    ·
                      rfl

theorem cell22_65695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_65695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65695 prefixEnd_65695 := by exact prefixLift 65695
  have htrace : WordTrace (prefixWord ++ tailWord_65695) baseStart_65695 baseEnd_65695 := by
    simpa [prefixWord, tailWord_65695, baseEnd_65695] using wordTrace_append hprefix tailTrace_65695
  have hstable : (prefixWord ++ tailWord_65695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65695).length < 2 ^ (prefixWord ++ tailWord_65695).sum := by decide
  have hdescent : baseEnd_65695 < baseStart_65695 := by decide
  rcases family_descends (prefixWord ++ tailWord_65695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65723 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 1, 3]
def baseStart_65723 : Nat := 118140960795 + 65723 * 2 ^ 59
def prefixEnd_65723 : Nat := 4983230072969 + 3 ^ 40 * 65723 * 2
def baseEnd_65723 : Nat := 22498326037034394773501

theorem tailTrace_65723 : CollatzResearch.WordTrace tailWord_65723 prefixEnd_65723 22498326037034394773501 := by
  unfold tailWord_65723
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397114740904270439873823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1598076493936180293249215 2397114740904270439873823)
  ·
    refine ⟨3595672111356405659810735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2397114740904270439873823 3595672111356405659810735)
    ·
      refine ⟨5393508167034608489716103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595672111356405659810735 5393508167034608489716103)
      ·
        refine ⟨8090262250551912734574155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393508167034608489716103 8090262250551912734574155)
        ·
          refine ⟨12135393375827869101861233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8090262250551912734574155 12135393375827869101861233)
          ·
            refine ⟨9101545031870901826395925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12135393375827869101861233 9101545031870901826395925)
            ·
              refine ⟨426634923368948523112309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9101545031870901826395925 426634923368948523112309)
              ·
                refine ⟨39997024065838924041779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426634923368948523112309 39997024065838924041779)
                ·
                  refine ⟨59995536098758386062669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39997024065838924041779 59995536098758386062669)
                  ·
                    refine ⟨22498326037034394773501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59995536098758386062669 22498326037034394773501)
                    ·
                      rfl

theorem cell22_65723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 1, 3].length) (baseStart_65723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65723 prefixEnd_65723 := by exact prefixLift 65723
  have htrace : WordTrace (prefixWord ++ tailWord_65723) baseStart_65723 baseEnd_65723 := by
    simpa [prefixWord, tailWord_65723, baseEnd_65723] using wordTrace_append hprefix tailTrace_65723
  have hstable : (prefixWord ++ tailWord_65723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65723).length < 2 ^ (prefixWord ++ tailWord_65723).sum := by decide
  have hdescent : baseEnd_65723 < baseStart_65723 := by decide
  rcases family_descends (prefixWord ++ tailWord_65723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65813 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_65813 : Nat := 118140960795 + 65813 * 2 ^ 59
def prefixEnd_65813 : Nat := 4983230072969 + 3 ^ 40 * 65813 * 2
def baseEnd_65813 : Nat := 22529134876304160023225

theorem tailTrace_65813 : CollatzResearch.WordTrace tailWord_65813 prefixEnd_65813 22529134876304160023225 := by
  unfold tailWord_65813
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400397310578215810650093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1600264873718810540433395 2400397310578215810650093)
  ·
    refine ⟨900148991466830928993785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2400397310578215810650093 900148991466830928993785)
    ·
      refine ⟨675111743600123196745339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 900148991466830928993785 675111743600123196745339)
      ·
        refine ⟨1012667615400184795118009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675111743600123196745339 1012667615400184795118009)
        ·
          refine ⟨759500711550138596338507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012667615400184795118009 759500711550138596338507)
          ·
            refine ⟨1139251067325207894507761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759500711550138596338507 1139251067325207894507761)
            ·
              refine ⟨854438300493905920880821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139251067325207894507761 854438300493905920880821)
              ·
                refine ⟨80103590671303680082577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 854438300493905920880821 80103590671303680082577)
                ·
                  refine ⟨60077693003477760061933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80103590671303680082577 60077693003477760061933)
                  ·
                    refine ⟨22529134876304160023225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60077693003477760061933 22529134876304160023225)
                    ·
                      rfl

theorem cell22_65813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_65813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65813 prefixEnd_65813 := by exact prefixLift 65813
  have htrace : WordTrace (prefixWord ++ tailWord_65813) baseStart_65813 baseEnd_65813 := by
    simpa [prefixWord, tailWord_65813, baseEnd_65813] using wordTrace_append hprefix tailTrace_65813
  have hstable : (prefixWord ++ tailWord_65813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65813).length < 2 ^ (prefixWord ++ tailWord_65813).sum := by decide
  have hdescent : baseEnd_65813 < baseStart_65813 := by decide
  rcases family_descends (prefixWord ++ tailWord_65813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65832 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 4]
def baseStart_65832 : Nat := 118140960795 + 65832 * 2 ^ 59
def prefixEnd_65832 : Nat := 4983230072969 + 3 ^ 40 * 65832 * 2
def baseEnd_65832 : Nat := 7511879654864814599389

theorem tailTrace_65832 : CollatzResearch.WordTrace tailWord_65832 prefixEnd_65832 7511879654864814599389 := by
  unfold tailWord_65832
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200545148754691027795875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1600726865006254703727833 1200545148754691027795875)
  ·
    refine ⟨1800817723132036541693813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1200545148754691027795875 1800817723132036541693813)
    ·
      refine ⟨168826661543628425783795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1800817723132036541693813 168826661543628425783795)
      ·
        refine ⟨253239992315442638675693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168826661543628425783795 253239992315442638675693)
        ·
          refine ⟨94964997118290989503385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253239992315442638675693 94964997118290989503385)
          ·
            refine ⟨71223747838718242127539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94964997118290989503385 71223747838718242127539)
            ·
              refine ⟨106835621758077363191309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71223747838718242127539 106835621758077363191309)
              ·
                refine ⟨40063358159279011196741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106835621758077363191309 40063358159279011196741)
                ·
                  refine ⟨7511879654864814599389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40063358159279011196741 7511879654864814599389)
                  ·
                    rfl

theorem cell22_65832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_65832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65832 prefixEnd_65832 := by exact prefixLift 65832
  have htrace : WordTrace (prefixWord ++ tailWord_65832) baseStart_65832 baseEnd_65832 := by
    simpa [prefixWord, tailWord_65832, baseEnd_65832] using wordTrace_append hprefix tailTrace_65832
  have hstable : (prefixWord ++ tailWord_65832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65832).length < 2 ^ (prefixWord ++ tailWord_65832).sum := by decide
  have hdescent : baseEnd_65832 < baseStart_65832 := by decide
  rcases family_descends (prefixWord ++ tailWord_65832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65860 : List Nat := [2, 3, 4, 1, 2, 1, 2, 7]
def baseStart_65860 : Nat := 118140960795 + 65860 * 2 ^ 59
def prefixEnd_65860 : Nat := 4983230072969 + 3 ^ 40 * 65860 * 2
def baseEnd_65860 : Nat := 2505024881867967122009

theorem tailTrace_65860 : CollatzResearch.WordTrace tailWord_65860 prefixEnd_65860 2505024881867967122009 := by
  unfold tailWord_65860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201055770703971418805517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1601407694271961891740689 1201055770703971418805517)
  ·
    refine ⟨450395914013989282052069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1201055770703971418805517 450395914013989282052069)
    ·
      refine ⟨84449233877622990384763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 450395914013989282052069 84449233877622990384763)
      ·
        refine ⟨126673850816434485577145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84449233877622990384763 126673850816434485577145)
        ·
          refine ⟨95005388112325864182859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126673850816434485577145 95005388112325864182859)
          ·
            refine ⟨142508082168488796274289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95005388112325864182859 142508082168488796274289)
            ·
              refine ⟨106881061626366597205717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142508082168488796274289 106881061626366597205717)
              ·
                refine ⟨2505024881867967122009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106881061626366597205717 2505024881867967122009)
                ·
                  rfl

theorem cell22_65860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_65860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65860 prefixEnd_65860 := by exact prefixLift 65860
  have htrace : WordTrace (prefixWord ++ tailWord_65860) baseStart_65860 baseEnd_65860 := by
    simpa [prefixWord, tailWord_65860, baseEnd_65860] using wordTrace_append hprefix tailTrace_65860
  have hstable : (prefixWord ++ tailWord_65860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65860).length < 2 ^ (prefixWord ++ tailWord_65860).sum := by decide
  have hdescent : baseEnd_65860 < baseStart_65860 := by decide
  rcases family_descends (prefixWord ++ tailWord_65860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65909 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_65909 : Nat := 118140960795 + 65909 * 2 ^ 59
def prefixEnd_65909 : Nat := 4983230072969 + 3 ^ 40 * 65909 * 2
def baseEnd_65909 : Nat := 22561997638191909622931

theorem tailTrace_65909 : CollatzResearch.WordTrace tailWord_65909 prefixEnd_65909 22561997638191909622931 := by
  unfold tailWord_65909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403898718230424206144781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1602599145486949470763187 2403898718230424206144781)
  ·
    refine ⟨901462019336409077304293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2403898718230424206144781 901462019336409077304293)
    ·
      refine ⟨169024128625576701994555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 901462019336409077304293 169024128625576701994555)
      ·
        refine ⟨253536192938365052991833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169024128625576701994555 253536192938365052991833)
        ·
          refine ⟨190152144703773789743875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253536192938365052991833 190152144703773789743875)
          ·
            refine ⟨285228217055660684615813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190152144703773789743875 285228217055660684615813)
            ·
              refine ⟨53480290697936378365465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 285228217055660684615813 53480290697936378365465)
              ·
                refine ⟨40110218023452283774099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53480290697936378365465 40110218023452283774099)
                ·
                  refine ⟨60165327035178425661149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40110218023452283774099 60165327035178425661149)
                  ·
                    refine ⟨22561997638191909622931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60165327035178425661149 22561997638191909622931)
                    ·
                      rfl

theorem cell22_65909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_65909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65909 prefixEnd_65909 := by exact prefixLift 65909
  have htrace : WordTrace (prefixWord ++ tailWord_65909) baseStart_65909 baseEnd_65909 := by
    simpa [prefixWord, tailWord_65909, baseEnd_65909] using wordTrace_append hprefix tailTrace_65909
  have hstable : (prefixWord ++ tailWord_65909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65909).length < 2 ^ (prefixWord ++ tailWord_65909).sum := by decide
  have hdescent : baseEnd_65909 < baseStart_65909 := by decide
  rcases family_descends (prefixWord ++ tailWord_65909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65952 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 1, 4]
def baseStart_65952 : Nat := 118140960795 + 65952 * 2 ^ 59
def prefixEnd_65952 : Nat := 4983230072969 + 3 ^ 40 * 65952 * 2
def baseEnd_65952 : Nat := 22576717416954130797799

theorem tailTrace_65952 : CollatzResearch.WordTrace tailWord_65952 prefixEnd_65952 22576717416954130797799 := by
  unfold tailWord_65952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202733528537321274980055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1603644704716428366640073 1202733528537321274980055)
  ·
    refine ⟨1804100292805981912470083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1202733528537321274980055 1804100292805981912470083)
    ·
      refine ⟨2706150439208972868705125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1804100292805981912470083 2706150439208972868705125)
      ·
        refine ⟨507403207351682412882211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2706150439208972868705125 507403207351682412882211)
        ·
          refine ⟨761104811027523619323317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507403207351682412882211 761104811027523619323317)
          ·
            refine ⟨71353576033830339311561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 761104811027523619323317 71353576033830339311561)
            ·
              refine ⟨53515182025372754483671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71353576033830339311561 53515182025372754483671)
              ·
                refine ⟨80272773038059131725507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53515182025372754483671 80272773038059131725507)
                ·
                  refine ⟨120409159557088697588261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80272773038059131725507 120409159557088697588261)
                  ·
                    refine ⟨22576717416954130797799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120409159557088697588261 22576717416954130797799)
                    ·
                      rfl

theorem cell22_65952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_65952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_65952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_65952 prefixEnd_65952 := by exact prefixLift 65952
  have htrace : WordTrace (prefixWord ++ tailWord_65952) baseStart_65952 baseEnd_65952 := by
    simpa [prefixWord, tailWord_65952, baseEnd_65952] using wordTrace_append hprefix tailTrace_65952
  have hstable : (prefixWord ++ tailWord_65952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65952).length < 2 ^ (prefixWord ++ tailWord_65952).sum := by decide
  have hdescent : baseEnd_65952 < baseStart_65952 := by decide
  rcases family_descends (prefixWord ++ tailWord_65952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66023 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 7]
def baseStart_66023 : Nat := 118140960795 + 66023 * 2 ^ 59
def prefixEnd_66023 : Nat := 4983230072969 + 3 ^ 40 * 66023 * 2
def baseEnd_66023 : Nat := 7533674055977870757527

theorem tailTrace_66023 : CollatzResearch.WordTrace tailWord_66023 prefixEnd_66023 7533674055977870757527 := by
  unfold tailWord_66023
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408056639817421675794723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1605371093211614450529815 2408056639817421675794723)
  ·
    refine ⟨3612084959726132513692085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2408056639817421675794723 3612084959726132513692085)
    ·
      refine ⟨338632964974324923158633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3612084959726132513692085 338632964974324923158633)
      ·
        refine ⟨253974723730743692368975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338632964974324923158633 253974723730743692368975)
        ·
          refine ⟨380962085596115538553463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253974723730743692368975 380962085596115538553463)
          ·
            refine ⟨571443128394173307830195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380962085596115538553463 571443128394173307830195)
            ·
              refine ⟨857164692591259961745293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571443128394173307830195 857164692591259961745293)
              ·
                refine ⟨321436759721722485654485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 857164692591259961745293 321436759721722485654485)
                ·
                  refine ⟨7533674055977870757527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 321436759721722485654485 7533674055977870757527)
                  ·
                    rfl

theorem cell22_66023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_66023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66023 prefixEnd_66023 := by exact prefixLift 66023
  have htrace : WordTrace (prefixWord ++ tailWord_66023) baseStart_66023 baseEnd_66023 := by
    simpa [prefixWord, tailWord_66023, baseEnd_66023] using wordTrace_append hprefix tailTrace_66023
  have hstable : (prefixWord ++ tailWord_66023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66023).length < 2 ^ (prefixWord ++ tailWord_66023).sum := by decide
  have hdescent : baseEnd_66023 < baseStart_66023 := by decide
  rcases family_descends (prefixWord ++ tailWord_66023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66102 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_66102 : Nat := 118140960795 + 66102 * 2 ^ 59
def prefixEnd_66102 : Nat := 4983230072969 + 3 ^ 40 * 66102 * 2
def baseEnd_66102 : Nat := 7542688494134579849113

theorem tailTrace_66102 : CollatzResearch.WordTrace tailWord_66102 prefixEnd_66102 7542688494134579849113 := by
  unfold tailWord_66102
  simp only [CollatzResearch.WordTrace]
  refine ⟨150683625408201135495035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1607292004354145445280373 150683625408201135495035)
  ·
    refine ⟨226025438112301703242553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150683625408201135495035 226025438112301703242553)
    ·
      refine ⟨169519078584226277431915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226025438112301703242553 169519078584226277431915)
      ·
        refine ⟨254278617876339416147873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169519078584226277431915 254278617876339416147873)
        ·
          refine ⟨190708963407254562110905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254278617876339416147873 190708963407254562110905)
          ·
            refine ⟨143031722555440921583179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190708963407254562110905 143031722555440921583179)
            ·
              refine ⟨214547583833161382374769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143031722555440921583179 214547583833161382374769)
              ·
                refine ⟨160910687874871036781077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214547583833161382374769 160910687874871036781077)
                ·
                  refine ⟨7542688494134579849113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160910687874871036781077 7542688494134579849113)
                  ·
                    rfl

theorem cell22_66102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_66102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66102 prefixEnd_66102 := by exact prefixLift 66102
  have htrace : WordTrace (prefixWord ++ tailWord_66102) baseStart_66102 baseEnd_66102 := by
    simpa [prefixWord, tailWord_66102, baseEnd_66102] using wordTrace_append hprefix tailTrace_66102
  have hstable : (prefixWord ++ tailWord_66102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66102).length < 2 ^ (prefixWord ++ tailWord_66102).sum := by decide
  have hdescent : baseEnd_66102 < baseStart_66102 := by decide
  rcases family_descends (prefixWord ++ tailWord_66102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66143 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_66143 : Nat := 118140960795 + 66143 * 2 ^ 59
def prefixEnd_66143 : Nat := 4983230072969 + 3 ^ 40 * 66143 * 2
def baseEnd_66143 : Nat := 22642100620293299272213

theorem tailTrace_66143 : CollatzResearch.WordTrace tailWord_66143 prefixEnd_66143 22642100620293299272213 := by
  unfold tailWord_66143
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412433399382682170163083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1608288932921788113442055 2412433399382682170163083)
  ·
    refine ⟨3618650099074023255244625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2412433399382682170163083 3618650099074023255244625)
    ·
      refine ⟨2713987574305517441433469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3618650099074023255244625 2713987574305517441433469)
      ·
        refine ⟨1017745340364569040537551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2713987574305517441433469 1017745340364569040537551)
        ·
          refine ⟨1526618010546853560806327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017745340364569040537551 1526618010546853560806327)
          ·
            refine ⟨2289927015820280341209491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526618010546853560806327 2289927015820280341209491)
            ·
              refine ⟨3434890523730420511814237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2289927015820280341209491 3434890523730420511814237)
              ·
                refine ⟨1288083946398907691930339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3434890523730420511814237 1288083946398907691930339)
                ·
                  refine ⟨1932125919598361537895509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1288083946398907691930339 1932125919598361537895509)
                  ·
                    refine ⟨22642100620293299272213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1932125919598361537895509 22642100620293299272213)
                    ·
                      rfl

theorem cell22_66143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_66143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66143 prefixEnd_66143 := by exact prefixLift 66143
  have htrace : WordTrace (prefixWord ++ tailWord_66143) baseStart_66143 baseEnd_66143 := by
    simpa [prefixWord, tailWord_66143, baseEnd_66143] using wordTrace_append hprefix tailTrace_66143
  have hstable : (prefixWord ++ tailWord_66143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66143).length < 2 ^ (prefixWord ++ tailWord_66143).sum := by decide
  have hdescent : baseEnd_66143 < baseStart_66143 := by decide
  rcases family_descends (prefixWord ++ tailWord_66143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66179 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 1, 3]
def baseStart_66179 : Nat := 118140960795 + 66179 * 2 ^ 59
def prefixEnd_66179 : Nat := 4983230072969 + 3 ^ 40 * 66179 * 2
def baseEnd_66179 : Nat := 22654424156001205372103

theorem tailTrace_66179 : CollatzResearch.WordTrace tailWord_66179 prefixEnd_66179 22654424156001205372103 := by
  unfold tailWord_66179
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413746427252260318473591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1609164284834840212315727 2413746427252260318473591)
  ·
    refine ⟨3620619640878390477710387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2413746427252260318473591 3620619640878390477710387)
    ·
      refine ⟨5430929461317585716565581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620619640878390477710387 5430929461317585716565581)
      ·
        refine ⟨2036598547994094643712093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5430929461317585716565581 2036598547994094643712093)
        ·
          refine ⟨763724455497785491392035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2036598547994094643712093 763724455497785491392035)
          ·
            refine ⟨1145586683246678237088053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763724455497785491392035 1145586683246678237088053)
            ·
              refine ⟨107398751554376084727005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1145586683246678237088053 107398751554376084727005)
              ·
                refine ⟨40274531832891031772627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107398751554376084727005 40274531832891031772627)
                ·
                  refine ⟨60411797749336547658941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40274531832891031772627 60411797749336547658941)
                  ·
                    refine ⟨22654424156001205372103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60411797749336547658941 22654424156001205372103)
                    ·
                      rfl

theorem cell22_66179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 3].length) (baseStart_66179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66179 prefixEnd_66179 := by exact prefixLift 66179
  have htrace : WordTrace (prefixWord ++ tailWord_66179) baseStart_66179 baseEnd_66179 := by
    simpa [prefixWord, tailWord_66179, baseEnd_66179] using wordTrace_append hprefix tailTrace_66179
  have hstable : (prefixWord ++ tailWord_66179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66179).length < 2 ^ (prefixWord ++ tailWord_66179).sum := by decide
  have hdescent : baseEnd_66179 < baseStart_66179 := by decide
  rcases family_descends (prefixWord ++ tailWord_66179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66196 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_66196 : Nat := 118140960795 + 66196 * 2 ^ 59
def prefixEnd_66196 : Nat := 4983230072969 + 3 ^ 40 * 66196 * 2
def baseEnd_66196 : Nat := 22660243603418827697051

theorem tailTrace_66196 : CollatzResearch.WordTrace tailWord_66196 prefixEnd_66196 22660243603418827697051 := by
  unfold tailWord_66196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207183234095336110921221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1609577645460448147894961 1207183234095336110921221)
  ·
    refine ⟨226346856392875520797729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1207183234095336110921221 226346856392875520797729)
    ·
      refine ⟨169760142294656640598297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226346856392875520797729 169760142294656640598297)
      ·
        refine ⟨127320106720992480448723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169760142294656640598297 127320106720992480448723)
        ·
          refine ⟨190980160081488720673085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127320106720992480448723 190980160081488720673085)
          ·
            refine ⟨71617560030558270252407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190980160081488720673085 71617560030558270252407)
            ·
              refine ⟨107426340045837405378611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71617560030558270252407 107426340045837405378611)
              ·
                refine ⟨161139510068756108067917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107426340045837405378611 161139510068756108067917)
                ·
                  refine ⟨60427316275783540525469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161139510068756108067917 60427316275783540525469)
                  ·
                    refine ⟨22660243603418827697051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60427316275783540525469 22660243603418827697051)
                    ·
                      rfl

theorem cell22_66196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_66196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66196 prefixEnd_66196 := by exact prefixLift 66196
  have htrace : WordTrace (prefixWord ++ tailWord_66196) baseStart_66196 baseEnd_66196 := by
    simpa [prefixWord, tailWord_66196, baseEnd_66196] using wordTrace_append hprefix tailTrace_66196
  have hstable : (prefixWord ++ tailWord_66196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66196).length < 2 ^ (prefixWord ++ tailWord_66196).sum := by decide
  have hdescent : baseEnd_66196 < baseStart_66196 := by decide
  rcases family_descends (prefixWord ++ tailWord_66196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66239 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 1, 4]
def baseStart_66239 : Nat := 118140960795 + 66239 * 2 ^ 59
def prefixEnd_66239 : Nat := 4983230072969 + 3 ^ 40 * 66239 * 2
def baseEnd_66239 : Nat := 22674963382181048871919

theorem tailTrace_66239 : CollatzResearch.WordTrace tailWord_66239 prefixEnd_66239 22674963382181048871919 := by
  unfold tailWord_66239
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415934807034890565657771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1610623204689927043771847 2415934807034890565657771)
  ·
    refine ⟨3623902210552335848486657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2415934807034890565657771 3623902210552335848486657)
    ·
      refine ⟨2717926657914251886364993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3623902210552335848486657 2717926657914251886364993)
      ·
        refine ⟨2038444993435688914773745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2717926657914251886364993 2038444993435688914773745)
        ·
          refine ⟨1528833745076766686080309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2038444993435688914773745 1528833745076766686080309)
          ·
            refine ⟨143328163600946876820029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1528833745076766686080309 143328163600946876820029)
            ·
              refine ⟨53748061350355078807511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143328163600946876820029 53748061350355078807511)
              ·
                refine ⟨80622092025532618211267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53748061350355078807511 80622092025532618211267)
                ·
                  refine ⟨120933138038298927316901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80622092025532618211267 120933138038298927316901)
                  ·
                    refine ⟨22674963382181048871919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120933138038298927316901 22674963382181048871919)
                    ·
                      rfl

theorem cell22_66239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_66239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66239 prefixEnd_66239 := by exact prefixLift 66239
  have htrace : WordTrace (prefixWord ++ tailWord_66239) baseStart_66239 baseEnd_66239 := by
    simpa [prefixWord, tailWord_66239, baseEnd_66239] using wordTrace_append hprefix tailTrace_66239
  have hstable : (prefixWord ++ tailWord_66239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66239).length < 2 ^ (prefixWord ++ tailWord_66239).sum := by decide
  have hdescent : baseEnd_66239 < baseStart_66239 := by decide
  rcases family_descends (prefixWord ++ tailWord_66239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66254 : List Nat := [4, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_66254 : Nat := 118140960795 + 66254 * 2 ^ 59
def prefixEnd_66254 : Nat := 4983230072969 + 3 ^ 40 * 66254 * 2
def baseEnd_66254 : Nat := 7560032729575336582291

theorem tailTrace_66254 : CollatzResearch.WordTrace tailWord_66254 prefixEnd_66254 7560032729575336582291 := by
  unfold tailWord_66254
  simp only [CollatzResearch.WordTrace]
  refine ⟨302060237747568515931727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1610987934653698751635877 302060237747568515931727)
  ·
    refine ⟨453090356621352773897591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302060237747568515931727 453090356621352773897591)
    ·
      refine ⟨679635534932029160846387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453090356621352773897591 679635534932029160846387)
      ·
        refine ⟨1019453302398043741269581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679635534932029160846387 1019453302398043741269581)
        ·
          refine ⟨382294988399266402976093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1019453302398043741269581 382294988399266402976093)
          ·
            refine ⟨143360620649724901116035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382294988399266402976093 143360620649724901116035)
            ·
              refine ⟨215040930974587351674053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143360620649724901116035 215040930974587351674053)
              ·
                refine ⟨40320174557735128438885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215040930974587351674053 40320174557735128438885)
                ·
                  refine ⟨7560032729575336582291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40320174557735128438885 7560032729575336582291)
                  ·
                    rfl

theorem cell22_66254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_66254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66254 prefixEnd_66254 := by exact prefixLift 66254
  have htrace : WordTrace (prefixWord ++ tailWord_66254) baseStart_66254 baseEnd_66254 := by
    simpa [prefixWord, tailWord_66254, baseEnd_66254] using wordTrace_append hprefix tailTrace_66254
  have hstable : (prefixWord ++ tailWord_66254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66254).length < 2 ^ (prefixWord ++ tailWord_66254).sum := by decide
  have hdescent : baseEnd_66254 < baseStart_66254 := by decide
  rcases family_descends (prefixWord ++ tailWord_66254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66314 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_66314 : Nat := 118140960795 + 66314 * 2 ^ 59
def prefixEnd_66314 : Nat := 4983230072969 + 3 ^ 40 * 66314 * 2
def baseEnd_66314 : Nat := 22700637414905853246689

theorem tailTrace_66314 : CollatzResearch.WordTrace tailWord_66314 prefixEnd_66314 22700637414905853246689 := by
  unfold tailWord_66314
  simp only [CollatzResearch.WordTrace]
  refine ⟨604667570440794593659499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1612446854508785583091997 604667570440794593659499)
  ·
    refine ⟨907001355661191890489249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 604667570440794593659499 907001355661191890489249)
    ·
      refine ⟨680251016745893917866937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907001355661191890489249 680251016745893917866937)
      ·
        refine ⟨510188262559420438400203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680251016745893917866937 510188262559420438400203)
        ·
          refine ⟨765282393839130657600305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510188262559420438400203 765282393839130657600305)
          ·
            refine ⟨573961795379347993200229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765282393839130657600305 573961795379347993200229)
            ·
              refine ⟨107617836633627748725043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573961795379347993200229 107617836633627748725043)
              ·
                refine ⟨161426754950441623087565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107617836633627748725043 161426754950441623087565)
                ·
                  refine ⟨60535033106415608657837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161426754950441623087565 60535033106415608657837)
                  ·
                    refine ⟨22700637414905853246689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60535033106415608657837 22700637414905853246689)
                    ·
                      rfl

theorem cell22_66314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_66314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66314 prefixEnd_66314 := by exact prefixLift 66314
  have htrace : WordTrace (prefixWord ++ tailWord_66314) baseStart_66314 baseEnd_66314 := by
    simpa [prefixWord, tailWord_66314, baseEnd_66314] using wordTrace_append hprefix tailTrace_66314
  have hstable : (prefixWord ++ tailWord_66314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66314).length < 2 ^ (prefixWord ++ tailWord_66314).sum := by decide
  have hdescent : baseEnd_66314 < baseStart_66314 := by decide
  rcases family_descends (prefixWord ++ tailWord_66314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66333 : List Nat := [1, 4, 2, 4, 2, 1, 2, 6]
def baseStart_66333 : Nat := 118140960795 + 66333 * 2 ^ 59
def prefixEnd_66333 : Nat := 4983230072969 + 3 ^ 40 * 66333 * 2
def baseEnd_66333 : Nat := 2523015722577348557959

theorem tailTrace_66333 : CollatzResearch.WordTrace tailWord_66333 prefixEnd_66333 2523015722577348557959 := by
  unfold tailWord_66333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419363268694344619579653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1612908845796229746386435 2419363268694344619579653)
  ·
    refine ⟨453630612880189616171185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2419363268694344619579653 453630612880189616171185)
    ·
      refine ⟨340222959660142212128389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453630612880189616171185 340222959660142212128389)
      ·
        refine ⟨63791804936276664774073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340222959660142212128389 63791804936276664774073)
        ·
          refine ⟨47843853702207498580555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63791804936276664774073 47843853702207498580555)
          ·
            refine ⟨71765780553311247870833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47843853702207498580555 71765780553311247870833)
            ·
              refine ⟨53824335414983435903125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71765780553311247870833 53824335414983435903125)
              ·
                refine ⟨2523015722577348557959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53824335414983435903125 2523015722577348557959)
                ·
                  rfl

theorem cell22_66333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 6].length) (baseStart_66333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66333 prefixEnd_66333 := by exact prefixLift 66333
  have htrace : WordTrace (prefixWord ++ tailWord_66333) baseStart_66333 baseEnd_66333 := by
    simpa [prefixWord, tailWord_66333, baseEnd_66333] using wordTrace_append hprefix tailTrace_66333
  have hstable : (prefixWord ++ tailWord_66333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66333).length < 2 ^ (prefixWord ++ tailWord_66333).sum := by decide
  have hdescent : baseEnd_66333 < baseStart_66333 := by decide
  rcases family_descends (prefixWord ++ tailWord_66333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66365 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_66365 : Nat := 118140960795 + 66365 * 2 ^ 59
def prefixEnd_66365 : Nat := 4983230072969 + 3 ^ 40 * 66365 * 2
def baseEnd_66365 : Nat := 22718095757158720221533

theorem tailTrace_66365 : CollatzResearch.WordTrace tailWord_66365 prefixEnd_66365 22718095757158720221533 := by
  unfold tailWord_66365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420530404578414084744549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1613686936385609389829699 2420530404578414084744549)
  ·
    refine ⟨453849450858452640889603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2420530404578414084744549 453849450858452640889603)
    ·
      refine ⟨680774176287678961334405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453849450858452640889603 680774176287678961334405)
      ·
        refine ⟨127645158053939805250201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 680774176287678961334405 127645158053939805250201)
        ·
          refine ⟨95733868540454853937651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127645158053939805250201 95733868540454853937651)
          ·
            refine ⟨143600802810682280906477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95733868540454853937651 143600802810682280906477)
            ·
              refine ⟨53850301054005855339929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143600802810682280906477 53850301054005855339929)
              ·
                refine ⟨40387725790504391504947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53850301054005855339929 40387725790504391504947)
                ·
                  refine ⟨60581588685756587257421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40387725790504391504947 60581588685756587257421)
                  ·
                    refine ⟨22718095757158720221533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60581588685756587257421 22718095757158720221533)
                    ·
                      rfl

theorem cell22_66365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_66365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66365 prefixEnd_66365 := by exact prefixLift 66365
  have htrace : WordTrace (prefixWord ++ tailWord_66365) baseStart_66365 baseEnd_66365 := by
    simpa [prefixWord, tailWord_66365, baseEnd_66365] using wordTrace_append hprefix tailTrace_66365
  have hstable : (prefixWord ++ tailWord_66365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66365).length < 2 ^ (prefixWord ++ tailWord_66365).sum := by decide
  have hdescent : baseEnd_66365 < baseStart_66365 := by decide
  rcases family_descends (prefixWord ++ tailWord_66365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66391 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 1, 4]
def baseStart_66391 : Nat := 118140960795 + 66391 * 2 ^ 59
def prefixEnd_66391 : Nat := 4983230072969 + 3 ^ 40 * 66391 * 2
def baseEnd_66391 : Nat := 22726996088503319071453

theorem tailTrace_66391 : CollatzResearch.WordTrace tailWord_66391 prefixEnd_66391 22726996088503319071453 := by
  unfold tailWord_66391
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421478702484220525191027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1614319134989480350127351 2421478702484220525191027)
  ·
    refine ⟨3632218053726330787786541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421478702484220525191027 3632218053726330787786541)
    ·
      refine ⟨1362081770147374045419953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3632218053726330787786541 1362081770147374045419953)
      ·
        refine ⟨1021561327610530534064965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1362081770147374045419953 1021561327610530534064965)
        ·
          refine ⟨191542748926974475137181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1021561327610530534064965 191542748926974475137181)
          ·
            refine ⟨71828530847615428176443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191542748926974475137181 71828530847615428176443)
            ·
              refine ⟨107742796271423142264665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71828530847615428176443 107742796271423142264665)
              ·
                refine ⟨80807097203567356698499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107742796271423142264665 80807097203567356698499)
                ·
                  refine ⟨121210645805351035047749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80807097203567356698499 121210645805351035047749)
                  ·
                    refine ⟨22726996088503319071453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121210645805351035047749 22726996088503319071453)
                    ·
                      rfl

theorem cell22_66391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_66391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66391 prefixEnd_66391 := by exact prefixLift 66391
  have htrace : WordTrace (prefixWord ++ tailWord_66391) baseStart_66391 baseEnd_66391 := by
    simpa [prefixWord, tailWord_66391, baseEnd_66391] using wordTrace_append hprefix tailTrace_66391
  have hstable : (prefixWord ++ tailWord_66391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66391).length < 2 ^ (prefixWord ++ tailWord_66391).sum := by decide
  have hdescent : baseEnd_66391 < baseStart_66391 := by decide
  rcases family_descends (prefixWord ++ tailWord_66391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66404 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_66404 : Nat := 118140960795 + 66404 * 2 ^ 59
def prefixEnd_66404 : Nat := 4983230072969 + 3 ^ 40 * 66404 * 2
def baseEnd_66404 : Nat := 22731446254175618496413

theorem tailTrace_66404 : CollatzResearch.WordTrace tailWord_66404 prefixEnd_66404 22731446254175618496413 := by
  unfold tailWord_66404
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210976425718561872707133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1614635234291415830276177 1210976425718561872707133)
  ·
    refine ⟨454116159644460702265175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1210976425718561872707133 454116159644460702265175)
    ·
      refine ⟨681174239466691053397763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454116159644460702265175 681174239466691053397763)
      ·
        refine ⟨1021761359200036580096645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681174239466691053397763 1021761359200036580096645)
        ·
          refine ⟨191580254850006858768121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1021761359200036580096645 191580254850006858768121)
          ·
            refine ⟨143685191137505144076091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191580254850006858768121 143685191137505144076091)
            ·
              refine ⟨215527786706257716114137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143685191137505144076091 215527786706257716114137)
              ·
                refine ⟨161645840029693287085603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215527786706257716114137 161645840029693287085603)
                ·
                  refine ⟨242468760044539930628405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161645840029693287085603 242468760044539930628405)
                  ·
                    refine ⟨22731446254175618496413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 242468760044539930628405 22731446254175618496413)
                    ·
                      rfl

theorem cell22_66404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_66404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66404 prefixEnd_66404 := by exact prefixLift 66404
  have htrace : WordTrace (prefixWord ++ tailWord_66404) baseStart_66404 baseEnd_66404 := by
    simpa [prefixWord, tailWord_66404, baseEnd_66404] using wordTrace_append hprefix tailTrace_66404
  have hstable : (prefixWord ++ tailWord_66404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66404).length < 2 ^ (prefixWord ++ tailWord_66404).sum := by decide
  have hdescent : baseEnd_66404 < baseStart_66404 := by decide
  rcases family_descends (prefixWord ++ tailWord_66404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66421 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 2, 3]
def baseStart_66421 : Nat := 118140960795 + 66421 * 2 ^ 59
def prefixEnd_66421 : Nat := 4983230072969 + 3 ^ 40 * 66421 * 2
def baseEnd_66421 : Nat := 22737265701593240821361

theorem tailTrace_66421 : CollatzResearch.WordTrace tailWord_66421 prefixEnd_66421 22737265701593240821361 := by
  unfold tailWord_66421
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422572892375535648783117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1615048594917023765855411 2422572892375535648783117)
  ·
    refine ⟨908464834640825868293669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2422572892375535648783117 908464834640825868293669)
    ·
      refine ⟨170337156495154850305063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 908464834640825868293669 170337156495154850305063)
      ·
        refine ⟨255505734742732275457595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170337156495154850305063 255505734742732275457595)
        ·
          refine ⟨383258602114098413186393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255505734742732275457595 383258602114098413186393)
          ·
            refine ⟨287443951585573809889795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383258602114098413186393 287443951585573809889795)
            ·
              refine ⟨431165927378360714834693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287443951585573809889795 431165927378360714834693)
              ·
                refine ⟨80843611383442634031505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 431165927378360714834693 80843611383442634031505)
                ·
                  refine ⟨60632708537581975523629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80843611383442634031505 60632708537581975523629)
                  ·
                    refine ⟨22737265701593240821361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60632708537581975523629 22737265701593240821361)
                    ·
                      rfl

theorem cell22_66421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_66421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66421 prefixEnd_66421 := by exact prefixLift 66421
  have htrace : WordTrace (prefixWord ++ tailWord_66421) baseStart_66421 baseEnd_66421 := by
    simpa [prefixWord, tailWord_66421, baseEnd_66421] using wordTrace_append hprefix tailTrace_66421
  have hstable : (prefixWord ++ tailWord_66421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66421).length < 2 ^ (prefixWord ++ tailWord_66421).sum := by decide
  have hdescent : baseEnd_66421 < baseStart_66421 := by decide
  rcases family_descends (prefixWord ++ tailWord_66421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66494 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_66494 : Nat := 118140960795 + 66494 * 2 ^ 59
def prefixEnd_66494 : Nat := 4983230072969 + 3 ^ 40 * 66494 * 2
def baseEnd_66494 : Nat := 22762255093445383746137

theorem tailTrace_66494 : CollatzResearch.WordTrace tailWord_66494 prefixEnd_66494 22762255093445383746137 := by
  unfold tailWord_66494
  simp only [CollatzResearch.WordTrace]
  refine ⟨303154427638883639523817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1616823614074046077460357 303154427638883639523817)
  ·
    refine ⟨227365820729162729642863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303154427638883639523817 227365820729162729642863)
    ·
      refine ⟨341048731093744094464295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227365820729162729642863 341048731093744094464295)
      ·
        refine ⟨511573096640616141696443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341048731093744094464295 511573096640616141696443)
        ·
          refine ⟨767359644960924212544665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511573096640616141696443 767359644960924212544665)
          ·
            refine ⟨575519733720693159408499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767359644960924212544665 575519733720693159408499)
            ·
              refine ⟨863279600581039739112749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575519733720693159408499 863279600581039739112749)
              ·
                refine ⟨323729850217889902167281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863279600581039739112749 323729850217889902167281)
                ·
                  refine ⟨242797387663417426625461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 323729850217889902167281 242797387663417426625461)
                  ·
                    refine ⟨22762255093445383746137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 242797387663417426625461 22762255093445383746137)
                    ·
                      rfl

theorem cell22_66494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_66494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66494 prefixEnd_66494 := by exact prefixLift 66494
  have htrace : WordTrace (prefixWord ++ tailWord_66494) baseStart_66494 baseEnd_66494 := by
    simpa [prefixWord, tailWord_66494, baseEnd_66494] using wordTrace_append hprefix tailTrace_66494
  have hstable : (prefixWord ++ tailWord_66494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66494).length < 2 ^ (prefixWord ++ tailWord_66494).sum := by decide
  have hdescent : baseEnd_66494 < baseStart_66494 := by decide
  rcases family_descends (prefixWord ++ tailWord_66494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66496 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 5]
def baseStart_66496 : Nat := 118140960795 + 66496 * 2 ^ 59
def prefixEnd_66496 : Nat := 4983230072969 + 3 ^ 40 * 66496 * 2
def baseEnd_66496 : Nat := 7587646578106015065377

theorem tailTrace_66496 : CollatzResearch.WordTrace tailWord_66496 prefixEnd_66496 7587646578106015065377 := by
  unfold tailWord_66496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212654183551911728881671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1616872244735882305175561 1212654183551911728881671)
  ·
    refine ⟨1818981275327867593322507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1212654183551911728881671 1818981275327867593322507)
    ·
      refine ⟨2728471912991801389983761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818981275327867593322507 2728471912991801389983761)
      ·
        refine ⟨2046353934743851042487821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2728471912991801389983761 2046353934743851042487821)
        ·
          refine ⟨767382725528944140932933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2046353934743851042487821 767382725528944140932933)
          ·
            refine ⟨143884261036677026424925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 767382725528944140932933 143884261036677026424925)
            ·
              refine ⟨53956597888753884909347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143884261036677026424925 53956597888753884909347)
              ·
                refine ⟨80934896833130827364021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53956597888753884909347 80934896833130827364021)
                ·
                  refine ⟨7587646578106015065377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80934896833130827364021 7587646578106015065377)
                  ·
                    rfl

theorem cell22_66496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_66496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66496 prefixEnd_66496 := by exact prefixLift 66496
  have htrace : WordTrace (prefixWord ++ tailWord_66496) baseStart_66496 baseEnd_66496 := by
    simpa [prefixWord, tailWord_66496, baseEnd_66496] using wordTrace_append hprefix tailTrace_66496
  have hstable : (prefixWord ++ tailWord_66496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66496).length < 2 ^ (prefixWord ++ tailWord_66496).sum := by decide
  have hdescent : baseEnd_66496 < baseStart_66496 := by decide
  rcases family_descends (prefixWord ++ tailWord_66496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66517 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 1, 3]
def baseStart_66517 : Nat := 118140960795 + 66517 * 2 ^ 59
def prefixEnd_66517 : Nat := 4983230072969 + 3 ^ 40 * 66517 * 2
def baseEnd_66517 : Nat := 22770128463480990421067

theorem tailTrace_66517 : CollatzResearch.WordTrace tailWord_66517 prefixEnd_66517 22770128463480990421067 := by
  unfold tailWord_66517
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426074300027744044277805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1617382866685162696185203 2426074300027744044277805)
  ·
    refine ⟨909777862510404016604177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2426074300027744044277805 909777862510404016604177)
    ·
      refine ⟨682333396882803012453133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 909777862510404016604177 682333396882803012453133)
      ·
        refine ⟨255875023831051129669925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 682333396882803012453133 255875023831051129669925)
        ·
          refine ⟨47976566968322086813111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255875023831051129669925 47976566968322086813111)
          ·
            refine ⟨71964850452483130219667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47976566968322086813111 71964850452483130219667)
            ·
              refine ⟨107947275678724695329501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71964850452483130219667 107947275678724695329501)
              ·
                refine ⟨40480228379521760748563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107947275678724695329501 40480228379521760748563)
                ·
                  refine ⟨60720342569282641122845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40480228379521760748563 60720342569282641122845)
                  ·
                    refine ⟨22770128463480990421067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60720342569282641122845 22770128463480990421067)
                    ·
                      rfl

theorem cell22_66517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_66517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66517 prefixEnd_66517 := by exact prefixLift 66517
  have htrace : WordTrace (prefixWord ++ tailWord_66517) baseStart_66517 baseEnd_66517 := by
    simpa [prefixWord, tailWord_66517, baseEnd_66517] using wordTrace_append hprefix tailTrace_66517
  have hstable : (prefixWord ++ tailWord_66517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66517).length < 2 ^ (prefixWord ++ tailWord_66517).sum := by decide
  have hdescent : baseEnd_66517 < baseStart_66517 := by decide
  rcases family_descends (prefixWord ++ tailWord_66517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66537 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_66537 : Nat := 118140960795 + 66537 * 2 ^ 59
def prefixEnd_66537 : Nat := 4983230072969 + 3 ^ 40 * 66537 * 2
def baseEnd_66537 : Nat := 22776974872207604921005

theorem tailTrace_66537 : CollatzResearch.WordTrace tailWord_66537 prefixEnd_66537 22776974872207604921005 := by
  unfold tailWord_66537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426803759955287460005865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1617869173303524973337243 2426803759955287460005865)
  ·
    refine ⟨1820102819966465595004399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2426803759955287460005865 1820102819966465595004399)
    ·
      refine ⟨2730154229949698392506599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820102819966465595004399 2730154229949698392506599)
      ·
        refine ⟨4095231344924547588759899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730154229949698392506599 4095231344924547588759899)
        ·
          refine ⟨6142847017386821383139849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095231344924547588759899 6142847017386821383139849)
          ·
            refine ⟨4607135263040116037354887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6142847017386821383139849 4607135263040116037354887)
            ·
              refine ⟨6910702894560174056032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607135263040116037354887 6910702894560174056032331)
              ·
                refine ⟨10366054341840261084048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6910702894560174056032331 10366054341840261084048497)
                ·
                  refine ⟨7774540756380195813036373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10366054341840261084048497 7774540756380195813036373)
                  ·
                    refine ⟨22776974872207604921005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 7774540756380195813036373 22776974872207604921005)
                    ·
                      rfl

theorem cell22_66537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_66537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66537 prefixEnd_66537 := by exact prefixLift 66537
  have htrace : WordTrace (prefixWord ++ tailWord_66537) baseStart_66537 baseEnd_66537 := by
    simpa [prefixWord, tailWord_66537, baseEnd_66537] using wordTrace_append hprefix tailTrace_66537
  have hstable : (prefixWord ++ tailWord_66537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66537).length < 2 ^ (prefixWord ++ tailWord_66537).sum := by decide
  have hdescent : baseEnd_66537 < baseStart_66537 := by decide
  rcases family_descends (prefixWord ++ tailWord_66537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66571 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 2, 4]
def baseStart_66571 : Nat := 118140960795 + 66571 * 2 ^ 59
def prefixEnd_66571 : Nat := 4983230072969 + 3 ^ 40 * 66571 * 2
def baseEnd_66571 : Nat := 22788613767042849570901

theorem tailTrace_66571 : CollatzResearch.WordTrace tailWord_66571 prefixEnd_66571 22788613767042849570901 := by
  unfold tailWord_66571
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428043841832111266743567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1618695894554740844495711 2428043841832111266743567)
  ·
    refine ⟨3642065762748166900115351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2428043841832111266743567 3642065762748166900115351)
    ·
      refine ⟨5463098644122250350173027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3642065762748166900115351 5463098644122250350173027)
      ·
        refine ⟨8194647966183375525259541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5463098644122250350173027 8194647966183375525259541)
        ·
          refine ⟨384124123414845727746541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8194647966183375525259541 384124123414845727746541)
          ·
            refine ⟨144046546280567147904953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384124123414845727746541 144046546280567147904953)
            ·
              refine ⟨108034909710425360928715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144046546280567147904953 108034909710425360928715)
              ·
                refine ⟨162052364565638041393073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108034909710425360928715 162052364565638041393073)
                ·
                  refine ⟨121539273424228531044805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162052364565638041393073 121539273424228531044805)
                  ·
                    refine ⟨22788613767042849570901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121539273424228531044805 22788613767042849570901)
                    ·
                      rfl

theorem cell22_66571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 4].length) (baseStart_66571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66571 prefixEnd_66571 := by exact prefixLift 66571
  have htrace : WordTrace (prefixWord ++ tailWord_66571) baseStart_66571 baseEnd_66571 := by
    simpa [prefixWord, tailWord_66571, baseEnd_66571] using wordTrace_append hprefix tailTrace_66571
  have hstable : (prefixWord ++ tailWord_66571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66571).length < 2 ^ (prefixWord ++ tailWord_66571).sum := by decide
  have hdescent : baseEnd_66571 < baseStart_66571 := by decide
  rcases family_descends (prefixWord ++ tailWord_66571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66592 : List Nat := [2, 1, 1, 7, 1, 2, 2, 2, 4]
def baseStart_66592 : Nat := 118140960795 + 66592 * 2 ^ 59
def prefixEnd_66592 : Nat := 4983230072969 + 3 ^ 40 * 66592 * 2
def baseEnd_66592 : Nat := 7598600832068598265279

theorem tailTrace_66592 : CollatzResearch.WordTrace tailWord_66592 prefixEnd_66592 7598600832068598265279 := by
  unfold tailWord_66592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214404887378015926629015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1619206516504021235505353 1214404887378015926629015)
  ·
    refine ⟨1821607331067023889943523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1214404887378015926629015 1821607331067023889943523)
    ·
      refine ⟨2732410996600535834915285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821607331067023889943523 2732410996600535834915285)
      ·
        refine ⟨64040882732825058630827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2732410996600535834915285 64040882732825058630827)
        ·
          refine ⟨96061324099237587946241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64040882732825058630827 96061324099237587946241)
          ·
            refine ⟨72045993074428190959681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96061324099237587946241 72045993074428190959681)
            ·
              refine ⟨54034494805821143219761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72045993074428190959681 54034494805821143219761)
              ·
                refine ⟨40525871104365857414821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54034494805821143219761 40525871104365857414821)
                ·
                  refine ⟨7598600832068598265279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40525871104365857414821 7598600832068598265279)
                  ·
                    rfl

theorem cell22_66592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_66592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66592 prefixEnd_66592 := by exact prefixLift 66592
  have htrace : WordTrace (prefixWord ++ tailWord_66592) baseStart_66592 baseEnd_66592 := by
    simpa [prefixWord, tailWord_66592, baseEnd_66592] using wordTrace_append hprefix tailTrace_66592
  have hstable : (prefixWord ++ tailWord_66592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66592).length < 2 ^ (prefixWord ++ tailWord_66592).sum := by decide
  have hdescent : baseEnd_66592 < baseStart_66592 := by decide
  rcases family_descends (prefixWord ++ tailWord_66592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66691 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 6, 3]
def baseStart_66691 : Nat := 118140960795 + 66691 * 2 ^ 59
def prefixEnd_66691 : Nat := 4983230072969 + 3 ^ 40 * 66691 * 2
def baseEnd_66691 : Nat := 22829692219402536570533

theorem tailTrace_66691 : CollatzResearch.WordTrace tailWord_66691 prefixEnd_66691 22829692219402536570533 := by
  unfold tailWord_66691
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432420601397371761111927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1621613734264914507407951 2432420601397371761111927)
  ·
    refine ⟨3648630902096057641667891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2432420601397371761111927 3648630902096057641667891)
    ·
      refine ⟨5472946353144086462501837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3648630902096057641667891 5472946353144086462501837)
      ·
        refine ⟨2052354882429032423438189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5472946353144086462501837 2052354882429032423438189)
        ·
          refine ⟨769633080910887158789321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2052354882429032423438189 769633080910887158789321)
          ·
            refine ⟨577224810683165369091991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769633080910887158789321 577224810683165369091991)
            ·
              refine ⟨865837216024748053637987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577224810683165369091991 865837216024748053637987)
              ·
                refine ⟨1298755824037122080456981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865837216024748053637987 1298755824037122080456981)
                ·
                  refine ⟨60879179251740097521421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1298755824037122080456981 60879179251740097521421)
                  ·
                    refine ⟨22829692219402536570533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60879179251740097521421 22829692219402536570533)
                    ·
                      rfl

theorem cell22_66691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 3].length) (baseStart_66691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66691 prefixEnd_66691 := by exact prefixLift 66691
  have htrace : WordTrace (prefixWord ++ tailWord_66691) baseStart_66691 baseEnd_66691 := by
    simpa [prefixWord, tailWord_66691, baseEnd_66691] using wordTrace_append hprefix tailTrace_66691
  have hstable : (prefixWord ++ tailWord_66691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66691).length < 2 ^ (prefixWord ++ tailWord_66691).sum := by decide
  have hdescent : baseEnd_66691 < baseStart_66691 := by decide
  rcases family_descends (prefixWord ++ tailWord_66691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66721 : List Nat := [1, 2, 3, 3, 1, 1, 4, 7]
def baseStart_66721 : Nat := 118140960795 + 66721 * 2 ^ 59
def prefixEnd_66721 : Nat := 4983230072969 + 3 ^ 40 * 66721 * 2
def baseEnd_66721 : Nat := 2537773536943606480049

theorem tailTrace_66721 : CollatzResearch.WordTrace tailWord_66721 prefixEnd_66721 2537773536943606480049 := by
  unfold tailWord_66721
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433514791288686884704017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1622343194192457923136011 2433514791288686884704017)
  ·
    refine ⟨1825136093466515163528013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2433514791288686884704017 1825136093466515163528013)
    ·
      refine ⟨684426035049943186323005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1825136093466515163528013 684426035049943186323005)
      ·
        refine ⟨256659763143728694871127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 684426035049943186323005 256659763143728694871127)
        ·
          refine ⟨384989644715593042306691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256659763143728694871127 384989644715593042306691)
          ·
            refine ⟨577484467073389563460037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384989644715593042306691 577484467073389563460037)
            ·
              refine ⟨108278337576260543148757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577484467073389563460037 108278337576260543148757)
              ·
                refine ⟨2537773536943606480049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108278337576260543148757 2537773536943606480049)
                ·
                  rfl

theorem cell22_66721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 7].length) (baseStart_66721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66721 prefixEnd_66721 := by exact prefixLift 66721
  have htrace : WordTrace (prefixWord ++ tailWord_66721) baseStart_66721 baseEnd_66721 := by
    simpa [prefixWord, tailWord_66721, baseEnd_66721] using wordTrace_append hprefix tailTrace_66721
  have hstable : (prefixWord ++ tailWord_66721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66721).length < 2 ^ (prefixWord ++ tailWord_66721).sum := by decide
  have hdescent : baseEnd_66721 < baseStart_66721 := by decide
  rcases family_descends (prefixWord ++ tailWord_66721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66725 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_66725 : Nat := 118140960795 + 66725 * 2 ^ 59
def prefixEnd_66725 : Nat := 4983230072969 + 3 ^ 40 * 66725 * 2
def baseEnd_66725 : Nat := 22841331114237781220429

theorem tailTrace_66725 : CollatzResearch.WordTrace tailWord_66725 prefixEnd_66725 22841331114237781220429 := by
  unfold tailWord_66725
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433660683274195567849629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1622440455516130378566419 2433660683274195567849629)
  ·
    refine ⟨912622756227823337943611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2433660683274195567849629 912622756227823337943611)
    ·
      refine ⟨1368934134341735006915417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 912622756227823337943611 1368934134341735006915417)
      ·
        refine ⟨1026700600756301255186563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1368934134341735006915417 1026700600756301255186563)
        ·
          refine ⟨1540050901134451882779845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026700600756301255186563 1540050901134451882779845)
          ·
            refine ⟨288759543962709728021221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1540050901134451882779845 288759543962709728021221)
            ·
              refine ⟨54142414493008074003979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288759543962709728021221 54142414493008074003979)
              ·
                refine ⟨81213621739512111005969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54142414493008074003979 81213621739512111005969)
                ·
                  refine ⟨60910216304634083254477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81213621739512111005969 60910216304634083254477)
                  ·
                    refine ⟨22841331114237781220429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60910216304634083254477 22841331114237781220429)
                    ·
                      rfl

theorem cell22_66725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_66725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66725 prefixEnd_66725 := by exact prefixLift 66725
  have htrace : WordTrace (prefixWord ++ tailWord_66725) baseStart_66725 baseEnd_66725 := by
    simpa [prefixWord, tailWord_66725, baseEnd_66725] using wordTrace_append hprefix tailTrace_66725
  have hstable : (prefixWord ++ tailWord_66725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66725).length < 2 ^ (prefixWord ++ tailWord_66725).sum := by decide
  have hdescent : baseEnd_66725 < baseStart_66725 := by decide
  rcases family_descends (prefixWord ++ tailWord_66725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66742 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_66742 : Nat := 118140960795 + 66742 * 2 ^ 59
def prefixEnd_66742 : Nat := 4983230072969 + 3 ^ 40 * 66742 * 2
def baseEnd_66742 : Nat := 22847150561655403545377

theorem tailTrace_66742 : CollatzResearch.WordTrace tailWord_66742 prefixEnd_66742 22847150561655403545377 := by
  unfold tailWord_66742
  simp only [CollatzResearch.WordTrace]
  refine ⟨152142545263287966951155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1622853816141738314145653 152142545263287966951155)
  ·
    refine ⟨228213817894931950426733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152142545263287966951155 228213817894931950426733)
    ·
      refine ⟨85580181710599481410025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228213817894931950426733 85580181710599481410025)
      ·
        refine ⟨64185136282949611057519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85580181710599481410025 64185136282949611057519)
        ·
          refine ⟨96277704424424416586279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64185136282949611057519 96277704424424416586279)
          ·
            refine ⟨144416556636636624879419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96277704424424416586279 144416556636636624879419)
            ·
              refine ⟨216624834954954937319129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144416556636636624879419 216624834954954937319129)
              ·
                refine ⟨162468626216216202989347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216624834954954937319129 162468626216216202989347)
                ·
                  refine ⟨243702939324324304484021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162468626216216202989347 243702939324324304484021)
                  ·
                    refine ⟨22847150561655403545377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 243702939324324304484021 22847150561655403545377)
                    ·
                      rfl

theorem cell22_66742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_66742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66742 prefixEnd_66742 := by exact prefixLift 66742
  have htrace : WordTrace (prefixWord ++ tailWord_66742) baseStart_66742 baseEnd_66742 := by
    simpa [prefixWord, tailWord_66742, baseEnd_66742] using wordTrace_append hprefix tailTrace_66742
  have hstable : (prefixWord ++ tailWord_66742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66742).length < 2 ^ (prefixWord ++ tailWord_66742).sum := by decide
  have hdescent : baseEnd_66742 < baseStart_66742 := by decide
  rcases family_descends (prefixWord ++ tailWord_66742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66772 : List Nat := [2, 4, 1, 4, 2, 1, 1, 7]
def baseStart_66772 : Nat := 118140960795 + 66772 * 2 ^ 59
def prefixEnd_66772 : Nat := 4983230072969 + 3 ^ 40 * 66772 * 2
def baseEnd_66772 : Nat := 2539713352749480588365

theorem tailTrace_66772 : CollatzResearch.WordTrace tailWord_66772 prefixEnd_66772 2539713352749480588365 := by
  unfold tailWord_66772
  simp only [CollatzResearch.WordTrace]
  refine ⟨1217687457051961297405285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1623583276069281729873713 1217687457051961297405285)
  ·
    refine ⟨228316398197242743263491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1217687457051961297405285 228316398197242743263491)
    ·
      refine ⟨342474597295864114895237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228316398197242743263491 342474597295864114895237)
      ·
        refine ⟨64213986992974521542857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 342474597295864114895237 64213986992974521542857)
        ·
          refine ⟨48160490244730891157143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64213986992974521542857 48160490244730891157143)
          ·
            refine ⟨72240735367096336735715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48160490244730891157143 72240735367096336735715)
            ·
              refine ⟨108361103050644505103573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72240735367096336735715 108361103050644505103573)
              ·
                refine ⟨2539713352749480588365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108361103050644505103573 2539713352749480588365)
                ·
                  rfl

theorem cell22_66772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 7].length) (baseStart_66772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66772 prefixEnd_66772 := by exact prefixLift 66772
  have htrace : WordTrace (prefixWord ++ tailWord_66772) baseStart_66772 baseEnd_66772 := by
    simpa [prefixWord, tailWord_66772, baseEnd_66772] using wordTrace_append hprefix tailTrace_66772
  have hstable : (prefixWord ++ tailWord_66772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66772).length < 2 ^ (prefixWord ++ tailWord_66772).sum := by decide
  have hdescent : baseEnd_66772 < baseStart_66772 := by decide
  rcases family_descends (prefixWord ++ tailWord_66772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66828 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_66828 : Nat := 118140960795 + 66828 * 2 ^ 59
def prefixEnd_66828 : Nat := 4983230072969 + 3 ^ 40 * 66828 * 2
def baseEnd_66828 : Nat := 7625530039726615298371

theorem tailTrace_66828 : CollatzResearch.WordTrace tailWord_66828 prefixEnd_66828 7625530039726615298371 := by
  unfold tailWord_66828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1218708700950522079424569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1624944934600696105899425 1218708700950522079424569)
  ·
    refine ⟨914031525712891559568427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1218708700950522079424569 914031525712891559568427)
    ·
      refine ⟨1371047288569337339352641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914031525712891559568427 1371047288569337339352641)
      ·
        refine ⟨1028285466427003004514481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371047288569337339352641 1028285466427003004514481)
        ·
          refine ⟨771214099820252253385861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028285466427003004514481 771214099820252253385861)
          ·
            refine ⟨144602643716297297509849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 771214099820252253385861 144602643716297297509849)
            ·
              refine ⟨108451982787222973132387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144602643716297297509849 108451982787222973132387)
              ·
                refine ⟨162677974180834459698581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108451982787222973132387 162677974180834459698581)
                ·
                  refine ⟨7625530039726615298371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162677974180834459698581 7625530039726615298371)
                  ·
                    rfl

theorem cell22_66828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_66828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66828 prefixEnd_66828 := by exact prefixLift 66828
  have htrace : WordTrace (prefixWord ++ tailWord_66828) baseStart_66828 baseEnd_66828 := by
    simpa [prefixWord, tailWord_66828, baseEnd_66828] using wordTrace_append hprefix tailTrace_66828
  have hstable : (prefixWord ++ tailWord_66828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66828).length < 2 ^ (prefixWord ++ tailWord_66828).sum := by decide
  have hdescent : baseEnd_66828 < baseStart_66828 := by decide
  rcases family_descends (prefixWord ++ tailWord_66828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66834 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_66834 : Nat := 118140960795 + 66834 * 2 ^ 59
def prefixEnd_66834 : Nat := 4983230072969 + 3 ^ 40 * 66834 * 2
def baseEnd_66834 : Nat := 7626214680599276748365

theorem tailTrace_66834 : CollatzResearch.WordTrace tailWord_66834 prefixEnd_66834 7626214680599276748365 := by
  unfold tailWord_66834
  simp only [CollatzResearch.WordTrace]
  refine ⟨609409059969826795891889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1625090826586204789045037 609409059969826795891889)
  ·
    refine ⟨457056794977370096918917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 609409059969826795891889 457056794977370096918917)
    ·
      refine ⟨85698149058256893172297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457056794977370096918917 85698149058256893172297)
      ·
        refine ⟨64273611793692669879223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85698149058256893172297 64273611793692669879223)
        ·
          refine ⟨96410417690539004818835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64273611793692669879223 96410417690539004818835)
          ·
            refine ⟨144615626535808507228253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96410417690539004818835 144615626535808507228253)
            ·
              refine ⟨54230859950928190210595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144615626535808507228253 54230859950928190210595)
              ·
                refine ⟨81346289926392285315893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54230859950928190210595 81346289926392285315893)
                ·
                  refine ⟨7626214680599276748365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81346289926392285315893 7626214680599276748365)
                  ·
                    rfl

theorem cell22_66834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_66834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66834 prefixEnd_66834 := by exact prefixLift 66834
  have htrace : WordTrace (prefixWord ++ tailWord_66834) baseStart_66834 baseEnd_66834 := by
    simpa [prefixWord, tailWord_66834, baseEnd_66834] using wordTrace_append hprefix tailTrace_66834
  have hstable : (prefixWord ++ tailWord_66834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66834).length < 2 ^ (prefixWord ++ tailWord_66834).sum := by decide
  have hdescent : baseEnd_66834 < baseStart_66834 := by decide
  rcases family_descends (prefixWord ++ tailWord_66834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66997 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 4]
def baseStart_66997 : Nat := 118140960795 + 66997 * 2 ^ 59
def prefixEnd_66997 : Nat := 4983230072969 + 3 ^ 40 * 66997 * 2
def baseEnd_66997 : Nat := 7644814090973246139865

theorem tailTrace_66997 : CollatzResearch.WordTrace tailWord_66997 prefixEnd_66997 7644814090973246139865 := by
  unfold tailWord_66997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443581338288786021751245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1629054225525857347834163 2443581338288786021751245)
  ·
    refine ⟨916343001858294758156717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2443581338288786021751245 916343001858294758156717)
    ·
      refine ⟨343628625696860534308769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 916343001858294758156717 343628625696860534308769)
      ·
        refine ⟨257721469272645400731577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343628625696860534308769 257721469272645400731577)
        ·
          refine ⟨193291101954484050548683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257721469272645400731577 193291101954484050548683)
          ·
            refine ⟨289936652931726075823025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193291101954484050548683 289936652931726075823025)
            ·
              refine ⟨217452489698794556867269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289936652931726075823025 217452489698794556867269)
              ·
                refine ⟨40772341818523979412613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217452489698794556867269 40772341818523979412613)
                ·
                  refine ⟨7644814090973246139865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40772341818523979412613 7644814090973246139865)
                  ·
                    rfl

theorem cell22_66997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_66997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_66997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_66997 prefixEnd_66997 := by exact prefixLift 66997
  have htrace : WordTrace (prefixWord ++ tailWord_66997) baseStart_66997 baseEnd_66997 := by
    simpa [prefixWord, tailWord_66997, baseEnd_66997] using wordTrace_append hprefix tailTrace_66997
  have hstable : (prefixWord ++ tailWord_66997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66997).length < 2 ^ (prefixWord ++ tailWord_66997).sum := by decide
  have hdescent : baseEnd_66997 < baseStart_66997 := by decide
  rcases family_descends (prefixWord ++ tailWord_66997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67012 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_67012 : Nat := 118140960795 + 67012 * 2 ^ 59
def prefixEnd_67012 : Nat := 4983230072969 + 3 ^ 40 * 67012 * 2
def baseEnd_67012 : Nat := 22939577079464699294549

theorem tailTrace_67012 : CollatzResearch.WordTrace tailWord_67012 prefixEnd_67012 22939577079464699294549 := by
  unfold tailWord_67012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222064216617221791773645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1629418955489629055698193 1222064216617221791773645)
  ·
    refine ⟨458274081231458171915117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1222064216617221791773645 458274081231458171915117)
    ·
      refine ⟨171852780461796814468169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458274081231458171915117 171852780461796814468169)
      ·
        refine ⟨128889585346347610851127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171852780461796814468169 128889585346347610851127)
        ·
          refine ⟨193334378019521416276691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128889585346347610851127 193334378019521416276691)
          ·
            refine ⟨290001567029282124415037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193334378019521416276691 290001567029282124415037)
            ·
              refine ⟨108750587635980796655639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290001567029282124415037 108750587635980796655639)
              ·
                refine ⟨163125881453971194983459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108750587635980796655639 163125881453971194983459)
                ·
                  refine ⟨244688822180956792475189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163125881453971194983459 244688822180956792475189)
                  ·
                    refine ⟨22939577079464699294549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244688822180956792475189 22939577079464699294549)
                    ·
                      rfl

theorem cell22_67012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_67012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67012 prefixEnd_67012 := by exact prefixLift 67012
  have htrace : WordTrace (prefixWord ++ tailWord_67012) baseStart_67012 baseEnd_67012 := by
    simpa [prefixWord, tailWord_67012, baseEnd_67012] using wordTrace_append hprefix tailTrace_67012
  have hstable : (prefixWord ++ tailWord_67012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67012).length < 2 ^ (prefixWord ++ tailWord_67012).sum := by decide
  have hdescent : baseEnd_67012 < baseStart_67012 := by decide
  rcases family_descends (prefixWord ++ tailWord_67012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67057 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_67057 : Nat := 118140960795 + 67057 * 2 ^ 59
def prefixEnd_67057 : Nat := 4983230072969 + 3 ^ 40 * 67057 * 2
def baseEnd_67057 : Nat := 22954981499099581919411

theorem tailTrace_67057 : CollatzResearch.WordTrace tailWord_67057 prefixEnd_67057 22954981499099581919411 := by
  unfold tailWord_67057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445769718071416268935425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1630513145380944179290283 2445769718071416268935425)
  ·
    refine ⟨1834327288553562201701569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2445769718071416268935425 1834327288553562201701569)
    ·
      refine ⟨1375745466415171651276177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834327288553562201701569 1375745466415171651276177)
      ·
        refine ⟨1031809099811378738457133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1375745466415171651276177 1031809099811378738457133)
        ·
          refine ⟨386928412429267026921425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031809099811378738457133 386928412429267026921425)
          ·
            refine ⟨290196309321950270191069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386928412429267026921425 290196309321950270191069)
            ·
              refine ⟨108823615995731351321651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290196309321950270191069 108823615995731351321651)
              ·
                refine ⟨163235423993597026982477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108823615995731351321651 163235423993597026982477)
                ·
                  refine ⟨61213283997598885118429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163235423993597026982477 61213283997598885118429)
                  ·
                    refine ⟨22954981499099581919411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61213283997598885118429 22954981499099581919411)
                    ·
                      rfl

theorem cell22_67057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_67057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67057 prefixEnd_67057 := by exact prefixLift 67057
  have htrace : WordTrace (prefixWord ++ tailWord_67057) baseStart_67057 baseEnd_67057 := by
    simpa [prefixWord, tailWord_67057, baseEnd_67057] using wordTrace_append hprefix tailTrace_67057
  have hstable : (prefixWord ++ tailWord_67057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67057).length < 2 ^ (prefixWord ++ tailWord_67057).sum := by decide
  have hdescent : baseEnd_67057 < baseStart_67057 := by decide
  rcases family_descends (prefixWord ++ tailWord_67057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67078 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_67078 : Nat := 118140960795 + 67078 * 2 ^ 59
def prefixEnd_67078 : Nat := 4983230072969 + 3 ^ 40 * 67078 * 2
def baseEnd_67078 : Nat := 22962170228262527144347

theorem tailTrace_67078 : CollatzResearch.WordTrace tailWord_67078 prefixEnd_67078 22962170228262527144347 := by
  unfold tailWord_67078
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454239093604276732809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1631023767330224570299925 76454239093604276732809)
  ·
    refine ⟨57340679320203207549607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76454239093604276732809 57340679320203207549607)
    ·
      refine ⟨86011018980304811324411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57340679320203207549607 86011018980304811324411)
      ·
        refine ⟨129016528470457216986617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86011018980304811324411 129016528470457216986617)
        ·
          refine ⟨96762396352842912739963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129016528470457216986617 96762396352842912739963)
          ·
            refine ⟨145143594529264369109945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96762396352842912739963 145143594529264369109945)
            ·
              refine ⟨108857695896948276832459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145143594529264369109945 108857695896948276832459)
              ·
                refine ⟨163286543845422415248689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108857695896948276832459 163286543845422415248689)
                ·
                  refine ⟨122464907884066811436517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163286543845422415248689 122464907884066811436517)
                  ·
                    refine ⟨22962170228262527144347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122464907884066811436517 22962170228262527144347)
                    ·
                      rfl

theorem cell22_67078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_67078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67078 prefixEnd_67078 := by exact prefixLift 67078
  have htrace : WordTrace (prefixWord ++ tailWord_67078) baseStart_67078 baseEnd_67078 := by
    simpa [prefixWord, tailWord_67078, baseEnd_67078] using wordTrace_append hprefix tailTrace_67078
  have hstable : (prefixWord ++ tailWord_67078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67078).length < 2 ^ (prefixWord ++ tailWord_67078).sum := by decide
  have hdescent : baseEnd_67078 < baseStart_67078 := by decide
  rcases family_descends (prefixWord ++ tailWord_67078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67132 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_67132 : Nat := 118140960795 + 67132 * 2 ^ 59
def prefixEnd_67132 : Nat := 4983230072969 + 3 ^ 40 * 67132 * 2
def baseEnd_67132 : Nat := 7660218510608128764727

theorem tailTrace_67132 : CollatzResearch.WordTrace tailWord_67132 prefixEnd_67132 7660218510608128764727 := by
  unfold tailWord_67132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224252596399852038957825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1632336795199802718610433 1224252596399852038957825)
  ·
    refine ⟨918189447299889029218369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1224252596399852038957825 918189447299889029218369)
    ·
      refine ⟨688642085474916771913777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 918189447299889029218369 688642085474916771913777)
      ·
        refine ⟨516481564106187578935333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688642085474916771913777 516481564106187578935333)
        ·
          refine ⟨96840293269910171050375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 516481564106187578935333 96840293269910171050375)
          ·
            refine ⟨145260439904865256575563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96840293269910171050375 145260439904865256575563)
            ·
              refine ⟨217890659857297884863345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145260439904865256575563 217890659857297884863345)
              ·
                refine ⟨163417994892973413647509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217890659857297884863345 163417994892973413647509)
                ·
                  refine ⟨7660218510608128764727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163417994892973413647509 7660218510608128764727)
                  ·
                    rfl

theorem cell22_67132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_67132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67132 prefixEnd_67132 := by exact prefixLift 67132
  have htrace : WordTrace (prefixWord ++ tailWord_67132) baseStart_67132 baseEnd_67132 := by
    simpa [prefixWord, tailWord_67132, baseEnd_67132] using wordTrace_append hprefix tailTrace_67132
  have hstable : (prefixWord ++ tailWord_67132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67132).length < 2 ^ (prefixWord ++ tailWord_67132).sum := by decide
  have hdescent : baseEnd_67132 < baseStart_67132 := by decide
  rcases family_descends (prefixWord ++ tailWord_67132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67164 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_67164 : Nat := 118140960795 + 67164 * 2 ^ 59
def prefixEnd_67164 : Nat := 4983230072969 + 3 ^ 40 * 67164 * 2
def baseEnd_67164 : Nat := 22991609785786969494083

theorem tailTrace_67164 : CollatzResearch.WordTrace tailWord_67164 prefixEnd_67164 22991609785786969494083 := by
  unfold tailWord_67164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224836164341886771540273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1633114885789182362053697 1224836164341886771540273)
  ·
    refine ⟨918627123256415078655205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1224836164341886771540273 918627123256415078655205)
    ·
      refine ⟨172242585610577827247851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 918627123256415078655205 172242585610577827247851)
      ·
        refine ⟨258363878415866740871777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172242585610577827247851 258363878415866740871777)
        ·
          refine ⟨193772908811900055653833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258363878415866740871777 193772908811900055653833)
          ·
            refine ⟨145329681608925041740375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193772908811900055653833 145329681608925041740375)
            ·
              refine ⟨217994522413387562610563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145329681608925041740375 217994522413387562610563)
              ·
                refine ⟨326991783620081343915845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217994522413387562610563 326991783620081343915845)
                ·
                  refine ⟨61310959428765251984221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326991783620081343915845 61310959428765251984221)
                  ·
                    refine ⟨22991609785786969494083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61310959428765251984221 22991609785786969494083)
                    ·
                      rfl

theorem cell22_67164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_67164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67164 prefixEnd_67164 := by exact prefixLift 67164
  have htrace : WordTrace (prefixWord ++ tailWord_67164) baseStart_67164 baseEnd_67164 := by
    simpa [prefixWord, tailWord_67164, baseEnd_67164] using wordTrace_append hprefix tailTrace_67164
  have hstable : (prefixWord ++ tailWord_67164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67164).length < 2 ^ (prefixWord ++ tailWord_67164).sum := by decide
  have hdescent : baseEnd_67164 < baseStart_67164 := by decide
  rcases family_descends (prefixWord ++ tailWord_67164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67181 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_67181 : Nat := 118140960795 + 67181 * 2 ^ 59
def prefixEnd_67181 : Nat := 4983230072969 + 3 ^ 40 * 67181 * 2
def baseEnd_67181 : Nat := 22997429233204591819031

theorem tailTrace_67181 : CollatzResearch.WordTrace tailWord_67181 prefixEnd_67181 22997429233204591819031 := by
  unfold tailWord_67181
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450292369622185446449397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1633528246414790297632931 2450292369622185446449397)
  ·
    refine ⟨229714909652079885604631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2450292369622185446449397 229714909652079885604631)
    ·
      refine ⟨344572364478119828406947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229714909652079885604631 344572364478119828406947)
      ·
        refine ⟨516858546717179742610421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344572364478119828406947 516858546717179742610421)
        ·
          refine ⟨48455488754735600869727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 516858546717179742610421 48455488754735600869727)
          ·
            refine ⟨72683233132103401304591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48455488754735600869727 72683233132103401304591)
            ·
              refine ⟨109024849698155101956887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72683233132103401304591 109024849698155101956887)
              ·
                refine ⟨163537274547232652935331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109024849698155101956887 163537274547232652935331)
                ·
                  refine ⟨245305911820848979402997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163537274547232652935331 245305911820848979402997)
                  ·
                    refine ⟨22997429233204591819031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 245305911820848979402997 22997429233204591819031)
                    ·
                      rfl

theorem cell22_67181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_67181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67181 prefixEnd_67181 := by exact prefixLift 67181
  have htrace : WordTrace (prefixWord ++ tailWord_67181) baseStart_67181 baseEnd_67181 := by
    simpa [prefixWord, tailWord_67181, baseEnd_67181] using wordTrace_append hprefix tailTrace_67181
  have hstable : (prefixWord ++ tailWord_67181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67181).length < 2 ^ (prefixWord ++ tailWord_67181).sum := by decide
  have hdescent : baseEnd_67181 < baseStart_67181 := by decide
  rcases family_descends (prefixWord ++ tailWord_67181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67205 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 9]
def baseStart_67205 : Nat := 118140960795 + 67205 * 2 ^ 59
def prefixEnd_67205 : Nat := 4983230072969 + 3 ^ 40 * 67205 * 2
def baseEnd_67205 : Nat := 7668548307892176406319

theorem tailTrace_67205 : CollatzResearch.WordTrace tailWord_67205 prefixEnd_67205 7668548307892176406319 := by
  unfold tailWord_67205
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451167721535237545323069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1634111814356825030215379 2451167721535237545323069)
  ·
    refine ⟨919187895575714079496151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2451167721535237545323069 919187895575714079496151)
    ·
      refine ⟨1378781843363571119244227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919187895575714079496151 1378781843363571119244227)
      ·
        refine ⟨2068172765045356678866341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378781843363571119244227 2068172765045356678866341)
        ·
          refine ⟨387782393446004377287439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2068172765045356678866341 387782393446004377287439)
          ·
            refine ⟨581673590169006565931159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387782393446004377287439 581673590169006565931159)
            ·
              refine ⟨872510385253509848896739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581673590169006565931159 872510385253509848896739)
              ·
                refine ⟨1308765577880264773345109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872510385253509848896739 1308765577880264773345109)
                ·
                  refine ⟨7668548307892176406319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1308765577880264773345109 7668548307892176406319)
                  ·
                    rfl

theorem cell22_67205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_67205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67205 prefixEnd_67205 := by exact prefixLift 67205
  have htrace : WordTrace (prefixWord ++ tailWord_67205) baseStart_67205 baseEnd_67205 := by
    simpa [prefixWord, tailWord_67205, baseEnd_67205] using wordTrace_append hprefix tailTrace_67205
  have hstable : (prefixWord ++ tailWord_67205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67205).length < 2 ^ (prefixWord ++ tailWord_67205).sum := by decide
  have hdescent : baseEnd_67205 < baseStart_67205 := by decide
  rcases family_descends (prefixWord ++ tailWord_67205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67277 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_67277 : Nat := 118140960795 + 67277 * 2 ^ 59
def prefixEnd_67277 : Nat := 4983230072969 + 3 ^ 40 * 67277 * 2
def baseEnd_67277 : Nat := 23030291995092341418737

theorem tailTrace_67277 : CollatzResearch.WordTrace tailWord_67277 prefixEnd_67277 23030291995092341418737 := by
  unfold tailWord_67277
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453793777274393841944085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1635862518182929227962723 2453793777274393841944085)
  ·
    refine ⟨115021583309737211341129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2453793777274393841944085 115021583309737211341129)
    ·
      refine ⟨86266187482302908505847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115021583309737211341129 86266187482302908505847)
      ·
        refine ⟨129399281223454362758771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86266187482302908505847 129399281223454362758771)
        ·
          refine ⟨194098921835181544138157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129399281223454362758771 194098921835181544138157)
          ·
            refine ⟨72787095688193079051809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194098921835181544138157 72787095688193079051809)
            ·
              refine ⟨54590321766144809288857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72787095688193079051809 54590321766144809288857)
              ·
                refine ⟨40942741324608606966643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54590321766144809288857 40942741324608606966643)
                ·
                  refine ⟨61414111986912910449965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40942741324608606966643 61414111986912910449965)
                  ·
                    refine ⟨23030291995092341418737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61414111986912910449965 23030291995092341418737)
                    ·
                      rfl

theorem cell22_67277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_67277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67277 prefixEnd_67277 := by exact prefixLift 67277
  have htrace : WordTrace (prefixWord ++ tailWord_67277) baseStart_67277 baseEnd_67277 := by
    simpa [prefixWord, tailWord_67277, baseEnd_67277] using wordTrace_append hprefix tailTrace_67277
  have hstable : (prefixWord ++ tailWord_67277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67277).length < 2 ^ (prefixWord ++ tailWord_67277).sum := by decide
  have hdescent : baseEnd_67277 < baseStart_67277 := by decide
  rcases family_descends (prefixWord ++ tailWord_67277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67342 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_67342 : Nat := 118140960795 + 67342 * 2 ^ 59
def prefixEnd_67342 : Nat := 4983230072969 + 3 ^ 40 * 67342 * 2
def baseEnd_67342 : Nat := 23052542823453838543537

theorem tailTrace_67342 : CollatzResearch.WordTrace tailWord_67342 prefixEnd_67342 23052542823453838543537 := by
  unfold tailWord_67342
  simp only [CollatzResearch.WordTrace]
  refine ⟨307020565254863742882535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1637443014692606628706853 307020565254863742882535)
  ·
    refine ⟨460530847882295614323803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307020565254863742882535 460530847882295614323803)
    ·
      refine ⟨690796271823443421485705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460530847882295614323803 690796271823443421485705)
      ·
        refine ⟨518097203867582566114279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690796271823443421485705 518097203867582566114279)
        ·
          refine ⟨777145805801373849171419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518097203867582566114279 777145805801373849171419)
          ·
            refine ⟨1165718708702060773757129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777145805801373849171419 1165718708702060773757129)
            ·
              refine ⟨874289031526545580317847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165718708702060773757129 874289031526545580317847)
              ·
                refine ⟨1311433547289818370476771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874289031526545580317847 1311433547289818370476771)
                ·
                  refine ⟨1967150320934727555715157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311433547289818370476771 1967150320934727555715157)
                  ·
                    refine ⟨23052542823453838543537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1967150320934727555715157 23052542823453838543537)
                    ·
                      rfl

theorem cell22_67342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_67342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67342 prefixEnd_67342 := by exact prefixLift 67342
  have htrace : WordTrace (prefixWord ++ tailWord_67342) baseStart_67342 baseEnd_67342 := by
    simpa [prefixWord, tailWord_67342, baseEnd_67342] using wordTrace_append hprefix tailTrace_67342
  have hstable : (prefixWord ++ tailWord_67342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67342).length < 2 ^ (prefixWord ++ tailWord_67342).sum := by decide
  have hdescent : baseEnd_67342 < baseStart_67342 := by decide
  rcases family_descends (prefixWord ++ tailWord_67342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67378 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_67378 : Nat := 118140960795 + 67378 * 2 ^ 59
def prefixEnd_67378 : Nat := 4983230072969 + 3 ^ 40 * 67378 * 2
def baseEnd_67378 : Nat := 23064866359161744643427

theorem tailTrace_67378 : CollatzResearch.WordTrace tailWord_67378 prefixEnd_67378 23064866359161744643427 := by
  unfold tailWord_67378
  simp only [CollatzResearch.WordTrace]
  refine ⟨614369387477122022842697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1638318366605658727580525 614369387477122022842697)
  ·
    refine ⟨460777040607841517132023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 614369387477122022842697 460777040607841517132023)
    ·
      refine ⟨691165560911762275698035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460777040607841517132023 691165560911762275698035)
      ·
        refine ⟨1036748341367643413547053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691165560911762275698035 1036748341367643413547053)
        ·
          refine ⟨388780628012866280080145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1036748341367643413547053 388780628012866280080145)
          ·
            refine ⟨291585471009649710060109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388780628012866280080145 291585471009649710060109)
            ·
              refine ⟨109344551628618641272541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291585471009649710060109 109344551628618641272541)
              ·
                refine ⟨41004206860731990477203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109344551628618641272541 41004206860731990477203)
                ·
                  refine ⟨61506310291097985715805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41004206860731990477203 61506310291097985715805)
                  ·
                    refine ⟨23064866359161744643427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61506310291097985715805 23064866359161744643427)
                    ·
                      rfl

theorem cell22_67378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_67378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67378 prefixEnd_67378 := by exact prefixLift 67378
  have htrace : WordTrace (prefixWord ++ tailWord_67378) baseStart_67378 baseEnd_67378 := by
    simpa [prefixWord, tailWord_67378, baseEnd_67378] using wordTrace_append hprefix tailTrace_67378
  have hstable : (prefixWord ++ tailWord_67378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67378).length < 2 ^ (prefixWord ++ tailWord_67378).sum := by decide
  have hdescent : baseEnd_67378 < baseStart_67378 := by decide
  rcases family_descends (prefixWord ++ tailWord_67378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67449 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_67449 : Nat := 118140960795 + 67449 * 2 ^ 59
def prefixEnd_67449 : Nat := 4983230072969 + 3 ^ 40 * 67449 * 2
def baseEnd_67449 : Nat := 23089171110141226118209

theorem tailTrace_67449 : CollatzResearch.WordTrace tailWord_67449 prefixEnd_67449 23089171110141226118209 := by
  unfold tailWord_67449
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460067132651267217205401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1640044755100844811470267 2460067132651267217205401)
  ·
    refine ⟨1845050349488450412904051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2460067132651267217205401 1845050349488450412904051)
    ·
      refine ⟨2767575524232675619356077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845050349488450412904051 2767575524232675619356077)
      ·
        refine ⟨1037840821587253357258529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2767575524232675619356077 1037840821587253357258529)
        ·
          refine ⟨778380616190440017943897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037840821587253357258529 778380616190440017943897)
          ·
            refine ⟨583785462142830013457923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778380616190440017943897 583785462142830013457923)
            ·
              refine ⟨875678193214245020186885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583785462142830013457923 875678193214245020186885)
              ·
                refine ⟨164189661227670941285041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 875678193214245020186885 164189661227670941285041)
                ·
                  refine ⟨123142245920753205963781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164189661227670941285041 123142245920753205963781)
                  ·
                    refine ⟨23089171110141226118209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123142245920753205963781 23089171110141226118209)
                    ·
                      rfl

theorem cell22_67449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_67449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67449 prefixEnd_67449 := by exact prefixLift 67449
  have htrace : WordTrace (prefixWord ++ tailWord_67449) baseStart_67449 baseEnd_67449 := by
    simpa [prefixWord, tailWord_67449, baseEnd_67449] using wordTrace_append hprefix tailTrace_67449
  have hstable : (prefixWord ++ tailWord_67449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67449).length < 2 ^ (prefixWord ++ tailWord_67449).sum := by decide
  have hdescent : baseEnd_67449 < baseStart_67449 := by decide
  rcases family_descends (prefixWord ++ tailWord_67449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67502 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_67502 : Nat := 118140960795 + 67502 * 2 ^ 59
def prefixEnd_67502 : Nat := 4983230072969 + 3 ^ 40 * 67502 * 2
def baseEnd_67502 : Nat := 23107314093266754543047

theorem tailTrace_67502 : CollatzResearch.WordTrace tailWord_67502 prefixEnd_67502 23107314093266754543047 := by
  unfold tailWord_67502
  simp only [CollatzResearch.WordTrace]
  refine ⟨307750025182407158610595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1641333467639504845923173 307750025182407158610595)
  ·
    refine ⟨461625037773610737915893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307750025182407158610595 461625037773610737915893)
    ·
      refine ⟨43277347291276006679615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 461625037773610737915893 43277347291276006679615)
      ·
        refine ⟨64916020936914010019423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43277347291276006679615 64916020936914010019423)
        ·
          refine ⟨97374031405371015029135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64916020936914010019423 97374031405371015029135)
          ·
            refine ⟨146061047108056522543703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97374031405371015029135 146061047108056522543703)
            ·
              refine ⟨219091570662084783815555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146061047108056522543703 219091570662084783815555)
              ·
                refine ⟨328637355993127175723333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219091570662084783815555 328637355993127175723333)
                ·
                  refine ⟨61619504248711345448125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328637355993127175723333 61619504248711345448125)
                  ·
                    refine ⟨23107314093266754543047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61619504248711345448125 23107314093266754543047)
                    ·
                      rfl

theorem cell22_67502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_67502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67502 prefixEnd_67502 := by exact prefixLift 67502
  have htrace : WordTrace (prefixWord ++ tailWord_67502) baseStart_67502 baseEnd_67502 := by
    simpa [prefixWord, tailWord_67502, baseEnd_67502] using wordTrace_append hprefix tailTrace_67502
  have hstable : (prefixWord ++ tailWord_67502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67502).length < 2 ^ (prefixWord ++ tailWord_67502).sum := by decide
  have hdescent : baseEnd_67502 < baseStart_67502 := by decide
  rcases family_descends (prefixWord ++ tailWord_67502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67513 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 1, 3]
def baseStart_67513 : Nat := 118140960795 + 67513 * 2 ^ 59
def prefixEnd_67513 : Nat := 4983230072969 + 3 ^ 40 * 67513 * 2
def baseEnd_67513 : Nat := 23111079618066392518013

theorem tailTrace_67513 : CollatzResearch.WordTrace tailWord_67513 prefixEnd_67513 23111079618066392518013 := by
  unfold tailWord_67513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462401404419406147535193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1641600936279604098356795 2462401404419406147535193)
  ·
    refine ⟨1846801053314554610651395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2462401404419406147535193 1846801053314554610651395)
    ·
      refine ⟨2770201579971831915977093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846801053314554610651395 2770201579971831915977093)
      ·
        refine ⟨519412796244718484245705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2770201579971831915977093 519412796244718484245705)
        ·
          refine ⟨389559597183538863184279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519412796244718484245705 389559597183538863184279)
          ·
            refine ⟨584339395775308294776419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389559597183538863184279 584339395775308294776419)
            ·
              refine ⟨876509093662962442164629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584339395775308294776419 876509093662962442164629)
              ·
                refine ⟨41086363765451364476467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 876509093662962442164629 41086363765451364476467)
                ·
                  refine ⟨61629545648177046714701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41086363765451364476467 61629545648177046714701)
                  ·
                    refine ⟨23111079618066392518013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61629545648177046714701 23111079618066392518013)
                    ·
                      rfl

theorem cell22_67513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_67513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67513 prefixEnd_67513 := by exact prefixLift 67513
  have htrace : WordTrace (prefixWord ++ tailWord_67513) baseStart_67513 baseEnd_67513 := by
    simpa [prefixWord, tailWord_67513, baseEnd_67513] using wordTrace_append hprefix tailTrace_67513
  have hstable : (prefixWord ++ tailWord_67513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67513).length < 2 ^ (prefixWord ++ tailWord_67513).sum := by decide
  have hdescent : baseEnd_67513 < baseStart_67513 := by decide
  rcases family_descends (prefixWord ++ tailWord_67513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67556 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_67556 : Nat := 118140960795 + 67556 * 2 ^ 59
def prefixEnd_67556 : Nat := 4983230072969 + 3 ^ 40 * 67556 * 2
def baseEnd_67556 : Nat := 23125799396828613692881

theorem tailTrace_67556 : CollatzResearch.WordTrace tailWord_67556 prefixEnd_67556 23125799396828613692881 := by
  unfold tailWord_67556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231984871631812245675261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1642646495509082994233681 1231984871631812245675261)
  ·
    refine ⟨461994326861929592128223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1231984871631812245675261 461994326861929592128223)
    ·
      refine ⟨692991490292894388192335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461994326861929592128223 692991490292894388192335)
      ·
        refine ⟨1039487235439341582288503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692991490292894388192335 1039487235439341582288503)
        ·
          refine ⟨1559230853159012373432755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039487235439341582288503 1559230853159012373432755)
          ·
            refine ⟨2338846279738518560149133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559230853159012373432755 2338846279738518560149133)
            ·
              refine ⟨877067354901944460055925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2338846279738518560149133 877067354901944460055925)
              ·
                refine ⟨82225064522057293130243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877067354901944460055925 82225064522057293130243)
                ·
                  refine ⟨123337596783085939695365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82225064522057293130243 123337596783085939695365)
                  ·
                    refine ⟨23125799396828613692881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123337596783085939695365 23125799396828613692881)
                    ·
                      rfl

theorem cell22_67556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_67556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67556 prefixEnd_67556 := by exact prefixLift 67556
  have htrace : WordTrace (prefixWord ++ tailWord_67556) baseStart_67556 baseEnd_67556 := by
    simpa [prefixWord, tailWord_67556, baseEnd_67556] using wordTrace_append hprefix tailTrace_67556
  have hstable : (prefixWord ++ tailWord_67556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67556).length < 2 ^ (prefixWord ++ tailWord_67556).sum := by decide
  have hdescent : baseEnd_67556 < baseStart_67556 := by decide
  rcases family_descends (prefixWord ++ tailWord_67556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67571 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 4]
def baseStart_67571 : Nat := 118140960795 + 67571 * 2 ^ 59
def prefixEnd_67571 : Nat := 4983230072969 + 3 ^ 40 * 67571 * 2
def baseEnd_67571 : Nat := 7710311401124524855945

theorem tailTrace_67571 : CollatzResearch.WordTrace tailWord_67571 prefixEnd_67571 7710311401124524855945 := by
  unfold tailWord_67571
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464516838209282053146567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1643011225472854702097711 2464516838209282053146567)
  ·
    refine ⟨3696775257313923079719851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2464516838209282053146567 3696775257313923079719851)
    ·
      refine ⟨5545162885970884619579777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3696775257313923079719851 5545162885970884619579777)
      ·
        refine ⟨4158872164478163464684833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5545162885970884619579777 4158872164478163464684833)
        ·
          refine ⟨3119154123358622598513625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4158872164478163464684833 3119154123358622598513625)
          ·
            refine ⟨2339365592518966948885219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3119154123358622598513625 2339365592518966948885219)
            ·
              refine ⟨3509048388778450423327829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339365592518966948885219 3509048388778450423327829)
              ·
                refine ⟨41121660805997465898373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3509048388778450423327829 41121660805997465898373)
                ·
                  refine ⟨7710311401124524855945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41121660805997465898373 7710311401124524855945)
                  ·
                    rfl

theorem cell22_67571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 4].length) (baseStart_67571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67571 prefixEnd_67571 := by exact prefixLift 67571
  have htrace : WordTrace (prefixWord ++ tailWord_67571) baseStart_67571 baseEnd_67571 := by
    simpa [prefixWord, tailWord_67571, baseEnd_67571] using wordTrace_append hprefix tailTrace_67571
  have hstable : (prefixWord ++ tailWord_67571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67571).length < 2 ^ (prefixWord ++ tailWord_67571).sum := by decide
  have hdescent : baseEnd_67571 < baseStart_67571 := by decide
  rcases family_descends (prefixWord ++ tailWord_67571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67584 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_67584 : Nat := 118140960795 + 67584 * 2 ^ 59
def prefixEnd_67584 : Nat := 4983230072969 + 3 ^ 40 * 67584 * 2
def baseEnd_67584 : Nat := 23135384369045873992795

theorem tailTrace_67584 : CollatzResearch.WordTrace tailWord_67584 prefixEnd_67584 23135384369045873992795 := by
  unfold tailWord_67584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232495493581092636684903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1643327324774790182246537 1232495493581092636684903)
  ·
    refine ⟨1848743240371638955027355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1232495493581092636684903 1848743240371638955027355)
    ·
      refine ⟨2773114860557458432541033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848743240371638955027355 2773114860557458432541033)
      ·
        refine ⟨2079836145418093824405775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773114860557458432541033 2079836145418093824405775)
        ·
          refine ⟨3119754218127140736608663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079836145418093824405775 3119754218127140736608663)
          ·
            refine ⟨4679631327190711104912995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119754218127140736608663 4679631327190711104912995)
            ·
              refine ⟨7019446990786066657369493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4679631327190711104912995 7019446990786066657369493)
              ·
                refine ⟨329036577693096874564195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7019446990786066657369493 329036577693096874564195)
                ·
                  refine ⟨493554866539645311846293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329036577693096874564195 493554866539645311846293)
                  ·
                    refine ⟨23135384369045873992795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 493554866539645311846293 23135384369045873992795)
                    ·
                      rfl

theorem cell22_67584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_67584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67584 prefixEnd_67584 := by exact prefixLift 67584
  have htrace : WordTrace (prefixWord ++ tailWord_67584) baseStart_67584 baseEnd_67584 := by
    simpa [prefixWord, tailWord_67584, baseEnd_67584] using wordTrace_append hprefix tailTrace_67584
  have hstable : (prefixWord ++ tailWord_67584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67584).length < 2 ^ (prefixWord ++ tailWord_67584).sum := by decide
  have hdescent : baseEnd_67584 < baseStart_67584 := by decide
  rcases family_descends (prefixWord ++ tailWord_67584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67648 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_67648 : Nat := 118140960795 + 67648 * 2 ^ 59
def prefixEnd_67648 : Nat := 4983230072969 + 3 ^ 40 * 67648 * 2
def baseEnd_67648 : Nat := 23157292876971040392599

theorem tailTrace_67648 : CollatzResearch.WordTrace tailWord_67648 prefixEnd_67648 23157292876971040392599 := by
  unfold tailWord_67648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233662629465162101849799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1644883505953549469133065 1233662629465162101849799)
  ·
    refine ⟨1850493944197743152774699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1233662629465162101849799 1850493944197743152774699)
    ·
      refine ⟨2775740916296614729162049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850493944197743152774699 2775740916296614729162049)
      ·
        refine ⟨2081805687222461046871537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2775740916296614729162049 2081805687222461046871537)
        ·
          refine ⟨1561354265416845785153653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2081805687222461046871537 1561354265416845785153653)
          ·
            refine ⟨146376962382829292358155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1561354265416845785153653 146376962382829292358155)
            ·
              refine ⟨219565443574243938537233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146376962382829292358155 219565443574243938537233)
              ·
                refine ⟨164674082680682953902925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219565443574243938537233 164674082680682953902925)
                ·
                  refine ⟨61752781005256107713597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164674082680682953902925 61752781005256107713597)
                  ·
                    refine ⟨23157292876971040392599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61752781005256107713597 23157292876971040392599)
                    ·
                      rfl

theorem cell22_67648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_67648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67648 prefixEnd_67648 := by exact prefixLift 67648
  have htrace : WordTrace (prefixWord ++ tailWord_67648) baseStart_67648 baseEnd_67648 := by
    simpa [prefixWord, tailWord_67648, baseEnd_67648] using wordTrace_append hprefix tailTrace_67648
  have hstable : (prefixWord ++ tailWord_67648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67648).length < 2 ^ (prefixWord ++ tailWord_67648).sum := by decide
  have hdescent : baseEnd_67648 < baseStart_67648 := by decide
  rcases family_descends (prefixWord ++ tailWord_67648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67682 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_67682 : Nat := 118140960795 + 67682 * 2 ^ 59
def prefixEnd_67682 : Nat := 4983230072969 + 3 ^ 40 * 67682 * 2
def baseEnd_67682 : Nat := 23168931771806285042495

theorem tailTrace_67682 : CollatzResearch.WordTrace tailWord_67682 prefixEnd_67682 23168931771806285042495 := by
  unfold tailWord_67682
  simp only [CollatzResearch.WordTrace]
  refine ⟨617141335201787002609325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1645710227204765340291533 617141335201787002609325)
  ·
    refine ⟨231428000700670125978497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 617141335201787002609325 231428000700670125978497)
    ·
      refine ⟨173571000525502594483873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231428000700670125978497 173571000525502594483873)
      ·
        refine ⟨130178250394126945862905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173571000525502594483873 130178250394126945862905)
        ·
          refine ⟨97633687795595209397179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130178250394126945862905 97633687795595209397179)
          ·
            refine ⟨146450531693392814095769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97633687795595209397179 146450531693392814095769)
            ·
              refine ⟨109837898770044610571827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146450531693392814095769 109837898770044610571827)
              ·
                refine ⟨164756848155066915857741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109837898770044610571827 164756848155066915857741)
                ·
                  refine ⟨61783818058150093446653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164756848155066915857741 61783818058150093446653)
                  ·
                    refine ⟨23168931771806285042495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61783818058150093446653 23168931771806285042495)
                    ·
                      rfl

theorem cell22_67682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_67682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67682 prefixEnd_67682 := by exact prefixLift 67682
  have htrace : WordTrace (prefixWord ++ tailWord_67682) baseStart_67682 baseEnd_67682 := by
    simpa [prefixWord, tailWord_67682, baseEnd_67682] using wordTrace_append hprefix tailTrace_67682
  have hstable : (prefixWord ++ tailWord_67682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67682).length < 2 ^ (prefixWord ++ tailWord_67682).sum := by decide
  have hdescent : baseEnd_67682 < baseStart_67682 := by decide
  rcases family_descends (prefixWord ++ tailWord_67682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67708 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_67708 : Nat := 118140960795 + 67708 * 2 ^ 59
def prefixEnd_67708 : Nat := 4983230072969 + 3 ^ 40 * 67708 * 2
def baseEnd_67708 : Nat := 23177832103150883892415

theorem tailTrace_67708 : CollatzResearch.WordTrace tailWord_67708 prefixEnd_67708 23177832103150883892415 := by
  unfold tailWord_67708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234756819356477225441889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1646342425808636300589185 1234756819356477225441889)
  ·
    refine ⟨926067614517357919081417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1234756819356477225441889 926067614517357919081417)
    ·
      refine ⟨694550710888018439311063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 926067614517357919081417 694550710888018439311063)
      ·
        refine ⟨1041826066332027658966595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694550710888018439311063 1041826066332027658966595)
        ·
          refine ⟨1562739099498041488449893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041826066332027658966595 1562739099498041488449893)
          ·
            refine ⟨293013581155882779084355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1562739099498041488449893 293013581155882779084355)
            ·
              refine ⟨439520371733824168626533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293013581155882779084355 439520371733824168626533)
              ·
                refine ⟨82410069700092031617475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439520371733824168626533 82410069700092031617475)
                ·
                  refine ⟨123615104550138047426213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82410069700092031617475 123615104550138047426213)
                  ·
                    refine ⟨23177832103150883892415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123615104550138047426213 23177832103150883892415)
                    ·
                      rfl

theorem cell22_67708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_67708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67708 prefixEnd_67708 := by exact prefixLift 67708
  have htrace : WordTrace (prefixWord ++ tailWord_67708) baseStart_67708 baseEnd_67708 := by
    simpa [prefixWord, tailWord_67708, baseEnd_67708] using wordTrace_append hprefix tailTrace_67708
  have hstable : (prefixWord ++ tailWord_67708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67708).length < 2 ^ (prefixWord ++ tailWord_67708).sum := by decide
  have hdescent : baseEnd_67708 < baseStart_67708 := by decide
  rcases family_descends (prefixWord ++ tailWord_67708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67721 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_67721 : Nat := 118140960795 + 67721 * 2 ^ 59
def prefixEnd_67721 : Nat := 4983230072969 + 3 ^ 40 * 67721 * 2
def baseEnd_67721 : Nat := 23182282268823183317375

theorem tailTrace_67721 : CollatzResearch.WordTrace tailWord_67721 prefixEnd_67721 23182282268823183317375 := by
  unfold tailWord_67721
  simp only [CollatzResearch.WordTrace]
  refine ⟨2469987787665857671107017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1646658525110571780738011 2469987787665857671107017)
  ·
    refine ⟨1852490840749393253330263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2469987787665857671107017 1852490840749393253330263)
    ·
      refine ⟨2778736261124089879995395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852490840749393253330263 2778736261124089879995395)
      ·
        refine ⟨4168104391686134819993093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778736261124089879995395 4168104391686134819993093)
        ·
          refine ⟨781519573441150278748705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4168104391686134819993093 781519573441150278748705)
          ·
            refine ⟨586139680080862709061529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 781519573441150278748705 586139680080862709061529)
            ·
              refine ⟨439604760060647031796147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586139680080862709061529 439604760060647031796147)
              ·
                refine ⟨659407140090970547694221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439604760060647031796147 659407140090970547694221)
                ·
                  refine ⟨247277677534113955385333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659407140090970547694221 247277677534113955385333)
                  ·
                    refine ⟨23182282268823183317375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 247277677534113955385333 23182282268823183317375)
                    ·
                      rfl

theorem cell22_67721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_67721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67721 prefixEnd_67721 := by exact prefixLift 67721
  have htrace : WordTrace (prefixWord ++ tailWord_67721) baseStart_67721 baseEnd_67721 := by
    simpa [prefixWord, tailWord_67721, baseEnd_67721] using wordTrace_append hprefix tailTrace_67721
  have hstable : (prefixWord ++ tailWord_67721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67721).length < 2 ^ (prefixWord ++ tailWord_67721).sum := by decide
  have hdescent : baseEnd_67721 < baseStart_67721 := by decide
  rcases family_descends (prefixWord ++ tailWord_67721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67877 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_67877 : Nat := 118140960795 + 67877 * 2 ^ 59
def prefixEnd_67877 : Nat := 4983230072969 + 3 ^ 40 * 67877 * 2
def baseEnd_67877 : Nat := 23235684256890776416897

theorem tailTrace_67877 : CollatzResearch.WordTrace tailWord_67877 prefixEnd_67877 23235684256890776416897 := by
  unfold tailWord_67877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2475677575100696313785885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1650451716733797542523923 2475677575100696313785885)
  ·
    refine ⟨928379090662761117669707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2475677575100696313785885 928379090662761117669707)
    ·
      refine ⟨1392568635994141676504561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928379090662761117669707 1392568635994141676504561)
      ·
        refine ⟨1044426476995606257378421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392568635994141676504561 1044426476995606257378421)
        ·
          refine ⟨97914982218338086629227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1044426476995606257378421 97914982218338086629227)
          ·
            refine ⟨146872473327507129943841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97914982218338086629227 146872473327507129943841)
            ·
              refine ⟨110154354995630347457881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146872473327507129943841 110154354995630347457881)
              ·
                refine ⟨82615766246722760593411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110154354995630347457881 82615766246722760593411)
                ·
                  refine ⟨123923649370084140890117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82615766246722760593411 123923649370084140890117)
                  ·
                    refine ⟨23235684256890776416897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123923649370084140890117 23235684256890776416897)
                    ·
                      rfl

theorem cell22_67877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_67877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67877 prefixEnd_67877 := by exact prefixLift 67877
  have htrace : WordTrace (prefixWord ++ tailWord_67877) baseStart_67877 baseEnd_67877 := by
    simpa [prefixWord, tailWord_67877, baseEnd_67877] using wordTrace_append hprefix tailTrace_67877
  have hstable : (prefixWord ++ tailWord_67877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67877).length < 2 ^ (prefixWord ++ tailWord_67877).sum := by decide
  have hdescent : baseEnd_67877 < baseStart_67877 := by decide
  rcases family_descends (prefixWord ++ tailWord_67877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67918 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_67918 : Nat := 118140960795 + 67918 * 2 ^ 59
def prefixEnd_67918 : Nat := 4983230072969 + 3 ^ 40 * 67918 * 2
def baseEnd_67918 : Nat := 23249719394780336141771

theorem tailTrace_67918 : CollatzResearch.WordTrace tailWord_67918 prefixEnd_67918 23249719394780336141771 := by
  unfold tailWord_67918
  simp only [CollatzResearch.WordTrace]
  refine ⟨309646620994020039503551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1651448645301440210685605 309646620994020039503551)
  ·
    refine ⟨464469931491030059255327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309646620994020039503551 464469931491030059255327)
    ·
      refine ⟨696704897236545088882991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464469931491030059255327 696704897236545088882991)
      ·
        refine ⟨1045057345854817633324487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696704897236545088882991 1045057345854817633324487)
        ·
          refine ⟨1567586018782226449986731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045057345854817633324487 1567586018782226449986731)
          ·
            refine ⟨2351379028173339674980097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567586018782226449986731 2351379028173339674980097)
            ·
              refine ⟨1763534271130004756235073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351379028173339674980097 1763534271130004756235073)
              ·
                refine ⟨1322650703347503567176305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763534271130004756235073 1322650703347503567176305)
                ·
                  refine ⟨991988027510627675382229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1322650703347503567176305 991988027510627675382229)
                  ·
                    refine ⟨23249719394780336141771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 991988027510627675382229 23249719394780336141771)
                    ·
                      rfl

theorem cell22_67918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_67918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67918 prefixEnd_67918 := by exact prefixLift 67918
  have htrace : WordTrace (prefixWord ++ tailWord_67918) baseStart_67918 baseEnd_67918 := by
    simpa [prefixWord, tailWord_67918, baseEnd_67918] using wordTrace_append hprefix tailTrace_67918
  have hstable : (prefixWord ++ tailWord_67918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67918).length < 2 ^ (prefixWord ++ tailWord_67918).sum := by decide
  have hdescent : baseEnd_67918 < baseStart_67918 := by decide
  rcases family_descends (prefixWord ++ tailWord_67918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67924 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_67924 : Nat := 118140960795 + 67924 * 2 ^ 59
def prefixEnd_67924 : Nat := 4983230072969 + 3 ^ 40 * 67924 * 2
def baseEnd_67924 : Nat := 23251773317398320491753

theorem tailTrace_67924 : CollatzResearch.WordTrace tailWord_67924 prefixEnd_67924 23251773317398320491753 := by
  unfold tailWord_67924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238695902965211670373413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1651594537286948893831217 1238695902965211670373413)
  ·
    refine ⟨232255481805977188195015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1238695902965211670373413 232255481805977188195015)
    ·
      refine ⟨348383222708965782292523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232255481805977188195015 348383222708965782292523)
      ·
        refine ⟨522574834063448673438785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348383222708965782292523 522574834063448673438785)
        ·
          refine ⟨391931125547586505079089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522574834063448673438785 391931125547586505079089)
          ·
            refine ⟨293948344160689878809317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391931125547586505079089 293948344160689878809317)
            ·
              refine ⟨55115314530129352276747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 293948344160689878809317 55115314530129352276747)
              ·
                refine ⟨82672971795194028415121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55115314530129352276747 82672971795194028415121)
                ·
                  refine ⟨62004728846395521311341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82672971795194028415121 62004728846395521311341)
                  ·
                    refine ⟨23251773317398320491753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62004728846395521311341 23251773317398320491753)
                    ·
                      rfl

theorem cell22_67924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_67924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67924 prefixEnd_67924 := by exact prefixLift 67924
  have htrace : WordTrace (prefixWord ++ tailWord_67924) baseStart_67924 baseEnd_67924 := by
    simpa [prefixWord, tailWord_67924, baseEnd_67924] using wordTrace_append hprefix tailTrace_67924
  have hstable : (prefixWord ++ tailWord_67924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67924).length < 2 ^ (prefixWord ++ tailWord_67924).sum := by decide
  have hdescent : baseEnd_67924 < baseStart_67924 := by decide
  rcases family_descends (prefixWord ++ tailWord_67924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67935 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 3, 3]
def baseStart_67935 : Nat := 118140960795 + 67935 * 2 ^ 59
def prefixEnd_67935 : Nat := 4983230072969 + 3 ^ 40 * 67935 * 2
def baseEnd_67935 : Nat := 23255538842197958466719

theorem tailTrace_67935 : CollatzResearch.WordTrace tailWord_67935 prefixEnd_67935 23255538842197958466719 := by
  unfold tailWord_67935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477793008890572219397259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1651862005927048146264839 2477793008890572219397259)
  ·
    refine ⟨3716689513335858329095889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2477793008890572219397259 3716689513335858329095889)
    ·
      refine ⟨2787517135001893746821917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3716689513335858329095889 2787517135001893746821917)
      ·
        refine ⟨1045318925625710155058219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2787517135001893746821917 1045318925625710155058219)
        ·
          refine ⟨1567978388438565232587329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045318925625710155058219 1567978388438565232587329)
          ·
            refine ⟨1175983791328923924440497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1567978388438565232587329 1175983791328923924440497)
            ·
              refine ⟨881987843496692943330373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175983791328923924440497 881987843496692943330373)
              ·
                refine ⟨165372720655629926874445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 881987843496692943330373 165372720655629926874445)
                ·
                  refine ⟨62014770245861222577917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165372720655629926874445 62014770245861222577917)
                  ·
                    refine ⟨23255538842197958466719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62014770245861222577917 23255538842197958466719)
                    ·
                      rfl

theorem cell22_67935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_67935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67935 prefixEnd_67935 := by exact prefixLift 67935
  have htrace : WordTrace (prefixWord ++ tailWord_67935) baseStart_67935 baseEnd_67935 := by
    simpa [prefixWord, tailWord_67935, baseEnd_67935] using wordTrace_append hprefix tailTrace_67935
  have hstable : (prefixWord ++ tailWord_67935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67935).length < 2 ^ (prefixWord ++ tailWord_67935).sum := by decide
  have hdescent : baseEnd_67935 < baseStart_67935 := by decide
  rcases family_descends (prefixWord ++ tailWord_67935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67965 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 5]
def baseStart_67965 : Nat := 118140960795 + 67965 * 2 ^ 59
def prefixEnd_67965 : Nat := 4983230072969 + 3 ^ 40 * 67965 * 2
def baseEnd_67965 : Nat := 7755269485095960072209

theorem tailTrace_67965 : CollatzResearch.WordTrace tailWord_67965 prefixEnd_67965 7755269485095960072209 := by
  unfold tailWord_67965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478887198781887342989349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1652591465854591561992899 2478887198781887342989349)
  ·
    refine ⟨464791349771603876810503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2478887198781887342989349 464791349771603876810503)
    ·
      refine ⟨697187024657405815215755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464791349771603876810503 697187024657405815215755)
      ·
        refine ⟨1045780536986108722823633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697187024657405815215755 1045780536986108722823633)
        ·
          refine ⟨784335402739581542117725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045780536986108722823633 784335402739581542117725)
          ·
            refine ⟨294125776027343078294147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 784335402739581542117725 294125776027343078294147)
            ·
              refine ⟨441188664041014617441221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294125776027343078294147 441188664041014617441221)
              ·
                refine ⟨82722874507690240770229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441188664041014617441221 82722874507690240770229)
                ·
                  refine ⟨7755269485095960072209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82722874507690240770229 7755269485095960072209)
                  ·
                    rfl

theorem cell22_67965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_67965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67965 prefixEnd_67965 := by exact prefixLift 67965
  have htrace : WordTrace (prefixWord ++ tailWord_67965) baseStart_67965 baseEnd_67965 := by
    simpa [prefixWord, tailWord_67965, baseEnd_67965] using wordTrace_append hprefix tailTrace_67965
  have hstable : (prefixWord ++ tailWord_67965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67965).length < 2 ^ (prefixWord ++ tailWord_67965).sum := by decide
  have hdescent : baseEnd_67965 < baseStart_67965 := by decide
  rcases family_descends (prefixWord ++ tailWord_67965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67980 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_67980 : Nat := 118140960795 + 67980 * 2 ^ 59
def prefixEnd_67980 : Nat := 4983230072969 + 3 ^ 40 * 67980 * 2
def baseEnd_67980 : Nat := 23270943261832841091581

theorem tailTrace_67980 : CollatzResearch.WordTrace tailWord_67980 prefixEnd_67980 23270943261832841091581 := by
  unfold tailWord_67980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239717146863772452392697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1652956195818363269856929 1239717146863772452392697)
  ·
    refine ⟨929787860147829339294523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239717146863772452392697 929787860147829339294523)
    ·
      refine ⟨1394681790221744008941785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929787860147829339294523 1394681790221744008941785)
      ·
        refine ⟨1046011342666308006706339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394681790221744008941785 1046011342666308006706339)
        ·
          refine ⟨1569017013999462010059509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046011342666308006706339 1569017013999462010059509)
          ·
            refine ⟨147095345062449563443079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1569017013999462010059509 147095345062449563443079)
            ·
              refine ⟨220643017593674345164619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147095345062449563443079 220643017593674345164619)
              ·
                refine ⟨330964526390511517746929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220643017593674345164619 330964526390511517746929)
                ·
                  refine ⟨248223394792883638310197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330964526390511517746929 248223394792883638310197)
                  ·
                    refine ⟨23270943261832841091581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 248223394792883638310197 23270943261832841091581)
                    ·
                      rfl

theorem cell22_67980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_67980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67980 prefixEnd_67980 := by exact prefixLift 67980
  have htrace : WordTrace (prefixWord ++ tailWord_67980) baseStart_67980 baseEnd_67980 := by
    simpa [prefixWord, tailWord_67980, baseEnd_67980] using wordTrace_append hprefix tailTrace_67980
  have hstable : (prefixWord ++ tailWord_67980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67980).length < 2 ^ (prefixWord ++ tailWord_67980).sum := by decide
  have hdescent : baseEnd_67980 < baseStart_67980 := by decide
  rcases family_descends (prefixWord ++ tailWord_67980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67982 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_67982 : Nat := 118140960795 + 67982 * 2 ^ 59
def prefixEnd_67982 : Nat := 4983230072969 + 3 ^ 40 * 67982 * 2
def baseEnd_67982 : Nat := 7757209300901834180525

theorem tailTrace_67982 : CollatzResearch.WordTrace tailWord_67982 prefixEnd_67982 7757209300901834180525 := by
  unfold tailWord_67982
  simp only [CollatzResearch.WordTrace]
  refine ⟨309938404965037405794775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1653004826480199497572133 309938404965037405794775)
  ·
    refine ⟨464907607447556108692163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309938404965037405794775 464907607447556108692163)
    ·
      refine ⟨697361411171334163038245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464907607447556108692163 697361411171334163038245)
      ·
        refine ⟨130755264594625155569671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 697361411171334163038245 130755264594625155569671)
        ·
          refine ⟨196132896891937733354507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130755264594625155569671 196132896891937733354507)
          ·
            refine ⟨294199345337906600031761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196132896891937733354507 294199345337906600031761)
            ·
              refine ⟨220649509003429950023821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294199345337906600031761 220649509003429950023821)
              ·
                refine ⟨82743565876286231258933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220649509003429950023821 82743565876286231258933)
                ·
                  refine ⟨7757209300901834180525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82743565876286231258933 7757209300901834180525)
                  ·
                    rfl

theorem cell22_67982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_67982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67982 prefixEnd_67982 := by exact prefixLift 67982
  have htrace : WordTrace (prefixWord ++ tailWord_67982) baseStart_67982 baseEnd_67982 := by
    simpa [prefixWord, tailWord_67982, baseEnd_67982] using wordTrace_append hprefix tailTrace_67982
  have hstable : (prefixWord ++ tailWord_67982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67982).length < 2 ^ (prefixWord ++ tailWord_67982).sum := by decide
  have hdescent : baseEnd_67982 < baseStart_67982 := by decide
  rcases family_descends (prefixWord ++ tailWord_67982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67990 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_67990 : Nat := 118140960795 + 67990 * 2 ^ 59
def prefixEnd_67990 : Nat := 4983230072969 + 3 ^ 40 * 67990 * 2
def baseEnd_67990 : Nat := 23274366466196148341551

theorem tailTrace_67990 : CollatzResearch.WordTrace tailWord_67990 prefixEnd_67990 23274366466196148341551 := by
  unfold tailWord_67990
  simp only [CollatzResearch.WordTrace]
  refine ⟨154987438980707288290589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1653199349127544408432949 154987438980707288290589)
  ·
    refine ⟨58120289617765233108971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154987438980707288290589 58120289617765233108971)
    ·
      refine ⟨87180434426647849663457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58120289617765233108971 87180434426647849663457)
      ·
        refine ⟨65385325819985887247593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87180434426647849663457 65385325819985887247593)
        ·
          refine ⟨49038994364989415435695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65385325819985887247593 49038994364989415435695)
          ·
            refine ⟨73558491547484123153543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49038994364989415435695 73558491547484123153543)
            ·
              refine ⟨110337737321226184730315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73558491547484123153543 110337737321226184730315)
              ·
                refine ⟨165506605981839277095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110337737321226184730315 165506605981839277095473)
                ·
                  refine ⟨124129954486379457821605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165506605981839277095473 124129954486379457821605)
                  ·
                    refine ⟨23274366466196148341551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124129954486379457821605 23274366466196148341551)
                    ·
                      rfl

theorem cell22_67990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_67990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_67990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_67990 prefixEnd_67990 := by exact prefixLift 67990
  have htrace : WordTrace (prefixWord ++ tailWord_67990) baseStart_67990 baseEnd_67990 := by
    simpa [prefixWord, tailWord_67990, baseEnd_67990] using wordTrace_append hprefix tailTrace_67990
  have hstable : (prefixWord ++ tailWord_67990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67990).length < 2 ^ (prefixWord ++ tailWord_67990).sum := by decide
  have hdescent : baseEnd_67990 < baseStart_67990 := by decide
  rcases family_descends (prefixWord ++ tailWord_67990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68033 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 5]
def baseStart_68033 : Nat := 118140960795 + 68033 * 2 ^ 59
def prefixEnd_68033 : Nat := 4983230072969 + 3 ^ 40 * 68033 * 2
def baseEnd_68033 : Nat := 7763028748319456505473

theorem tailTrace_68033 : CollatzResearch.WordTrace tailWord_68033 prefixEnd_68033 7763028748319456505473 := by
  unfold tailWord_68033
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481367362535534956464753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1654244908357023304309835 2481367362535534956464753)
  ·
    refine ⟨1861025521901651217348565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2481367362535534956464753 1861025521901651217348565)
    ·
      refine ⟨43617785669569950406607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1861025521901651217348565 43617785669569950406607)
      ·
        refine ⟨65426678504354925609911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43617785669569950406607 65426678504354925609911)
        ·
          refine ⟨98140017756532388414867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65426678504354925609911 98140017756532388414867)
          ·
            refine ⟨147210026634798582622301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98140017756532388414867 147210026634798582622301)
            ·
              refine ⟨55203759988049468483363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147210026634798582622301 55203759988049468483363)
              ·
                refine ⟨82805639982074202725045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55203759988049468483363 82805639982074202725045)
                ·
                  refine ⟨7763028748319456505473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82805639982074202725045 7763028748319456505473)
                  ·
                    rfl

theorem cell22_68033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_68033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68033 prefixEnd_68033 := by exact prefixLift 68033
  have htrace : WordTrace (prefixWord ++ tailWord_68033) baseStart_68033 baseEnd_68033 := by
    simpa [prefixWord, tailWord_68033, baseEnd_68033] using wordTrace_append hprefix tailTrace_68033
  have hstable : (prefixWord ++ tailWord_68033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68033).length < 2 ^ (prefixWord ++ tailWord_68033).sum := by decide
  have hdescent : baseEnd_68033 < baseStart_68033 := by decide
  rcases family_descends (prefixWord ++ tailWord_68033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68040 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_68040 : Nat := 118140960795 + 68040 * 2 ^ 59
def prefixEnd_68040 : Nat := 4983230072969 + 3 ^ 40 * 68040 * 2
def baseEnd_68040 : Nat := 23291482488012684591397

theorem tailTrace_68040 : CollatzResearch.WordTrace tailWord_68040 prefixEnd_68040 23291482488012684591397 := by
  unfold tailWord_68040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240811336755087575984787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1654415115673450101313049 1240811336755087575984787)
  ·
    refine ⟨1861217005132631363977181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1240811336755087575984787 1861217005132631363977181)
    ·
      refine ⟨697956376924736761491443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1861217005132631363977181 697956376924736761491443)
      ·
        refine ⟨1046934565387105142237165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697956376924736761491443 1046934565387105142237165)
        ·
          refine ⟨392600462020164428338937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1046934565387105142237165 392600462020164428338937)
          ·
            refine ⟨294450346515123321254203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392600462020164428338937 294450346515123321254203)
            ·
              refine ⟨441675519772684981881305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294450346515123321254203 441675519772684981881305)
              ·
                refine ⟨331256639829513736410979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441675519772684981881305 331256639829513736410979)
                ·
                  refine ⟨496884959744270604616469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331256639829513736410979 496884959744270604616469)
                  ·
                    refine ⟨23291482488012684591397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 496884959744270604616469 23291482488012684591397)
                    ·
                      rfl

theorem cell22_68040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_68040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68040 prefixEnd_68040 := by exact prefixLift 68040
  have htrace : WordTrace (prefixWord ++ tailWord_68040) baseStart_68040 baseEnd_68040 := by
    simpa [prefixWord, tailWord_68040, baseEnd_68040] using wordTrace_append hprefix tailTrace_68040
  have hstable : (prefixWord ++ tailWord_68040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68040).length < 2 ^ (prefixWord ++ tailWord_68040).sum := by decide
  have hdescent : baseEnd_68040 < baseStart_68040 := by decide
  rcases family_descends (prefixWord ++ tailWord_68040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68138 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_68138 : Nat := 118140960795 + 68138 * 2 ^ 59
def prefixEnd_68138 : Nat := 4983230072969 + 3 ^ 40 * 68138 * 2
def baseEnd_68138 : Nat := 23325029890773095641097

theorem tailTrace_68138 : CollatzResearch.WordTrace tailWord_68138 prefixEnd_68138 23325029890773095641097 := by
  unfold tailWord_68138
  simp only [CollatzResearch.WordTrace]
  refine ⟨621299256788784472259267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1656798018103425259358045 621299256788784472259267)
  ·
    refine ⟨931948885183176708388901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 621299256788784472259267 931948885183176708388901)
    ·
      refine ⟨174740415971845632822919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 931948885183176708388901 174740415971845632822919)
      ·
        refine ⟨262110623957768449234379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174740415971845632822919 262110623957768449234379)
        ·
          refine ⟨393165935936652673851569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262110623957768449234379 393165935936652673851569)
          ·
            refine ⟨294874451952489505388677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393165935936652673851569 294874451952489505388677)
            ·
              refine ⟨55288959741091782260377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294874451952489505388677 55288959741091782260377)
              ·
                refine ⟨41466719805818836695283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55288959741091782260377 41466719805818836695283)
                ·
                  refine ⟨62200079708728255042925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41466719805818836695283 62200079708728255042925)
                  ·
                    refine ⟨23325029890773095641097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62200079708728255042925 23325029890773095641097)
                    ·
                      rfl

theorem cell22_68138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_68138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68138 prefixEnd_68138 := by exact prefixLift 68138
  have htrace : WordTrace (prefixWord ++ tailWord_68138) baseStart_68138 baseEnd_68138 := by
    simpa [prefixWord, tailWord_68138, baseEnd_68138] using wordTrace_append hprefix tailTrace_68138
  have hstable : (prefixWord ++ tailWord_68138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68138).length < 2 ^ (prefixWord ++ tailWord_68138).sum := by decide
  have hdescent : baseEnd_68138 < baseStart_68138 := by decide
  rcases family_descends (prefixWord ++ tailWord_68138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68177 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_68177 : Nat := 118140960795 + 68177 * 2 ^ 59
def prefixEnd_68177 : Nat := 4983230072969 + 3 ^ 40 * 68177 * 2
def baseEnd_68177 : Nat := 23338380387789993915977

theorem tailTrace_68177 : CollatzResearch.WordTrace tailWord_68177 prefixEnd_68177 23338380387789993915977 := by
  unfold tailWord_68177
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486619474013847549706785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1657746316009231699804523 2486619474013847549706785)
  ·
    refine ⟨1864964605510385662280089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2486619474013847549706785 1864964605510385662280089)
    ·
      refine ⟨1398723454132789246710067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1864964605510385662280089 1398723454132789246710067)
      ·
        refine ⟨2098085181199183870065101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398723454132789246710067 2098085181199183870065101)
        ·
          refine ⟨786781942949693951274413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2098085181199183870065101 786781942949693951274413)
          ·
            refine ⟨295043228606135231727905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 786781942949693951274413 295043228606135231727905)
            ·
              refine ⟨221282421454601423795929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295043228606135231727905 221282421454601423795929)
              ·
                refine ⟨165961816090951067846947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221282421454601423795929 165961816090951067846947)
                ·
                  refine ⟨248942724136426601770421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165961816090951067846947 248942724136426601770421)
                  ·
                    refine ⟨23338380387789993915977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 248942724136426601770421 23338380387789993915977)
                    ·
                      rfl

theorem cell22_68177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_68177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68177 prefixEnd_68177 := by exact prefixLift 68177
  have htrace : WordTrace (prefixWord ++ tailWord_68177) baseStart_68177 baseEnd_68177 := by
    simpa [prefixWord, tailWord_68177, baseEnd_68177] using wordTrace_append hprefix tailTrace_68177
  have hstable : (prefixWord ++ tailWord_68177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68177).length < 2 ^ (prefixWord ++ tailWord_68177).sum := by decide
  have hdescent : baseEnd_68177 < baseStart_68177 := by decide
  rcases family_descends (prefixWord ++ tailWord_68177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68192 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_68192 : Nat := 118140960795 + 68192 * 2 ^ 59
def prefixEnd_68192 : Nat := 4983230072969 + 3 ^ 40 * 68192 * 2
def baseEnd_68192 : Nat := 23343515194334954790931

theorem tailTrace_68192 : CollatzResearch.WordTrace tailWord_68192 prefixEnd_68192 23343515194334954790931 := by
  unfold tailWord_68192
  simp only [CollatzResearch.WordTrace]
  refine ⟨1243583284479752555751415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1658111045973003407668553 1243583284479752555751415)
  ·
    refine ⟨1865374926719628833627123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1243583284479752555751415 1865374926719628833627123)
    ·
      refine ⟨2798062390079443250440685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1865374926719628833627123 2798062390079443250440685)
      ·
        refine ⟨1049273396279791218915257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2798062390079443250440685 1049273396279791218915257)
        ·
          refine ⟨786955047209843414186443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1049273396279791218915257 786955047209843414186443)
          ·
            refine ⟨1180432570814765121279665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786955047209843414186443 1180432570814765121279665)
            ·
              refine ⟨885324428111073840959749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1180432570814765121279665 885324428111073840959749)
              ·
                refine ⟨165998330270826345179953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 885324428111073840959749 165998330270826345179953)
                ·
                  refine ⟨124498747703119758884965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165998330270826345179953 124498747703119758884965)
                  ·
                    refine ⟨23343515194334954790931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124498747703119758884965 23343515194334954790931)
                    ·
                      rfl

theorem cell22_68192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_68192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68192 prefixEnd_68192 := by exact prefixLift 68192
  have htrace : WordTrace (prefixWord ++ tailWord_68192) baseStart_68192 baseEnd_68192 := by
    simpa [prefixWord, tailWord_68192, baseEnd_68192] using wordTrace_append hprefix tailTrace_68192
  have hstable : (prefixWord ++ tailWord_68192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68192).length < 2 ^ (prefixWord ++ tailWord_68192).sum := by decide
  have hdescent : baseEnd_68192 < baseStart_68192 := by decide
  rcases family_descends (prefixWord ++ tailWord_68192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68224 : List Nat := [2, 1, 1, 2, 1, 7, 2, 6]
def baseStart_68224 : Nat := 118140960795 + 68224 * 2 ^ 59
def prefixEnd_68224 : Nat := 4983230072969 + 3 ^ 40 * 68224 * 2
def baseEnd_68224 : Nat := 2594941049810837554537

theorem tailTrace_68224 : CollatzResearch.WordTrace tailWord_68224 prefixEnd_68224 2594941049810837554537 := by
  unfold tailWord_68224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244166852421787288333863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1658889136562383051111817 1244166852421787288333863)
  ·
    refine ⟨1866250278632680932500795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1244166852421787288333863 1866250278632680932500795)
    ·
      refine ⟨2799375417949021398751193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866250278632680932500795 2799375417949021398751193)
      ·
        refine ⟨2099531563461766049063395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2799375417949021398751193 2099531563461766049063395)
        ·
          refine ⟨3149297345192649073595093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099531563461766049063395 3149297345192649073595093)
          ·
            refine ⟨73811656527952712662385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3149297345192649073595093 73811656527952712662385)
            ·
              refine ⟨55358742395964534496789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73811656527952712662385 55358742395964534496789)
              ·
                refine ⟨2594941049810837554537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55358742395964534496789 2594941049810837554537)
                ·
                  rfl

theorem cell22_68224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_68224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68224 prefixEnd_68224 := by exact prefixLift 68224
  have htrace : WordTrace (prefixWord ++ tailWord_68224) baseStart_68224 baseEnd_68224 := by
    simpa [prefixWord, tailWord_68224, baseEnd_68224] using wordTrace_append hprefix tailTrace_68224
  have hstable : (prefixWord ++ tailWord_68224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68224).length < 2 ^ (prefixWord ++ tailWord_68224).sum := by decide
  have hdescent : baseEnd_68224 < baseStart_68224 := by decide
  rcases family_descends (prefixWord ++ tailWord_68224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68254 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_68254 : Nat := 118140960795 + 68254 * 2 ^ 59
def prefixEnd_68254 : Nat := 4983230072969 + 3 ^ 40 * 68254 * 2
def baseEnd_68254 : Nat := 23364739061387459740741

theorem tailTrace_68254 : CollatzResearch.WordTrace tailWord_68254 prefixEnd_68254 23364739061387459740741 := by
  unfold tailWord_68254
  simp only [CollatzResearch.WordTrace]
  refine ⟨311178486841861212532477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1659618596489926466839877 311178486841861212532477)
  ·
    refine ⟨116691932565697954699679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 311178486841861212532477 116691932565697954699679)
    ·
      refine ⟨175037898848546932049519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116691932565697954699679 175037898848546932049519)
      ·
        refine ⟨262556848272820398074279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175037898848546932049519 262556848272820398074279)
        ·
          refine ⟨393835272409230597111419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262556848272820398074279 393835272409230597111419)
          ·
            refine ⟨590752908613845895667129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393835272409230597111419 590752908613845895667129)
            ·
              refine ⟨443064681460384421750347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590752908613845895667129 443064681460384421750347)
              ·
                refine ⟨664597022190576632625521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443064681460384421750347 664597022190576632625521)
                ·
                  refine ⟨498447766642932474469141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 664597022190576632625521 498447766642932474469141)
                  ·
                    refine ⟨23364739061387459740741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 498447766642932474469141 23364739061387459740741)
                    ·
                      rfl

theorem cell22_68254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_68254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68254 prefixEnd_68254 := by exact prefixLift 68254
  have htrace : WordTrace (prefixWord ++ tailWord_68254) baseStart_68254 baseEnd_68254 := by
    simpa [prefixWord, tailWord_68254, baseEnd_68254] using wordTrace_append hprefix tailTrace_68254
  have hstable : (prefixWord ++ tailWord_68254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68254).length < 2 ^ (prefixWord ++ tailWord_68254).sum := by decide
  have hdescent : baseEnd_68254 < baseStart_68254 := by decide
  rcases family_descends (prefixWord ++ tailWord_68254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68316 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_68316 : Nat := 118140960795 + 68316 * 2 ^ 59
def prefixEnd_68316 : Nat := 4983230072969 + 3 ^ 40 * 68316 * 2
def baseEnd_68316 : Nat := 23385962928439964690551

theorem tailTrace_68316 : CollatzResearch.WordTrace tailWord_68316 prefixEnd_68316 23385962928439964690551 := by
  unfold tailWord_68316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245844610255137144508401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1661126147006849526011201 1245844610255137144508401)
  ·
    refine ⟨934383457691352858381301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1245844610255137144508401 934383457691352858381301)
    ·
      refine ⟨87598449158564330473247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 934383457691352858381301 87598449158564330473247)
      ·
        refine ⟨131397673737846495709871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87598449158564330473247 131397673737846495709871)
        ·
          refine ⟨197096510606769743564807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131397673737846495709871 197096510606769743564807)
          ·
            refine ⟨295644765910154615347211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197096510606769743564807 295644765910154615347211)
            ·
              refine ⟨443467148865231923020817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295644765910154615347211 443467148865231923020817)
              ·
                refine ⟨332600361648923942265613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443467148865231923020817 332600361648923942265613)
                ·
                  refine ⟨124725135618346478349605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332600361648923942265613 124725135618346478349605)
                  ·
                    refine ⟨23385962928439964690551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124725135618346478349605 23385962928439964690551)
                    ·
                      rfl

theorem cell22_68316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_68316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68316 prefixEnd_68316 := by exact prefixLift 68316
  have htrace : WordTrace (prefixWord ++ tailWord_68316) baseStart_68316 baseEnd_68316 := by
    simpa [prefixWord, tailWord_68316, baseEnd_68316] using wordTrace_append hprefix tailTrace_68316
  have hstable : (prefixWord ++ tailWord_68316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68316).length < 2 ^ (prefixWord ++ tailWord_68316).sum := by decide
  have hdescent : baseEnd_68316 < baseStart_68316 := by decide
  rcases family_descends (prefixWord ++ tailWord_68316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68350 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_68350 : Nat := 118140960795 + 68350 * 2 ^ 59
def prefixEnd_68350 : Nat := 4983230072969 + 3 ^ 40 * 68350 * 2
def baseEnd_68350 : Nat := 23397601823275209340447

theorem tailTrace_68350 : CollatzResearch.WordTrace tailWord_68350 prefixEnd_68350 23397601823275209340447 := by
  unfold tailWord_68350
  simp only [CollatzResearch.WordTrace]
  refine ⟨311616162798387261969313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1661952868258065397169669 311616162798387261969313)
  ·
    refine ⟨233712122098790446476985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311616162798387261969313 233712122098790446476985)
    ·
      refine ⟨175284091574092834857739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233712122098790446476985 175284091574092834857739)
      ·
        refine ⟨262926137361139252286609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175284091574092834857739 262926137361139252286609)
        ·
          refine ⟨197194603020854439214957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262926137361139252286609 197194603020854439214957)
          ·
            refine ⟨73947976132820414705609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197194603020854439214957 73947976132820414705609)
            ·
              refine ⟨55460982099615311029207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73947976132820414705609 55460982099615311029207)
              ·
                refine ⟨83191473149422966543811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55460982099615311029207 83191473149422966543811)
                ·
                  refine ⟨124787209724134449815717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83191473149422966543811 124787209724134449815717)
                  ·
                    refine ⟨23397601823275209340447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124787209724134449815717 23397601823275209340447)
                    ·
                      rfl

theorem cell22_68350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_68350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68350 prefixEnd_68350 := by exact prefixLift 68350
  have htrace : WordTrace (prefixWord ++ tailWord_68350) baseStart_68350 baseEnd_68350 := by
    simpa [prefixWord, tailWord_68350, baseEnd_68350] using wordTrace_append hprefix tailTrace_68350
  have hstable : (prefixWord ++ tailWord_68350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68350).length < 2 ^ (prefixWord ++ tailWord_68350).sum := by decide
  have hdescent : baseEnd_68350 < baseStart_68350 := by decide
  rcases family_descends (prefixWord ++ tailWord_68350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68357 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_68357 : Nat := 118140960795 + 68357 * 2 ^ 59
def prefixEnd_68357 : Nat := 4983230072969 + 3 ^ 40 * 68357 * 2
def baseEnd_68357 : Nat := 23399998066329524415425

theorem tailTrace_68357 : CollatzResearch.WordTrace tailWord_68357 prefixEnd_68357 23399998066329524415425 := by
  unfold tailWord_68357
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493184613361738291259325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1662123075574492194172883 2493184613361738291259325)
  ·
    refine ⟨934944230010651859222247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2493184613361738291259325 934944230010651859222247)
    ·
      refine ⟨1402416345015977788833371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934944230010651859222247 1402416345015977788833371)
      ·
        refine ⟨2103624517523966683250057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402416345015977788833371 2103624517523966683250057)
        ·
          refine ⟨1577718388142975012437543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2103624517523966683250057 1577718388142975012437543)
          ·
            refine ⟨2366577582214462518656315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577718388142975012437543 2366577582214462518656315)
            ·
              refine ⟨3549866373321693777984473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366577582214462518656315 3549866373321693777984473)
              ·
                refine ⟨2662399779991270333488355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3549866373321693777984473 2662399779991270333488355)
                ·
                  refine ⟨3993599669986905500232533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662399779991270333488355 3993599669986905500232533)
                  ·
                    refine ⟨23399998066329524415425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3993599669986905500232533 23399998066329524415425)
                    ·
                      rfl

theorem cell22_68357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_68357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68357 prefixEnd_68357 := by exact prefixLift 68357
  have htrace : WordTrace (prefixWord ++ tailWord_68357) baseStart_68357 baseEnd_68357 := by
    simpa [prefixWord, tailWord_68357, baseEnd_68357] using wordTrace_append hprefix tailTrace_68357
  have hstable : (prefixWord ++ tailWord_68357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68357).length < 2 ^ (prefixWord ++ tailWord_68357).sum := by decide
  have hdescent : baseEnd_68357 < baseStart_68357 := by decide
  rcases family_descends (prefixWord ++ tailWord_68357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68359 : List Nat := [1, 1, 4, 4, 1, 2, 9]
def baseStart_68359 : Nat := 118140960795 + 68359 * 2 ^ 59
def prefixEnd_68359 : Nat := 4983230072969 + 3 ^ 40 * 68359 * 2
def baseEnd_68359 : Nat := 866691952118599476497

theorem tailTrace_68359 : CollatzResearch.WordTrace tailWord_68359 prefixEnd_68359 866691952118599476497 := by
  unfold tailWord_68359
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493257559354492632832131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1662171706236328421888087 2493257559354492632832131)
  ·
    refine ⟨3739886339031738949248197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493257559354492632832131 3739886339031738949248197)
    ·
      refine ⟨701228688568451052984037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3739886339031738949248197 701228688568451052984037)
      ·
        refine ⟨131480379106584572434507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 701228688568451052984037 131480379106584572434507)
        ·
          refine ⟨197220568659876858651761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131480379106584572434507 197220568659876858651761)
          ·
            refine ⟨147915426494907643988821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197220568659876858651761 147915426494907643988821)
            ·
              refine ⟨866691952118599476497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 147915426494907643988821 866691952118599476497)
              ·
                rfl

theorem cell22_68359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 9].length) (baseStart_68359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68359 prefixEnd_68359 := by exact prefixLift 68359
  have htrace : WordTrace (prefixWord ++ tailWord_68359) baseStart_68359 baseEnd_68359 := by
    simpa [prefixWord, tailWord_68359, baseEnd_68359] using wordTrace_append hprefix tailTrace_68359
  have hstable : (prefixWord ++ tailWord_68359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68359).length < 2 ^ (prefixWord ++ tailWord_68359).sum := by decide
  have hdescent : baseEnd_68359 < baseStart_68359 := by decide
  rcases family_descends (prefixWord ++ tailWord_68359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68425 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 1, 3]
def baseStart_68425 : Nat := 118140960795 + 68425 * 2 ^ 59
def prefixEnd_68425 : Nat := 4983230072969 + 3 ^ 40 * 68425 * 2
def baseEnd_68425 : Nat := 23423275856000013715217

theorem tailTrace_68425 : CollatzResearch.WordTrace tailWord_68425 prefixEnd_68425 23423275856000013715217 := by
  unfold tailWord_68425
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495664777115385904734729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1663776518076923936489819 2495664777115385904734729)
  ·
    refine ⟨1871748582836539428551047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2495664777115385904734729 1871748582836539428551047)
    ·
      refine ⟨2807622874254809142826571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871748582836539428551047 2807622874254809142826571)
      ·
        refine ⟨4211434311382213714239857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807622874254809142826571 4211434311382213714239857)
        ·
          refine ⟨3158575733536660285679893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4211434311382213714239857 3158575733536660285679893)
          ·
            refine ⟨148058237509530950891245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3158575733536660285679893 148058237509530950891245)
            ·
              refine ⟨55521839066074106584217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148058237509530950891245 55521839066074106584217)
              ·
                refine ⟨41641379299555579938163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55521839066074106584217 41641379299555579938163)
                ·
                  refine ⟨62462068949333369907245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41641379299555579938163 62462068949333369907245)
                  ·
                    refine ⟨23423275856000013715217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62462068949333369907245 23423275856000013715217)
                    ·
                      rfl

theorem cell22_68425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_68425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68425 prefixEnd_68425 := by exact prefixLift 68425
  have htrace : WordTrace (prefixWord ++ tailWord_68425) baseStart_68425 baseEnd_68425 := by
    simpa [prefixWord, tailWord_68425, baseEnd_68425] using wordTrace_append hprefix tailTrace_68425
  have hstable : (prefixWord ++ tailWord_68425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68425).length < 2 ^ (prefixWord ++ tailWord_68425).sum := by decide
  have hdescent : baseEnd_68425 < baseStart_68425 := by decide
  rcases family_descends (prefixWord ++ tailWord_68425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68451 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 3, 4]
def baseStart_68451 : Nat := 118140960795 + 68451 * 2 ^ 59
def prefixEnd_68451 : Nat := 4983230072969 + 3 ^ 40 * 68451 * 2
def baseEnd_68451 : Nat := 23432176187344612565137

theorem tailTrace_68451 : CollatzResearch.WordTrace tailWord_68451 prefixEnd_68451 23432176187344612565137 := by
  unfold tailWord_68451
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496613075021192345181207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1664408716680794896787471 2496613075021192345181207)
  ·
    refine ⟨3744919612531788517771811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496613075021192345181207 3744919612531788517771811)
    ·
      refine ⟨5617379418797682776657717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744919612531788517771811 5617379418797682776657717)
      ·
        refine ⟨526629320512282760311661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5617379418797682776657717 526629320512282760311661)
        ·
          refine ⟨197485995192106035116873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 526629320512282760311661 197485995192106035116873)
          ·
            refine ⟨148114496394079526337655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197485995192106035116873 148114496394079526337655)
            ·
              refine ⟨222171744591119289506483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148114496394079526337655 222171744591119289506483)
              ·
                refine ⟨333257616886678934259725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222171744591119289506483 333257616886678934259725)
                ·
                  refine ⟨124971606332504600347397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333257616886678934259725 124971606332504600347397)
                  ·
                    refine ⟨23432176187344612565137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124971606332504600347397 23432176187344612565137)
                    ·
                      rfl

theorem cell22_68451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 4].length) (baseStart_68451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68451 prefixEnd_68451 := by exact prefixLift 68451
  have htrace : WordTrace (prefixWord ++ tailWord_68451) baseStart_68451 baseEnd_68451 := by
    simpa [prefixWord, tailWord_68451, baseEnd_68451] using wordTrace_append hprefix tailTrace_68451
  have hstable : (prefixWord ++ tailWord_68451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68451).length < 2 ^ (prefixWord ++ tailWord_68451).sum := by decide
  have hdescent : baseEnd_68451 < baseStart_68451 := by decide
  rcases family_descends (prefixWord ++ tailWord_68451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68464 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_68464 : Nat := 118140960795 + 68464 * 2 ^ 59
def prefixEnd_68464 : Nat := 4983230072969 + 3 ^ 40 * 68464 * 2
def baseEnd_68464 : Nat := 23436626353016911990097

theorem tailTrace_68464 : CollatzResearch.WordTrace tailWord_68464 prefixEnd_68464 23436626353016911990097 := by
  unfold tailWord_68464
  simp only [CollatzResearch.WordTrace]
  refine ⟨1248543611987047782702223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1664724815982730376936297 1248543611987047782702223)
  ·
    refine ⟨1872815417980571674053335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1248543611987047782702223 1872815417980571674053335)
    ·
      refine ⟨2809223126970857511080003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1872815417980571674053335 2809223126970857511080003)
      ·
        refine ⟨4213834690456286266620005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2809223126970857511080003 4213834690456286266620005)
        ·
          refine ⟨790094004460553674991251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4213834690456286266620005 790094004460553674991251)
          ·
            refine ⟨1185141006690830512486877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790094004460553674991251 1185141006690830512486877)
            ·
              refine ⟨444427877509061442182579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1185141006690830512486877 444427877509061442182579)
              ·
                refine ⟨666641816263592163273869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444427877509061442182579 666641816263592163273869)
                ·
                  refine ⟨249990681098847061227701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 666641816263592163273869 249990681098847061227701)
                  ·
                    refine ⟨23436626353016911990097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 249990681098847061227701 23436626353016911990097)
                    ·
                      rfl

theorem cell22_68464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_68464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68464 prefixEnd_68464 := by exact prefixLift 68464
  have htrace : WordTrace (prefixWord ++ tailWord_68464) baseStart_68464 baseEnd_68464 := by
    simpa [prefixWord, tailWord_68464, baseEnd_68464] using wordTrace_append hprefix tailTrace_68464
  have hstable : (prefixWord ++ tailWord_68464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68464).length < 2 ^ (prefixWord ++ tailWord_68464).sum := by decide
  have hdescent : baseEnd_68464 < baseStart_68464 := by decide
  rcases family_descends (prefixWord ++ tailWord_68464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68513 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_68513 : Nat := 118140960795 + 68513 * 2 ^ 59
def prefixEnd_68513 : Nat := 4983230072969 + 3 ^ 40 * 68513 * 2
def baseEnd_68513 : Nat := 23453400054397117514947

theorem tailTrace_68513 : CollatzResearch.WordTrace tailWord_68513 prefixEnd_68513 23453400054397117514947 := by
  unfold tailWord_68513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498874400796576933938193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1665916267197717955958795 2498874400796576933938193)
  ·
    refine ⟨1874155800597432700453645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2498874400796576933938193 1874155800597432700453645)
    ·
      refine ⟨702808425224037262670117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1874155800597432700453645 702808425224037262670117)
      ·
        refine ⟨131776579729506986750647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 702808425224037262670117 131776579729506986750647)
        ·
          refine ⟨197664869594260480125971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131776579729506986750647 197664869594260480125971)
          ·
            refine ⟨296497304391390720188957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197664869594260480125971 296497304391390720188957)
            ·
              refine ⟨111186489146771520070859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296497304391390720188957 111186489146771520070859)
              ·
                refine ⟨166779733720157280106289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111186489146771520070859 166779733720157280106289)
                ·
                  refine ⟨125084800290117960079717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166779733720157280106289 125084800290117960079717)
                  ·
                    refine ⟨23453400054397117514947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125084800290117960079717 23453400054397117514947)
                    ·
                      rfl

theorem cell22_68513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_68513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68513 prefixEnd_68513 := by exact prefixLift 68513
  have htrace : WordTrace (prefixWord ++ tailWord_68513) baseStart_68513 baseEnd_68513 := by
    simpa [prefixWord, tailWord_68513, baseEnd_68513] using wordTrace_append hprefix tailTrace_68513
  have hstable : (prefixWord ++ tailWord_68513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68513).length < 2 ^ (prefixWord ++ tailWord_68513).sum := by decide
  have hdescent : baseEnd_68513 < baseStart_68513 := by decide
  rcases family_descends (prefixWord ++ tailWord_68513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68524 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_68524 : Nat := 118140960795 + 68524 * 2 ^ 59
def prefixEnd_68524 : Nat := 4983230072969 + 3 ^ 40 * 68524 * 2
def baseEnd_68524 : Nat := 23457165579196755489913

theorem tailTrace_68524 : CollatzResearch.WordTrace tailWord_68524 prefixEnd_68524 23457165579196755489913 := by
  unfold tailWord_68524
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249637801878362906294313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1666183735837817208392417 1249637801878362906294313)
  ·
    refine ⟨937228351408772179720735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1249637801878362906294313 937228351408772179720735)
    ·
      refine ⟨1405842527113158269581103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937228351408772179720735 1405842527113158269581103)
      ·
        refine ⟨2108763790669737404371655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1405842527113158269581103 2108763790669737404371655)
        ·
          refine ⟨3163145686004606106557483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108763790669737404371655 3163145686004606106557483)
          ·
            refine ⟨4744718529006909159836225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163145686004606106557483 4744718529006909159836225)
            ·
              refine ⟨3558538896755181869877169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4744718529006909159836225 3558538896755181869877169)
              ·
                refine ⟨2668904172566386402407877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558538896755181869877169 2668904172566386402407877)
                ·
                  refine ⟨500419532356197450451477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2668904172566386402407877 500419532356197450451477)
                  ·
                    refine ⟨23457165579196755489913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 500419532356197450451477 23457165579196755489913)
                    ·
                      rfl

theorem cell22_68524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_68524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68524 prefixEnd_68524 := by exact prefixLift 68524
  have htrace : WordTrace (prefixWord ++ tailWord_68524) baseStart_68524 baseEnd_68524 := by
    simpa [prefixWord, tailWord_68524, baseEnd_68524] using wordTrace_append hprefix tailTrace_68524
  have hstable : (prefixWord ++ tailWord_68524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68524).length < 2 ^ (prefixWord ++ tailWord_68524).sum := by decide
  have hdescent : baseEnd_68524 < baseStart_68524 := by decide
  rcases family_descends (prefixWord ++ tailWord_68524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68532 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_68532 : Nat := 118140960795 + 68532 * 2 ^ 59
def prefixEnd_68532 : Nat := 4983230072969 + 3 ^ 40 * 68532 * 2
def baseEnd_68532 : Nat := 23459904142687401289889

theorem tailTrace_68532 : CollatzResearch.WordTrace tailWord_68532 prefixEnd_68532 23459904142687401289889 := by
  unfold tailWord_68532
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249783693863871589439925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1666378258485162119253233 1249783693863871589439925)
  ·
    refine ⟨117167221299737961509993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1249783693863871589439925 117167221299737961509993)
    ·
      refine ⟨87875415974803471132495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117167221299737961509993 87875415974803471132495)
      ·
        refine ⟨131813123962205206698743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87875415974803471132495 131813123962205206698743)
        ·
          refine ⟨197719685943307810048115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131813123962205206698743 197719685943307810048115)
          ·
            refine ⟨296579528914961715072173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197719685943307810048115 296579528914961715072173)
            ·
              refine ⟨111217323343110643152065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296579528914961715072173 111217323343110643152065)
              ·
                refine ⟨83412992507332982364049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111217323343110643152065 83412992507332982364049)
                ·
                  refine ⟨62559744380499736773037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83412992507332982364049 62559744380499736773037)
                  ·
                    refine ⟨23459904142687401289889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62559744380499736773037 23459904142687401289889)
                    ·
                      rfl

theorem cell22_68532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_68532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68532 prefixEnd_68532 := by exact prefixLift 68532
  have htrace : WordTrace (prefixWord ++ tailWord_68532) baseStart_68532 baseEnd_68532 := by
    simpa [prefixWord, tailWord_68532, baseEnd_68532] using wordTrace_append hprefix tailTrace_68532
  have hstable : (prefixWord ++ tailWord_68532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68532).length < 2 ^ (prefixWord ++ tailWord_68532).sum := by decide
  have hdescent : baseEnd_68532 < baseStart_68532 := by decide
  rcases family_descends (prefixWord ++ tailWord_68532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68594 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_68594 : Nat := 118140960795 + 68594 * 2 ^ 59
def prefixEnd_68594 : Nat := 4983230072969 + 3 ^ 40 * 68594 * 2
def baseEnd_68594 : Nat := 23481128009739906239699

theorem tailTrace_68594 : CollatzResearch.WordTrace tailWord_68594 prefixEnd_68594 23481128009739906239699 := by
  unfold tailWord_68594
  simp only [CollatzResearch.WordTrace]
  refine ⟨625457178375781941909209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1667885809002085178424557 625457178375781941909209)
  ·
    refine ⟨469092883781836456431907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 625457178375781941909209 469092883781836456431907)
    ·
      refine ⟨703639325672754684647861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469092883781836456431907 703639325672754684647861)
      ·
        refine ⟨65966186781820751685737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 703639325672754684647861 65966186781820751685737)
        ·
          refine ⟨49474640086365563764303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65966186781820751685737 49474640086365563764303)
          ·
            refine ⟨74211960129548345646455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49474640086365563764303 74211960129548345646455)
            ·
              refine ⟨111317940194322518469683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74211960129548345646455 111317940194322518469683)
              ·
                refine ⟨166976910291483777704525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111317940194322518469683 166976910291483777704525)
                ·
                  refine ⟨62616341359306416639197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166976910291483777704525 62616341359306416639197)
                  ·
                    refine ⟨23481128009739906239699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62616341359306416639197 23481128009739906239699)
                    ·
                      rfl

theorem cell22_68594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_68594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68594 prefixEnd_68594 := by exact prefixLift 68594
  have htrace : WordTrace (prefixWord ++ tailWord_68594) baseStart_68594 baseEnd_68594 := by
    simpa [prefixWord, tailWord_68594, baseEnd_68594] using wordTrace_append hprefix tailTrace_68594
  have hstable : (prefixWord ++ tailWord_68594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68594).length < 2 ^ (prefixWord ++ tailWord_68594).sum := by decide
  have hdescent : baseEnd_68594 < baseStart_68594 := by decide
  rcases family_descends (prefixWord ++ tailWord_68594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68620 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_68620 : Nat := 118140960795 + 68620 * 2 ^ 59
def prefixEnd_68620 : Nat := 4983230072969 + 3 ^ 40 * 68620 * 2
def baseEnd_68620 : Nat := 23490028341084505089619

theorem tailTrace_68620 : CollatzResearch.WordTrace tailWord_68620 prefixEnd_68620 23490028341084505089619 := by
  unfold tailWord_68620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251388505704467104041657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1668518007605956138722209 1251388505704467104041657)
  ·
    refine ⟨938541379278350328031243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1251388505704467104041657 938541379278350328031243)
    ·
      refine ⟨1407812068917525492046865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938541379278350328031243 1407812068917525492046865)
      ·
        refine ⟨1055859051688144119035149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1407812068917525492046865 1055859051688144119035149)
        ·
          refine ⟨395947144383054044638181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1055859051688144119035149 395947144383054044638181)
          ·
            refine ⟨74240089571822633369659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 395947144383054044638181 74240089571822633369659)
            ·
              refine ⟨111360134357733950054489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74240089571822633369659 111360134357733950054489)
              ·
                refine ⟨83520100768300462540867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111360134357733950054489 83520100768300462540867)
                ·
                  refine ⟨125280151152450693811301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83520100768300462540867 125280151152450693811301)
                  ·
                    refine ⟨23490028341084505089619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125280151152450693811301 23490028341084505089619)
                    ·
                      rfl

theorem cell22_68620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_68620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68620 prefixEnd_68620 := by exact prefixLift 68620
  have htrace : WordTrace (prefixWord ++ tailWord_68620) baseStart_68620 baseEnd_68620 := by
    simpa [prefixWord, tailWord_68620, baseEnd_68620] using wordTrace_append hprefix tailTrace_68620
  have hstable : (prefixWord ++ tailWord_68620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68620).length < 2 ^ (prefixWord ++ tailWord_68620).sum := by decide
  have hdescent : baseEnd_68620 < baseStart_68620 := by decide
  rcases family_descends (prefixWord ++ tailWord_68620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68637 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_68637 : Nat := 118140960795 + 68637 * 2 ^ 59
def prefixEnd_68637 : Nat := 4983230072969 + 3 ^ 40 * 68637 * 2
def baseEnd_68637 : Nat := 23495847788502127414567

theorem tailTrace_68637 : CollatzResearch.WordTrace tailWord_68637 prefixEnd_68637 23495847788502127414567 := by
  unfold tailWord_68637
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503397052347346111452165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1668931368231564074301443 2503397052347346111452165)
  ·
    refine ⟨469386947315127395897281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2503397052347346111452165 469386947315127395897281)
    ·
      refine ⟨352040210486345546922961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 469386947315127395897281 352040210486345546922961)
      ·
        refine ⟨264030157864759160192221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352040210486345546922961 264030157864759160192221)
        ·
          refine ⟨99011309199284685072083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264030157864759160192221 99011309199284685072083)
          ·
            refine ⟨148516963798927027608125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99011309199284685072083 148516963798927027608125)
            ·
              refine ⟨55693861424597635353047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148516963798927027608125 55693861424597635353047)
              ·
                refine ⟨83540792136896453029571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55693861424597635353047 83540792136896453029571)
                ·
                  refine ⟨125311188205344679544357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83540792136896453029571 125311188205344679544357)
                  ·
                    refine ⟨23495847788502127414567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125311188205344679544357 23495847788502127414567)
                    ·
                      rfl

theorem cell22_68637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_68637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68637 prefixEnd_68637 := by exact prefixLift 68637
  have htrace : WordTrace (prefixWord ++ tailWord_68637) baseStart_68637 baseEnd_68637 := by
    simpa [prefixWord, tailWord_68637, baseEnd_68637] using wordTrace_append hprefix tailTrace_68637
  have hstable : (prefixWord ++ tailWord_68637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68637).length < 2 ^ (prefixWord ++ tailWord_68637).sum := by decide
  have hdescent : baseEnd_68637 < baseStart_68637 := by decide
  rcases family_descends (prefixWord ++ tailWord_68637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68661 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_68661 : Nat := 118140960795 + 68661 * 2 ^ 59
def prefixEnd_68661 : Nat := 4983230072969 + 3 ^ 40 * 68661 * 2
def baseEnd_68661 : Nat := 23504063478974064814493

theorem tailTrace_68661 : CollatzResearch.WordTrace tailWord_68661 prefixEnd_68661 23504063478974064814493 := by
  unfold tailWord_68661
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504272404260398210325837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1669514936173598806883891 2504272404260398210325837)
  ·
    refine ⟨939102151597649328872189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2504272404260398210325837 939102151597649328872189)
    ·
      refine ⟨352163306849118498327071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 939102151597649328872189 352163306849118498327071)
      ·
        refine ⟨528244960273677747490607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352163306849118498327071 528244960273677747490607)
        ·
          refine ⟨792367440410516621235911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528244960273677747490607 792367440410516621235911)
          ·
            refine ⟨1188551160615774931853867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792367440410516621235911 1188551160615774931853867)
            ·
              refine ⟨1782826740923662397780801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188551160615774931853867 1782826740923662397780801)
              ·
                refine ⟨1337120055692746798335601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782826740923662397780801 1337120055692746798335601)
                ·
                  refine ⟨1002840041769560098751701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337120055692746798335601 1002840041769560098751701)
                  ·
                    refine ⟨23504063478974064814493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1002840041769560098751701 23504063478974064814493)
                    ·
                      rfl

theorem cell22_68661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_68661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68661 prefixEnd_68661 := by exact prefixLift 68661
  have htrace : WordTrace (prefixWord ++ tailWord_68661) baseStart_68661 baseEnd_68661 := by
    simpa [prefixWord, tailWord_68661, baseEnd_68661] using wordTrace_append hprefix tailTrace_68661
  have hstable : (prefixWord ++ tailWord_68661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68661).length < 2 ^ (prefixWord ++ tailWord_68661).sum := by decide
  have hdescent : baseEnd_68661 < baseStart_68661 := by decide
  rcases family_descends (prefixWord ++ tailWord_68661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68701 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_68701 : Nat := 118140960795 + 68701 * 2 ^ 59
def prefixEnd_68701 : Nat := 4983230072969 + 3 ^ 40 * 68701 * 2
def baseEnd_68701 : Nat := 23517756296427293814371

theorem tailTrace_68701 : CollatzResearch.WordTrace tailWord_68701 prefixEnd_68701 23517756296427293814371 := by
  unfold tailWord_68701
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505731324115485041781957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1670487549410323361187971 2505731324115485041781957)
  ·
    refine ⟨469824623271653445334117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2505731324115485041781957 469824623271653445334117)
    ·
      refine ⟨88092116863435021000147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 469824623271653445334117 88092116863435021000147)
      ·
        refine ⟨132138175295152531500221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88092116863435021000147 132138175295152531500221)
        ·
          refine ⟨49551815735682199312583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132138175295152531500221 49551815735682199312583)
          ·
            refine ⟨74327723603523298968875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49551815735682199312583 74327723603523298968875)
            ·
              refine ⟨111491585405284948453313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74327723603523298968875 111491585405284948453313)
              ·
                refine ⟨83618689053963711339985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111491585405284948453313 83618689053963711339985)
                ·
                  refine ⟨62714016790472783504989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83618689053963711339985 62714016790472783504989)
                  ·
                    refine ⟨23517756296427293814371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62714016790472783504989 23517756296427293814371)
                    ·
                      rfl

theorem cell22_68701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_68701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68701 prefixEnd_68701 := by exact prefixLift 68701
  have htrace : WordTrace (prefixWord ++ tailWord_68701) baseStart_68701 baseEnd_68701 := by
    simpa [prefixWord, tailWord_68701, baseEnd_68701] using wordTrace_append hprefix tailTrace_68701
  have hstable : (prefixWord ++ tailWord_68701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68701).length < 2 ^ (prefixWord ++ tailWord_68701).sum := by decide
  have hdescent : baseEnd_68701 < baseStart_68701 := by decide
  rcases family_descends (prefixWord ++ tailWord_68701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68721 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_68721 : Nat := 118140960795 + 68721 * 2 ^ 59
def prefixEnd_68721 : Nat := 4983230072969 + 3 ^ 40 * 68721 * 2
def baseEnd_68721 : Nat := 23524602705153908314309

theorem tailTrace_68721 : CollatzResearch.WordTrace tailWord_68721 prefixEnd_68721 23524602705153908314309 := by
  unfold tailWord_68721
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506460784043028457510017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1670973856028685638340011 2506460784043028457510017)
  ·
    refine ⟨1879845588032271343132513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2506460784043028457510017 1879845588032271343132513)
    ·
      refine ⟨1409884191024203507349385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1879845588032271343132513 1409884191024203507349385)
      ·
        refine ⟨1057413143268152630512039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1409884191024203507349385 1057413143268152630512039)
        ·
          refine ⟨1586119714902228945768059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057413143268152630512039 1586119714902228945768059)
          ·
            refine ⟨2379179572353343418652089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586119714902228945768059 2379179572353343418652089)
            ·
              refine ⟨1784384679265007563989067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379179572353343418652089 1784384679265007563989067)
              ·
                refine ⟨2676577018897511345983601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784384679265007563989067 2676577018897511345983601)
                ·
                  refine ⟨2007432764173133509487701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676577018897511345983601 2007432764173133509487701)
                  ·
                    refine ⟨23524602705153908314309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2007432764173133509487701 23524602705153908314309)
                    ·
                      rfl

theorem cell22_68721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_68721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68721 prefixEnd_68721 := by exact prefixLift 68721
  have htrace : WordTrace (prefixWord ++ tailWord_68721) baseStart_68721 baseEnd_68721 := by
    simpa [prefixWord, tailWord_68721, baseEnd_68721] using wordTrace_append hprefix tailTrace_68721
  have hstable : (prefixWord ++ tailWord_68721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68721).length < 2 ^ (prefixWord ++ tailWord_68721).sum := by decide
  have hdescent : baseEnd_68721 < baseStart_68721 := by decide
  rcases family_descends (prefixWord ++ tailWord_68721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68847 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 3, 3]
def baseStart_68847 : Nat := 118140960795 + 68847 * 2 ^ 59
def prefixEnd_68847 : Nat := 4983230072969 + 3 ^ 40 * 68847 * 2
def baseEnd_68847 : Nat := 23567735080131579663923

theorem tailTrace_68847 : CollatzResearch.WordTrace tailWord_68847 prefixEnd_68847 23567735080131579663923 := by
  unfold tailWord_68847
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511056381586551976596795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1674037587724367984397863 2511056381586551976596795)
  ·
    refine ⟨3766584572379827964895193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2511056381586551976596795 3766584572379827964895193)
    ·
      refine ⟨2824938429284870973671395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3766584572379827964895193 2824938429284870973671395)
      ·
        refine ⟨4237407643927306460507093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824938429284870973671395 4237407643927306460507093)
        ·
          refine ⟨99314241654546245168135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4237407643927306460507093 99314241654546245168135)
          ·
            refine ⟨148971362481819367752203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99314241654546245168135 148971362481819367752203)
            ·
              refine ⟨223457043722729051628305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148971362481819367752203 223457043722729051628305)
              ·
                refine ⟨167592782792046788721229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223457043722729051628305 167592782792046788721229)
                ·
                  refine ⟨62847293547017545770461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167592782792046788721229 62847293547017545770461)
                  ·
                    refine ⟨23567735080131579663923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62847293547017545770461 23567735080131579663923)
                    ·
                      rfl

theorem cell22_68847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_68847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68847 prefixEnd_68847 := by exact prefixLift 68847
  have htrace : WordTrace (prefixWord ++ tailWord_68847) baseStart_68847 baseEnd_68847 := by
    simpa [prefixWord, tailWord_68847, baseEnd_68847] using wordTrace_append hprefix tailTrace_68847
  have hstable : (prefixWord ++ tailWord_68847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68847).length < 2 ^ (prefixWord ++ tailWord_68847).sum := by decide
  have hdescent : baseEnd_68847 < baseStart_68847 := by decide
  rcases family_descends (prefixWord ++ tailWord_68847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68858 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_68858 : Nat := 118140960795 + 68858 * 2 ^ 59
def prefixEnd_68858 : Nat := 4983230072969 + 3 ^ 40 * 68858 * 2
def baseEnd_68858 : Nat := 23571500604931217638889

theorem tailTrace_68858 : CollatzResearch.WordTrace tailWord_68858 prefixEnd_68858 23571500604931217638889 := by
  unfold tailWord_68858
  simp only [CollatzResearch.WordTrace]
  refine ⟨627864396136675213811807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1674305056364467236831485 627864396136675213811807)
  ·
    refine ⟨941796594205012820717711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627864396136675213811807 941796594205012820717711)
    ·
      refine ⟨1412694891307519231076567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941796594205012820717711 1412694891307519231076567)
      ·
        refine ⟨2119042336961278846614851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412694891307519231076567 2119042336961278846614851)
        ·
          refine ⟨3178563505441918269922277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119042336961278846614851 3178563505441918269922277)
          ·
            refine ⟨595980657270359675610427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3178563505441918269922277 595980657270359675610427)
            ·
              refine ⟨893970985905539513415641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595980657270359675610427 893970985905539513415641)
              ·
                refine ⟨670478239429154635061731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893970985905539513415641 670478239429154635061731)
                ·
                  refine ⟨1005717359143731952592597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670478239429154635061731 1005717359143731952592597)
                  ·
                    refine ⟨23571500604931217638889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1005717359143731952592597 23571500604931217638889)
                    ·
                      rfl

theorem cell22_68858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_68858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68858 prefixEnd_68858 := by exact prefixLift 68858
  have htrace : WordTrace (prefixWord ++ tailWord_68858) baseStart_68858 baseEnd_68858 := by
    simpa [prefixWord, tailWord_68858, baseEnd_68858] using wordTrace_append hprefix tailTrace_68858
  have hstable : (prefixWord ++ tailWord_68858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68858).length < 2 ^ (prefixWord ++ tailWord_68858).sum := by decide
  have hdescent : baseEnd_68858 < baseStart_68858 := by decide
  rcases family_descends (prefixWord ++ tailWord_68858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68935 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 4, 4]
def baseStart_68935 : Nat := 118140960795 + 68935 * 2 ^ 59
def prefixEnd_68935 : Nat := 4983230072969 + 3 ^ 40 * 68935 * 2
def baseEnd_68935 : Nat := 23597859278528683463653

theorem tailTrace_68935 : CollatzResearch.WordTrace tailWord_68935 prefixEnd_68935 23597859278528683463653 := by
  unfold tailWord_68935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514266005267743005800259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1676177336845162003866839 2514266005267743005800259)
  ·
    refine ⟨3771399007901614508700389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2514266005267743005800259 3771399007901614508700389)
    ·
      refine ⟨707137313981552720381323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3771399007901614508700389 707137313981552720381323)
      ·
        refine ⟨1060705970972329080571985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707137313981552720381323 1060705970972329080571985)
        ·
          refine ⟨795529478229246810428989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1060705970972329080571985 795529478229246810428989)
          ·
            refine ⟨298323554335967553910871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 795529478229246810428989 298323554335967553910871)
            ·
              refine ⟨447485331503951330866307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298323554335967553910871 447485331503951330866307)
              ·
                refine ⟨671227997255926996299461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447485331503951330866307 671227997255926996299461)
                ·
                  refine ⟨125855249485486311806149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671227997255926996299461 125855249485486311806149)
                  ·
                    refine ⟨23597859278528683463653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125855249485486311806149 23597859278528683463653)
                    ·
                      rfl

theorem cell22_68935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_68935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68935 prefixEnd_68935 := by exact prefixLift 68935
  have htrace : WordTrace (prefixWord ++ tailWord_68935) baseStart_68935 baseEnd_68935 := by
    simpa [prefixWord, tailWord_68935, baseEnd_68935] using wordTrace_append hprefix tailTrace_68935
  have hstable : (prefixWord ++ tailWord_68935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68935).length < 2 ^ (prefixWord ++ tailWord_68935).sum := by decide
  have hdescent : baseEnd_68935 < baseStart_68935 := by decide
  rcases family_descends (prefixWord ++ tailWord_68935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68954 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_68954 : Nat := 118140960795 + 68954 * 2 ^ 59
def prefixEnd_68954 : Nat := 4983230072969 + 3 ^ 40 * 68954 * 2
def baseEnd_68954 : Nat := 23604363366818967238595

theorem tailTrace_68954 : CollatzResearch.WordTrace tailWord_68954 prefixEnd_68954 23604363366818967238595 := by
  unfold tailWord_68954
  simp only [CollatzResearch.WordTrace]
  refine ⟨628739748049727312685479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1676639328132606167161277 628739748049727312685479)
  ·
    refine ⟨943109622074590969028219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 628739748049727312685479 943109622074590969028219)
    ·
      refine ⟨1414664433111886453542329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943109622074590969028219 1414664433111886453542329)
      ·
        refine ⟨1060998324833914840156747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1414664433111886453542329 1060998324833914840156747)
        ·
          refine ⟨1591497487250872260235121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060998324833914840156747 1591497487250872260235121)
          ·
            refine ⟨1193623115438154195176341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1591497487250872260235121 1193623115438154195176341)
            ·
              refine ⟨55951083536163477898891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1193623115438154195176341 55951083536163477898891)
              ·
                refine ⟨83926625304245216848337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55951083536163477898891 83926625304245216848337)
                ·
                  refine ⟨62944968978183912636253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83926625304245216848337 62944968978183912636253)
                  ·
                    refine ⟨23604363366818967238595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62944968978183912636253 23604363366818967238595)
                    ·
                      rfl

theorem cell22_68954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_68954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68954 prefixEnd_68954 := by exact prefixLift 68954
  have htrace : WordTrace (prefixWord ++ tailWord_68954) baseStart_68954 baseEnd_68954 := by
    simpa [prefixWord, tailWord_68954, baseEnd_68954] using wordTrace_append hprefix tailTrace_68954
  have hstable : (prefixWord ++ tailWord_68954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68954).length < 2 ^ (prefixWord ++ tailWord_68954).sum := by decide
  have hdescent : baseEnd_68954 < baseStart_68954 := by decide
  rcases family_descends (prefixWord ++ tailWord_68954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68990 : List Nat := [4, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_68990 : Nat := 118140960795 + 68990 * 2 ^ 59
def prefixEnd_68990 : Nat := 4983230072969 + 3 ^ 40 * 68990 * 2
def baseEnd_68990 : Nat := 7872228967508957779495

theorem tailTrace_68990 : CollatzResearch.WordTrace tailWord_68990 prefixEnd_68990 7872228967508957779495 := by
  unfold tailWord_68990
  simp only [CollatzResearch.WordTrace]
  refine ⟨314534002508560924881553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1677514680045658266034949 314534002508560924881553)
  ·
    refine ⟨235900501881420693661165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 314534002508560924881553 235900501881420693661165)
    ·
      refine ⟨88462688205532760122937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235900501881420693661165 88462688205532760122937)
      ·
        refine ⟨66347016154149570092203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88462688205532760122937 66347016154149570092203)
        ·
          refine ⟨99520524231224355138305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66347016154149570092203 99520524231224355138305)
          ·
            refine ⟨74640393173418266353729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99520524231224355138305 74640393173418266353729)
            ·
              refine ⟨55980294880063699765297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74640393173418266353729 55980294880063699765297)
              ·
                refine ⟨41985221160047774823973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55980294880063699765297 41985221160047774823973)
                ·
                  refine ⟨7872228967508957779495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41985221160047774823973 7872228967508957779495)
                  ·
                    rfl

theorem cell22_68990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_68990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_68990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_68990 prefixEnd_68990 := by exact prefixLift 68990
  have htrace : WordTrace (prefixWord ++ tailWord_68990) baseStart_68990 baseEnd_68990 := by
    simpa [prefixWord, tailWord_68990, baseEnd_68990] using wordTrace_append hprefix tailTrace_68990
  have hstable : (prefixWord ++ tailWord_68990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68990).length < 2 ^ (prefixWord ++ tailWord_68990).sum := by decide
  have hdescent : baseEnd_68990 < baseStart_68990 := by decide
  rcases family_descends (prefixWord ++ tailWord_68990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69055 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 3, 5]
def baseStart_69055 : Nat := 118140960795 + 69055 * 2 ^ 59
def prefixEnd_69055 : Nat := 4983230072969 + 3 ^ 40 * 69055 * 2
def baseEnd_69055 : Nat := 23638937730888370463285

theorem tailTrace_69055 : CollatzResearch.WordTrace tailWord_69055 prefixEnd_69055 23638937730888370463285 := by
  unfold tailWord_69055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518642764833003500168619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1679095176555335666779079 2518642764833003500168619)
  ·
    refine ⟨3777964147249505250252929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518642764833003500168619 3777964147249505250252929)
    ·
      refine ⟨2833473110437128937689697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3777964147249505250252929 2833473110437128937689697)
      ·
        refine ⟨2125104832827846703267273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2833473110437128937689697 2125104832827846703267273)
        ·
          refine ⟨1593828624620885027450455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125104832827846703267273 1593828624620885027450455)
          ·
            refine ⟨2390742936931327541175683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593828624620885027450455 2390742936931327541175683)
            ·
              refine ⟨3586114405396991311763525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2390742936931327541175683 3586114405396991311763525)
              ·
                refine ⟨672396451011935870955661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3586114405396991311763525 672396451011935870955661)
                ·
                  refine ⟨252148669129475951608373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 672396451011935870955661 252148669129475951608373)
                  ·
                    refine ⟨23638937730888370463285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 252148669129475951608373 23638937730888370463285)
                    ·
                      rfl

theorem cell22_69055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_69055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69055 prefixEnd_69055 := by exact prefixLift 69055
  have htrace : WordTrace (prefixWord ++ tailWord_69055) baseStart_69055 baseEnd_69055 := by
    simpa [prefixWord, tailWord_69055, baseEnd_69055] using wordTrace_append hprefix tailTrace_69055
  have hstable : (prefixWord ++ tailWord_69055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69055).length < 2 ^ (prefixWord ++ tailWord_69055).sum := by decide
  have hdescent : baseEnd_69055 < baseStart_69055 := by decide
  rcases family_descends (prefixWord ++ tailWord_69055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69076 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_69076 : Nat := 118140960795 + 69076 * 2 ^ 59
def prefixEnd_69076 : Nat := 4983230072969 + 3 ^ 40 * 69076 * 2
def baseEnd_69076 : Nat := 23646126460051315688221

theorem tailTrace_69076 : CollatzResearch.WordTrace tailWord_69076 prefixEnd_69076 23646126460051315688221 := by
  unfold tailWord_69076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259704348878462043341541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1679605798504616057788721 1259704348878462043341541)
  ·
    refine ⟨236194565414711633126539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1259704348878462043341541 236194565414711633126539)
    ·
      refine ⟨354291848122067449689809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236194565414711633126539 354291848122067449689809)
      ·
        refine ⟨265718886091550587267357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354291848122067449689809 265718886091550587267357)
        ·
          refine ⟨99644582284331470225259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265718886091550587267357 99644582284331470225259)
          ·
            refine ⟨149466873426497205337889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99644582284331470225259 149466873426497205337889)
            ·
              refine ⟨112100155069872904003417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149466873426497205337889 112100155069872904003417)
              ·
                refine ⟨84075116302404678002563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112100155069872904003417 84075116302404678002563)
                ·
                  refine ⟨126112674453607017003845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84075116302404678002563 126112674453607017003845)
                  ·
                    refine ⟨23646126460051315688221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126112674453607017003845 23646126460051315688221)
                    ·
                      rfl

theorem cell22_69076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_69076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69076 prefixEnd_69076 := by exact prefixLift 69076
  have htrace : WordTrace (prefixWord ++ tailWord_69076) baseStart_69076 baseEnd_69076 := by
    simpa [prefixWord, tailWord_69076, baseEnd_69076] using wordTrace_append hprefix tailTrace_69076
  have hstable : (prefixWord ++ tailWord_69076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69076).length < 2 ^ (prefixWord ++ tailWord_69076).sum := by decide
  have hdescent : baseEnd_69076 < baseStart_69076 := by decide
  rcases family_descends (prefixWord ++ tailWord_69076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69087 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 2, 4]
def baseStart_69087 : Nat := 118140960795 + 69087 * 2 ^ 59
def prefixEnd_69087 : Nat := 4983230072969 + 3 ^ 40 * 69087 * 2
def baseEnd_69087 : Nat := 23649891984850953663187

theorem tailTrace_69087 : CollatzResearch.WordTrace tailWord_69087 prefixEnd_69087 23649891984850953663187 := by
  unfold tailWord_69087
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519809900717072965333515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1679873267144715310222343 2519809900717072965333515)
  ·
    refine ⟨3779714851075609448000273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2519809900717072965333515 3779714851075609448000273)
    ·
      refine ⟨2834786138306707086000205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3779714851075609448000273 2834786138306707086000205)
      ·
        refine ⟨1063044801865015157250077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2834786138306707086000205 1063044801865015157250077)
        ·
          refine ⟨398641800699380683968779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1063044801865015157250077 398641800699380683968779)
          ·
            refine ⟨597962701049071025953169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398641800699380683968779 597962701049071025953169)
            ·
              refine ⟨448472025786803269464877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597962701049071025953169 448472025786803269464877)
              ·
                refine ⟨168177009670051226049329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448472025786803269464877 168177009670051226049329)
                ·
                  refine ⟨126132757252538419536997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168177009670051226049329 126132757252538419536997)
                  ·
                    refine ⟨23649891984850953663187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126132757252538419536997 23649891984850953663187)
                    ·
                      rfl

theorem cell22_69087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_69087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69087 prefixEnd_69087 := by exact prefixLift 69087
  have htrace : WordTrace (prefixWord ++ tailWord_69087) baseStart_69087 baseEnd_69087 := by
    simpa [prefixWord, tailWord_69087, baseEnd_69087] using wordTrace_append hprefix tailTrace_69087
  have hstable : (prefixWord ++ tailWord_69087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69087).length < 2 ^ (prefixWord ++ tailWord_69087).sum := by decide
  have hdescent : baseEnd_69087 < baseStart_69087 := by decide
  rcases family_descends (prefixWord ++ tailWord_69087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69091 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 4]
def baseStart_69091 : Nat := 118140960795 + 69091 * 2 ^ 59
def prefixEnd_69091 : Nat := 4983230072969 + 3 ^ 40 * 69091 * 2
def baseEnd_69091 : Nat := 7883753755532092187725

theorem tailTrace_69091 : CollatzResearch.WordTrace tailWord_69091 prefixEnd_69091 7883753755532092187725 := by
  unfold tailWord_69091
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519955792702581648479127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1679970528468387765652751 2519955792702581648479127)
  ·
    refine ⟨3779933689053872472718691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2519955792702581648479127 3779933689053872472718691)
    ·
      refine ⟨5669900533580808709078037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779933689053872472718691 5669900533580808709078037)
      ·
        refine ⟨265776587511600408238033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5669900533580808709078037 265776587511600408238033)
        ·
          refine ⟨199332440633700306178525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265776587511600408238033 199332440633700306178525)
          ·
            refine ⟨74749665237637614816947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199332440633700306178525 74749665237637614816947)
            ·
              refine ⟨112124497856456422225421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74749665237637614816947 112124497856456422225421)
              ·
                refine ⟨42046686696171158334533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112124497856456422225421 42046686696171158334533)
                ·
                  refine ⟨7883753755532092187725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42046686696171158334533 7883753755532092187725)
                  ·
                    rfl

theorem cell22_69091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 4].length) (baseStart_69091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69091 prefixEnd_69091 := by exact prefixLift 69091
  have htrace : WordTrace (prefixWord ++ tailWord_69091) baseStart_69091 baseEnd_69091 := by
    simpa [prefixWord, tailWord_69091, baseEnd_69091] using wordTrace_append hprefix tailTrace_69091
  have hstable : (prefixWord ++ tailWord_69091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69091).length < 2 ^ (prefixWord ++ tailWord_69091).sum := by decide
  have hdescent : baseEnd_69091 < baseStart_69091 := by decide
  rcases family_descends (prefixWord ++ tailWord_69091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69115 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 8]
def baseStart_69115 : Nat := 118140960795 + 69115 * 2 ^ 59
def prefixEnd_69115 : Nat := 4983230072969 + 3 ^ 40 * 69115 * 2
def baseEnd_69115 : Nat := 23659476957068213963101

theorem tailTrace_69115 : CollatzResearch.WordTrace tailWord_69115 prefixEnd_69115 23659476957068213963101 := by
  unfold tailWord_69115
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520831144615633747352799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1680554096410422498235199 2520831144615633747352799)
  ·
    refine ⟨3781246716923450621029199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2520831144615633747352799 3781246716923450621029199)
    ·
      refine ⟨5671870075385175931543799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781246716923450621029199 5671870075385175931543799)
      ·
        refine ⟨8507805113077763897315699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5671870075385175931543799 8507805113077763897315699)
        ·
          refine ⟨12761707669616645845973549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507805113077763897315699 12761707669616645845973549)
          ·
            refine ⟨4785640376106242192240081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12761707669616645845973549 4785640376106242192240081)
            ·
              refine ⟨3589230282079681644180061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785640376106242192240081 3589230282079681644180061)
              ·
                refine ⟨1345961355779880616567523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3589230282079681644180061 1345961355779880616567523)
                ·
                  refine ⟨2018942033669820924851285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345961355779880616567523 2018942033669820924851285)
                  ·
                    refine ⟨23659476957068213963101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2018942033669820924851285 23659476957068213963101)
                    ·
                      rfl

theorem cell22_69115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_69115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69115 prefixEnd_69115 := by exact prefixLift 69115
  have htrace : WordTrace (prefixWord ++ tailWord_69115) baseStart_69115 baseEnd_69115 := by
    simpa [prefixWord, tailWord_69115, baseEnd_69115] using wordTrace_append hprefix tailTrace_69115
  have hstable : (prefixWord ++ tailWord_69115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69115).length < 2 ^ (prefixWord ++ tailWord_69115).sum := by decide
  have hdescent : baseEnd_69115 < baseStart_69115 := by decide
  rcases family_descends (prefixWord ++ tailWord_69115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69194 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_69194 : Nat := 118140960795 + 69194 * 2 ^ 59
def prefixEnd_69194 : Nat := 4983230072969 + 3 ^ 40 * 69194 * 2
def baseEnd_69194 : Nat := 23686520271538341237859

theorem tailTrace_69194 : CollatzResearch.WordTrace tailWord_69194 prefixEnd_69194 23686520271538341237859 := by
  unfold tailWord_69194
  simp only [CollatzResearch.WordTrace]
  refine ⟨630928127832357559869659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1682475007552953492985757 630928127832357559869659)
  ·
    refine ⟨946392191748536339804489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630928127832357559869659 946392191748536339804489)
    ·
      refine ⟨709794143811402254853367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 946392191748536339804489 709794143811402254853367)
      ·
        refine ⟨1064691215717103382280051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709794143811402254853367 1064691215717103382280051)
        ·
          refine ⟨1597036823575655073420077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064691215717103382280051 1597036823575655073420077)
          ·
            refine ⟨598888808840870652532529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1597036823575655073420077 598888808840870652532529)
            ·
              refine ⟨449166606630652989399397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598888808840870652532529 449166606630652989399397)
              ·
                refine ⟨84218738743247435512387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 449166606630652989399397 84218738743247435512387)
                ·
                  refine ⟨126328108114871153268581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84218738743247435512387 126328108114871153268581)
                  ·
                    refine ⟨23686520271538341237859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126328108114871153268581 23686520271538341237859)
                    ·
                      rfl

theorem cell22_69194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_69194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69194 prefixEnd_69194 := by exact prefixLift 69194
  have htrace : WordTrace (prefixWord ++ tailWord_69194) baseStart_69194 baseEnd_69194 := by
    simpa [prefixWord, tailWord_69194, baseEnd_69194] using wordTrace_append hprefix tailTrace_69194
  have hstable : (prefixWord ++ tailWord_69194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69194).length < 2 ^ (prefixWord ++ tailWord_69194).sum := by decide
  have hdescent : baseEnd_69194 < baseStart_69194 := by decide
  rcases family_descends (prefixWord ++ tailWord_69194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69226 : List Nat := [3, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_69226 : Nat := 118140960795 + 69226 * 2 ^ 59
def prefixEnd_69226 : Nat := 4983230072969 + 3 ^ 40 * 69226 * 2
def baseEnd_69226 : Nat := 7899158175166974812587

theorem tailTrace_69226 : CollatzResearch.WordTrace tailWord_69226 prefixEnd_69226 7899158175166974812587 := by
  unfold tailWord_69226
  simp only [CollatzResearch.WordTrace]
  refine ⟨631219911803374926160883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1683253098142333136429021 631219911803374926160883)
  ·
    refine ⟨946829867705062389241325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 631219911803374926160883 946829867705062389241325)
    ·
      refine ⟨355061200389398395965497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 946829867705062389241325 355061200389398395965497)
      ·
        refine ⟨266295900292048796974123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355061200389398395965497 266295900292048796974123)
        ·
          refine ⟨399443850438073195461185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266295900292048796974123 399443850438073195461185)
          ·
            refine ⟨299582887828554896595889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399443850438073195461185 299582887828554896595889)
            ·
              refine ⟨224687165871416172446917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299582887828554896595889 224687165871416172446917)
              ·
                refine ⟨42128843600890532333797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224687165871416172446917 42128843600890532333797)
                ·
                  refine ⟨7899158175166974812587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42128843600890532333797 7899158175166974812587)
                  ·
                    rfl

theorem cell22_69226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_69226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69226 prefixEnd_69226 := by exact prefixLift 69226
  have htrace : WordTrace (prefixWord ++ tailWord_69226) baseStart_69226 baseEnd_69226 := by
    simpa [prefixWord, tailWord_69226, baseEnd_69226] using wordTrace_append hprefix tailTrace_69226
  have hstable : (prefixWord ++ tailWord_69226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69226).length < 2 ^ (prefixWord ++ tailWord_69226).sum := by decide
  have hdescent : baseEnd_69226 < baseStart_69226 := by decide
  rcases family_descends (prefixWord ++ tailWord_69226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69269 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 5, 3]
def baseStart_69269 : Nat := 118140960795 + 69269 * 2 ^ 59
def prefixEnd_69269 : Nat := 4983230072969 + 3 ^ 40 * 69269 * 2
def baseEnd_69269 : Nat := 23712194304263145612629

theorem tailTrace_69269 : CollatzResearch.WordTrace tailWord_69269 prefixEnd_69269 23712194304263145612629 := by
  unfold tailWord_69269
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526447986057718048458861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1684298657371812032305907 2526447986057718048458861)
  ·
    refine ⟨947417994771644268172073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2526447986057718048458861 947417994771644268172073)
    ·
      refine ⟨710563496078733201129055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947417994771644268172073 710563496078733201129055)
      ·
        refine ⟨1065845244118099801693583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710563496078733201129055 1065845244118099801693583)
        ·
          refine ⟨1598767866177149702540375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065845244118099801693583 1598767866177149702540375)
          ·
            refine ⟨2398151799265724553810563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598767866177149702540375 2398151799265724553810563)
            ·
              refine ⟨3597227698898586830715845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398151799265724553810563 3597227698898586830715845)
              ·
                refine ⟨674480193543485030759221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3597227698898586830715845 674480193543485030759221)
                ·
                  refine ⟨63232518144701721633677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 674480193543485030759221 63232518144701721633677)
                  ·
                    refine ⟨23712194304263145612629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63232518144701721633677 23712194304263145612629)
                    ·
                      rfl

theorem cell22_69269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_69269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69269 prefixEnd_69269 := by exact prefixLift 69269
  have htrace : WordTrace (prefixWord ++ tailWord_69269) baseStart_69269 baseEnd_69269 := by
    simpa [prefixWord, tailWord_69269, baseEnd_69269] using wordTrace_append hprefix tailTrace_69269
  have hstable : (prefixWord ++ tailWord_69269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69269).length < 2 ^ (prefixWord ++ tailWord_69269).sum := by decide
  have hdescent : baseEnd_69269 < baseStart_69269 := by decide
  rcases family_descends (prefixWord ++ tailWord_69269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69299 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 5]
def baseStart_69299 : Nat := 118140960795 + 69299 * 2 ^ 59
def prefixEnd_69299 : Nat := 4983230072969 + 3 ^ 40 * 69299 * 2
def baseEnd_69299 : Nat := 7907487972451022454179

theorem tailTrace_69299 : CollatzResearch.WordTrace tailWord_69299 prefixEnd_69299 7907487972451022454179 := by
  unfold tailWord_69299
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527542175949033172050951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1685028117299355448033967 2527542175949033172050951)
  ·
    refine ⟨3791313263923549758076427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2527542175949033172050951 3791313263923549758076427)
    ·
      refine ⟨5686969895885324637114641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3791313263923549758076427 5686969895885324637114641)
      ·
        refine ⟨4265227421913993477835981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5686969895885324637114641 4265227421913993477835981)
        ·
          refine ⟨1599460283217747554188493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4265227421913993477835981 1599460283217747554188493)
          ·
            refine ⟨599797606206655332820685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1599460283217747554188493 599797606206655332820685)
            ·
              refine ⟨224924102327495749807757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599797606206655332820685 224924102327495749807757)
              ·
                refine ⟨84346538372810906177909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224924102327495749807757 84346538372810906177909)
                ·
                  refine ⟨7907487972451022454179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84346538372810906177909 7907487972451022454179)
                  ·
                    rfl

theorem cell22_69299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 5].length) (baseStart_69299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69299 prefixEnd_69299 := by exact prefixLift 69299
  have htrace : WordTrace (prefixWord ++ tailWord_69299) baseStart_69299 baseEnd_69299 := by
    simpa [prefixWord, tailWord_69299, baseEnd_69299] using wordTrace_append hprefix tailTrace_69299
  have hstable : (prefixWord ++ tailWord_69299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69299).length < 2 ^ (prefixWord ++ tailWord_69299).sum := by decide
  have hdescent : baseEnd_69299 < baseStart_69299 := by decide
  rcases family_descends (prefixWord ++ tailWord_69299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69380 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_69380 : Nat := 118140960795 + 69380 * 2 ^ 59
def prefixEnd_69380 : Nat := 4983230072969 + 3 ^ 40 * 69380 * 2
def baseEnd_69380 : Nat := 23750191872695856087289

theorem tailTrace_69380 : CollatzResearch.WordTrace tailWord_69380 prefixEnd_69380 23750191872695856087289 := by
  unfold tailWord_69380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265248244327792002874797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1686997659103722670499729 1265248244327792002874797)
  ·
    refine ⟨474468091622922001078049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1265248244327792002874797 474468091622922001078049)
    ·
      refine ⟨355851068717191500808537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 474468091622922001078049 355851068717191500808537)
      ·
        refine ⟨266888301537893625606403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355851068717191500808537 266888301537893625606403)
        ·
          refine ⟨400332452306840438409605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266888301537893625606403 400332452306840438409605)
          ·
            refine ⟨75062334807532582201801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 400332452306840438409605 75062334807532582201801)
            ·
              refine ⟨56296751105649436651351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75062334807532582201801 56296751105649436651351)
              ·
                refine ⟨84445126658474154977027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56296751105649436651351 84445126658474154977027)
                ·
                  refine ⟨126667689987711232465541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84445126658474154977027 126667689987711232465541)
                  ·
                    refine ⟨23750191872695856087289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126667689987711232465541 23750191872695856087289)
                    ·
                      rfl

theorem cell22_69380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_69380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69380 prefixEnd_69380 := by exact prefixLift 69380
  have htrace : WordTrace (prefixWord ++ tailWord_69380) baseStart_69380 baseEnd_69380 := by
    simpa [prefixWord, tailWord_69380, baseEnd_69380] using wordTrace_append hprefix tailTrace_69380
  have hstable : (prefixWord ++ tailWord_69380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69380).length < 2 ^ (prefixWord ++ tailWord_69380).sum := by decide
  have hdescent : baseEnd_69380 < baseStart_69380 := by decide
  rcases family_descends (prefixWord ++ tailWord_69380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69410 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_69410 : Nat := 118140960795 + 69410 * 2 ^ 59
def prefixEnd_69410 : Nat := 4983230072969 + 3 ^ 40 * 69410 * 2
def baseEnd_69410 : Nat := 23760461485785777837197

theorem tailTrace_69410 : CollatzResearch.WordTrace tailWord_69410 prefixEnd_69410 23760461485785777837197 := by
  unfold tailWord_69410
  simp only [CollatzResearch.WordTrace]
  refine ⟨632897669636724782335421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1687727119031266086227789 632897669636724782335421)
  ·
    refine ⟨237336626113771793375783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 632897669636724782335421 237336626113771793375783)
    ·
      refine ⟨356004939170657690063675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237336626113771793375783 356004939170657690063675)
      ·
        refine ⟨534007408755986535095513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356004939170657690063675 534007408755986535095513)
        ·
          refine ⟨400505556566989901321635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534007408755986535095513 400505556566989901321635)
          ·
            refine ⟨600758334850484851982453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400505556566989901321635 600758334850484851982453)
            ·
              refine ⟨56321093892232954873355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 600758334850484851982453 56321093892232954873355)
              ·
                refine ⟨84481640838349432310033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56321093892232954873355 84481640838349432310033)
                ·
                  refine ⟨63361230628762074232525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84481640838349432310033 63361230628762074232525)
                  ·
                    refine ⟨23760461485785777837197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63361230628762074232525 23760461485785777837197)
                    ·
                      rfl

theorem cell22_69410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_69410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69410 prefixEnd_69410 := by exact prefixLift 69410
  have htrace : WordTrace (prefixWord ++ tailWord_69410) baseStart_69410 baseEnd_69410 := by
    simpa [prefixWord, tailWord_69410, baseEnd_69410] using wordTrace_append hprefix tailTrace_69410
  have hstable : (prefixWord ++ tailWord_69410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69410).length < 2 ^ (prefixWord ++ tailWord_69410).sum := by decide
  have hdescent : baseEnd_69410 < baseStart_69410 := by decide
  rcases family_descends (prefixWord ++ tailWord_69410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69464 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_69464 : Nat := 118140960795 + 69464 * 2 ^ 59
def prefixEnd_69464 : Nat := 4983230072969 + 3 ^ 40 * 69464 * 2
def baseEnd_69464 : Nat := 23778946789347636987031

theorem tailTrace_69464 : CollatzResearch.WordTrace tailWord_69464 prefixEnd_69464 23778946789347636987031 := by
  unfold tailWord_69464
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266780110175633175903723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1689040146900844234538297 1266780110175633175903723)
  ·
    refine ⟨1900170165263449763855585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1266780110175633175903723 1900170165263449763855585)
    ·
      refine ⟨1425127623947587322891689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1900170165263449763855585 1425127623947587322891689)
      ·
        refine ⟨1068845717960690492168767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1425127623947587322891689 1068845717960690492168767)
        ·
          refine ⟨1603268576941035738253151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068845717960690492168767 1603268576941035738253151)
          ·
            refine ⟨2404902865411553607379727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603268576941035738253151 2404902865411553607379727)
            ·
              refine ⟨3607354298117330411069591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404902865411553607379727 3607354298117330411069591)
              ·
                refine ⟨5411031447175995616604387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607354298117330411069591 5411031447175995616604387)
                ·
                  refine ⟨8116547170763993424906581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411031447175995616604387 8116547170763993424906581)
                  ·
                    refine ⟨23778946789347636987031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 8116547170763993424906581 23778946789347636987031)
                    ·
                      rfl

theorem cell22_69464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_69464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69464 prefixEnd_69464 := by exact prefixLift 69464
  have htrace : WordTrace (prefixWord ++ tailWord_69464) baseStart_69464 baseEnd_69464 := by
    simpa [prefixWord, tailWord_69464, baseEnd_69464] using wordTrace_append hprefix tailTrace_69464
  have hstable : (prefixWord ++ tailWord_69464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69464).length < 2 ^ (prefixWord ++ tailWord_69464).sum := by decide
  have hdescent : baseEnd_69464 < baseStart_69464 := by decide
  rcases family_descends (prefixWord ++ tailWord_69464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69513 : List Nat := [1, 2, 1, 1, 5, 1, 3, 4, 4]
def baseStart_69513 : Nat := 118140960795 + 69513 * 2 ^ 59
def prefixEnd_69513 : Nat := 4983230072969 + 3 ^ 40 * 69513 * 2
def baseEnd_69513 : Nat := 7931906830242614170627

theorem tailTrace_69513 : CollatzResearch.WordTrace tailWord_69513 prefixEnd_69513 7931906830242614170627 := by
  unfold tailWord_69513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535347397173747720341193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1690231598115831813560795 2535347397173747720341193)
  ·
    refine ⟨1901510547880310790255895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2535347397173747720341193 1901510547880310790255895)
    ·
      refine ⟨2852265821820466185383843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901510547880310790255895 2852265821820466185383843)
      ·
        refine ⟨4278398732730699278075765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852265821820466185383843 4278398732730699278075765)
        ·
          refine ⟨401099881193503057319603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4278398732730699278075765 401099881193503057319603)
          ·
            refine ⟨601649821790254585979405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401099881193503057319603 601649821790254585979405)
            ·
              refine ⟨225618683171345469742277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601649821790254585979405 225618683171345469742277)
              ·
                refine ⟨42303503094627275576677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 225618683171345469742277 42303503094627275576677)
                ·
                  refine ⟨7931906830242614170627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42303503094627275576677 7931906830242614170627)
                  ·
                    rfl

theorem cell22_69513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_69513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69513 prefixEnd_69513 := by exact prefixLift 69513
  have htrace : WordTrace (prefixWord ++ tailWord_69513) baseStart_69513 baseEnd_69513 := by
    simpa [prefixWord, tailWord_69513, baseEnd_69513] using wordTrace_append hprefix tailTrace_69513
  have hstable : (prefixWord ++ tailWord_69513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69513).length < 2 ^ (prefixWord ++ tailWord_69513).sum := by decide
  have hdescent : baseEnd_69513 < baseStart_69513 := by decide
  rcases family_descends (prefixWord ++ tailWord_69513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69543 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 1, 6]
def baseStart_69543 : Nat := 118140960795 + 69543 * 2 ^ 59
def prefixEnd_69543 : Nat := 4983230072969 + 3 ^ 40 * 69543 * 2
def baseEnd_69543 : Nat := 23805990103817764261789

theorem tailTrace_69543 : CollatzResearch.WordTrace tailWord_69543 prefixEnd_69543 23805990103817764261789 := by
  unfold tailWord_69543
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536441587065062843933283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1690961058043375229288855 2536441587065062843933283)
  ·
    refine ⟨3804662380597594265899925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536441587065062843933283 3804662380597594265899925)
    ·
      refine ⟨178343549090512231214059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3804662380597594265899925 178343549090512231214059)
      ·
        refine ⟨267515323635768346821089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178343549090512231214059 267515323635768346821089)
        ·
          refine ⟨200636492726826260115817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267515323635768346821089 200636492726826260115817)
          ·
            refine ⟨150477369545119695086863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200636492726826260115817 150477369545119695086863)
            ·
              refine ⟨225716054317679542630295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150477369545119695086863 225716054317679542630295)
              ·
                refine ⟨338574081476519313945443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225716054317679542630295 338574081476519313945443)
                ·
                  refine ⟨507861122214778970918165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338574081476519313945443 507861122214778970918165)
                  ·
                    refine ⟨23805990103817764261789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 507861122214778970918165 23805990103817764261789)
                    ·
                      rfl

theorem cell22_69543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_69543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69543 prefixEnd_69543 := by exact prefixLift 69543
  have htrace : WordTrace (prefixWord ++ tailWord_69543) baseStart_69543 baseEnd_69543 := by
    simpa [prefixWord, tailWord_69543, baseEnd_69543] using wordTrace_append hprefix tailTrace_69543
  have hstable : (prefixWord ++ tailWord_69543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69543).length < 2 ^ (prefixWord ++ tailWord_69543).sum := by decide
  have hdescent : baseEnd_69543 < baseStart_69543 := by decide
  rcases family_descends (prefixWord ++ tailWord_69543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69601 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_69601 : Nat := 118140960795 + 69601 * 2 ^ 59
def prefixEnd_69601 : Nat := 4983230072969 + 3 ^ 40 * 69601 * 2
def baseEnd_69601 : Nat := 23825844689124946311611

theorem tailTrace_69601 : CollatzResearch.WordTrace tailWord_69601 prefixEnd_69601 23825844689124946311611 := by
  unfold tailWord_69601
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538557020854938749544657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1692371347236625833029771 2538557020854938749544657)
  ·
    refine ⟨1903917765641204062158493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2538557020854938749544657 1903917765641204062158493)
    ·
      refine ⟨713969162115451523309435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1903917765641204062158493 713969162115451523309435)
      ·
        refine ⟨1070953743173177284964153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713969162115451523309435 1070953743173177284964153)
        ·
          refine ⟨803215307379882963723115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070953743173177284964153 803215307379882963723115)
          ·
            refine ⟨1204822961069824445584673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803215307379882963723115 1204822961069824445584673)
            ·
              refine ⟨903617220802368334188505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204822961069824445584673 903617220802368334188505)
              ·
                refine ⟨677712915601776250641379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903617220802368334188505 677712915601776250641379)
                ·
                  refine ⟨1016569373402664375962069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677712915601776250641379 1016569373402664375962069)
                  ·
                    refine ⟨23825844689124946311611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1016569373402664375962069 23825844689124946311611)
                    ·
                      rfl

theorem cell22_69601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_69601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69601 prefixEnd_69601 := by exact prefixLift 69601
  have htrace : WordTrace (prefixWord ++ tailWord_69601) baseStart_69601 baseEnd_69601 := by
    simpa [prefixWord, tailWord_69601, baseEnd_69601] using wordTrace_append hprefix tailTrace_69601
  have hstable : (prefixWord ++ tailWord_69601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69601).length < 2 ^ (prefixWord ++ tailWord_69601).sum := by decide
  have hdescent : baseEnd_69601 < baseStart_69601 := by decide
  rcases family_descends (prefixWord ++ tailWord_69601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69633 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_69633 : Nat := 118140960795 + 69633 * 2 ^ 59
def prefixEnd_69633 : Nat := 4983230072969 + 3 ^ 40 * 69633 * 2
def baseEnd_69633 : Nat := 23836798943087529511513

theorem tailTrace_69633 : CollatzResearch.WordTrace tailWord_69633 prefixEnd_69633 23836798943087529511513 := by
  unfold tailWord_69633
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539724156739008214709553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1693149437826005476473035 2539724156739008214709553)
  ·
    refine ⟨1904793117554256161032165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2539724156739008214709553 1904793117554256161032165)
    ·
      refine ⟨357148709541423030193531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1904793117554256161032165 357148709541423030193531)
      ·
        refine ⟨535723064312134545290297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357148709541423030193531 535723064312134545290297)
        ·
          refine ⟨401792298234100908967723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535723064312134545290297 401792298234100908967723)
          ·
            refine ⟨602688447351151363451585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401792298234100908967723 602688447351151363451585)
            ·
              refine ⟨452016335513363522588689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602688447351151363451585 452016335513363522588689)
              ·
                refine ⟨339012251635022641941517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452016335513363522588689 339012251635022641941517)
                ·
                  refine ⟨127129594363133490728069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339012251635022641941517 127129594363133490728069)
                  ·
                    refine ⟨23836798943087529511513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127129594363133490728069 23836798943087529511513)
                    ·
                      rfl

theorem cell22_69633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_69633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69633 prefixEnd_69633 := by exact prefixLift 69633
  have htrace : WordTrace (prefixWord ++ tailWord_69633) baseStart_69633 baseEnd_69633 := by
    simpa [prefixWord, tailWord_69633, baseEnd_69633] using wordTrace_append hprefix tailTrace_69633
  have hstable : (prefixWord ++ tailWord_69633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69633).length < 2 ^ (prefixWord ++ tailWord_69633).sum := by decide
  have hdescent : baseEnd_69633 < baseStart_69633 := by decide
  rcases family_descends (prefixWord ++ tailWord_69633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69663 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 1, 5]
def baseStart_69663 : Nat := 118140960795 + 69663 * 2 ^ 59
def prefixEnd_69663 : Nat := 4983230072969 + 3 ^ 40 * 69663 * 2
def baseEnd_69663 : Nat := 23847068556177451261421

theorem tailTrace_69663 : CollatzResearch.WordTrace tailWord_69663 prefixEnd_69663 23847068556177451261421 := by
  unfold tailWord_69663
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540818346630323338301643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1693878897753548892201095 2540818346630323338301643)
  ·
    refine ⟨3811227519945485007452465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2540818346630323338301643 3811227519945485007452465)
    ·
      refine ⟨2858420639959113755589349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3811227519945485007452465 2858420639959113755589349)
      ·
        refine ⟨535953869992333829173003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2858420639959113755589349 535953869992333829173003)
        ·
          refine ⟨803930804988500743759505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535953869992333829173003 803930804988500743759505)
          ·
            refine ⟨602948103741375557819629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 803930804988500743759505 602948103741375557819629)
            ·
              refine ⟨226105538903015834182361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 602948103741375557819629 226105538903015834182361)
              ·
                refine ⟨169579154177261875636771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226105538903015834182361 169579154177261875636771)
                ·
                  refine ⟨254368731265892813455157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169579154177261875636771 254368731265892813455157)
                  ·
                    refine ⟨23847068556177451261421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 254368731265892813455157 23847068556177451261421)
                    ·
                      rfl

theorem cell22_69663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_69663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69663 prefixEnd_69663 := by exact prefixLift 69663
  have htrace : WordTrace (prefixWord ++ tailWord_69663) baseStart_69663 baseEnd_69663 := by
    simpa [prefixWord, tailWord_69663, baseEnd_69663] using wordTrace_append hprefix tailTrace_69663
  have hstable : (prefixWord ++ tailWord_69663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69663).length < 2 ^ (prefixWord ++ tailWord_69663).sum := by decide
  have hdescent : baseEnd_69663 < baseStart_69663 := by decide
  rcases family_descends (prefixWord ++ tailWord_69663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69680 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_69680 : Nat := 118140960795 + 69680 * 2 ^ 59
def prefixEnd_69680 : Nat := 4983230072969 + 3 ^ 40 * 69680 * 2
def baseEnd_69680 : Nat := 23852888003595073586369

theorem tailTrace_69680 : CollatzResearch.WordTrace tailWord_69680 prefixEnd_69680 23852888003595073586369 := by
  unfold tailWord_69680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270719193784367620835247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1694292258379156827780329 1270719193784367620835247)
  ·
    refine ⟨1906078790676551431252871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1270719193784367620835247 1906078790676551431252871)
    ·
      refine ⟨2859118186014827146879307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906078790676551431252871 2859118186014827146879307)
      ·
        refine ⟨4288677279022240720318961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2859118186014827146879307 4288677279022240720318961)
        ·
          refine ⟨3216507959266680540239221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4288677279022240720318961 3216507959266680540239221)
          ·
            refine ⟨301547621181251300647427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3216507959266680540239221 301547621181251300647427)
            ·
              refine ⟨452321431771876950971141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301547621181251300647427 452321431771876950971141)
              ·
                refine ⟨84810268457226928307089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452321431771876950971141 84810268457226928307089)
                ·
                  refine ⟨63607701342920196230317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84810268457226928307089 63607701342920196230317)
                  ·
                    refine ⟨23852888003595073586369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63607701342920196230317 23852888003595073586369)
                    ·
                      rfl

theorem cell22_69680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_69680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69680 prefixEnd_69680 := by exact prefixLift 69680
  have htrace : WordTrace (prefixWord ++ tailWord_69680) baseStart_69680 baseEnd_69680 := by
    simpa [prefixWord, tailWord_69680, baseEnd_69680] using wordTrace_append hprefix tailTrace_69680
  have hstable : (prefixWord ++ tailWord_69680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69680).length < 2 ^ (prefixWord ++ tailWord_69680).sum := by decide
  have hdescent : baseEnd_69680 < baseStart_69680 := by decide
  rcases family_descends (prefixWord ++ tailWord_69680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69682 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_69682 : Nat := 118140960795 + 69682 * 2 ^ 59
def prefixEnd_69682 : Nat := 4983230072969 + 3 ^ 40 * 69682 * 2
def baseEnd_69682 : Nat := 7951190881489245012121

theorem tailTrace_69682 : CollatzResearch.WordTrace tailWord_69682 prefixEnd_69682 7951190881489245012121 := by
  unfold tailWord_69682
  simp only [CollatzResearch.WordTrace]
  refine ⟨635377833390372395810825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1694340889040993055495533 635377833390372395810825)
  ·
    refine ⟨476533375042779296858119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 635377833390372395810825 476533375042779296858119)
    ·
      refine ⟨714800062564168945287179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476533375042779296858119 714800062564168945287179)
      ·
        refine ⟨1072200093846253417930769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714800062564168945287179 1072200093846253417930769)
        ·
          refine ⟨804150070384690063448077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072200093846253417930769 804150070384690063448077)
          ·
            refine ⟨301556276394258773793029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 804150070384690063448077 301556276394258773793029)
            ·
              refine ⟨56541801823923520086193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 301556276394258773793029 56541801823923520086193)
              ·
                refine ⟨42406351367942640064645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56541801823923520086193 42406351367942640064645)
                ·
                  refine ⟨7951190881489245012121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42406351367942640064645 7951190881489245012121)
                  ·
                    rfl

theorem cell22_69682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_69682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69682 prefixEnd_69682 := by exact prefixLift 69682
  have htrace : WordTrace (prefixWord ++ tailWord_69682) baseStart_69682 baseEnd_69682 := by
    simpa [prefixWord, tailWord_69682, baseEnd_69682] using wordTrace_append hprefix tailTrace_69682
  have hstable : (prefixWord ++ tailWord_69682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69682).length < 2 ^ (prefixWord ++ tailWord_69682).sum := by decide
  have hdescent : baseEnd_69682 < baseStart_69682 := by decide
  rcases family_descends (prefixWord ++ tailWord_69682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69697 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_69697 : Nat := 118140960795 + 69697 * 2 ^ 59
def prefixEnd_69697 : Nat := 4983230072969 + 3 ^ 40 * 69697 * 2
def baseEnd_69697 : Nat := 23858707451012695911317

theorem tailTrace_69697 : CollatzResearch.WordTrace tailWord_69697 prefixEnd_69697 23858707451012695911317 := by
  unfold tailWord_69697
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542058428507147145039345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1694705619004764763359563 2542058428507147145039345)
  ·
    refine ⟨1906543821380360358779509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2542058428507147145039345 1906543821380360358779509)
    ·
      refine ⟨178738483254408783635579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1906543821380360358779509 178738483254408783635579)
      ·
        refine ⟨268107724881613175453369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178738483254408783635579 268107724881613175453369)
        ·
          refine ⟨201080793661209881590027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268107724881613175453369 201080793661209881590027)
          ·
            refine ⟨301621190491814822385041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201080793661209881590027 301621190491814822385041)
            ·
              refine ⟨226215892868861116788781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301621190491814822385041 226215892868861116788781)
              ·
                refine ⟨84830959825822918795793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226215892868861116788781 84830959825822918795793)
                ·
                  refine ⟨63623219869367189096845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84830959825822918795793 63623219869367189096845)
                  ·
                    refine ⟨23858707451012695911317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63623219869367189096845 23858707451012695911317)
                    ·
                      rfl

theorem cell22_69697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_69697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69697 prefixEnd_69697 := by exact prefixLift 69697
  have htrace : WordTrace (prefixWord ++ tailWord_69697) baseStart_69697 baseEnd_69697 := by
    simpa [prefixWord, tailWord_69697, baseEnd_69697] using wordTrace_append hprefix tailTrace_69697
  have hstable : (prefixWord ++ tailWord_69697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69697).length < 2 ^ (prefixWord ++ tailWord_69697).sum := by decide
  have hdescent : baseEnd_69697 < baseStart_69697 := by decide
  rcases family_descends (prefixWord ++ tailWord_69697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69710 : List Nat := [4, 1, 1, 1, 1, 5, 3, 6]
def baseStart_69710 : Nat := 118140960795 + 69710 * 2 ^ 59
def prefixEnd_69710 : Nat := 4983230072969 + 3 ^ 40 * 69710 * 2
def baseEnd_69710 : Nat := 2651461957409443926253

theorem tailTrace_69710 : CollatzResearch.WordTrace tailWord_69710 prefixEnd_69710 2651461957409443926253 := by
  unfold tailWord_69710
  simp only [CollatzResearch.WordTrace]
  refine ⟨317816572182506295657823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1695021718306700243508389 317816572182506295657823)
  ·
    refine ⟨476724858273759443486735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317816572182506295657823 476724858273759443486735)
    ·
      refine ⟨715087287410639165230103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476724858273759443486735 715087287410639165230103)
      ·
        refine ⟨1072630931115958747845155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715087287410639165230103 1072630931115958747845155)
        ·
          refine ⟨1608946396673938121767733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072630931115958747845155 1608946396673938121767733)
          ·
            refine ⟨150838724688181698915725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1608946396673938121767733 150838724688181698915725)
            ·
              refine ⟨56564521758068137093397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150838724688181698915725 56564521758068137093397)
              ·
                refine ⟨2651461957409443926253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56564521758068137093397 2651461957409443926253)
                ·
                  rfl

theorem cell22_69710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_69710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69710 prefixEnd_69710 := by exact prefixLift 69710
  have htrace : WordTrace (prefixWord ++ tailWord_69710) baseStart_69710 baseEnd_69710 := by
    simpa [prefixWord, tailWord_69710, baseEnd_69710] using wordTrace_append hprefix tailTrace_69710
  have hstable : (prefixWord ++ tailWord_69710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69710).length < 2 ^ (prefixWord ++ tailWord_69710).sum := by decide
  have hdescent : baseEnd_69710 < baseStart_69710 := by decide
  rcases family_descends (prefixWord ++ tailWord_69710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69742 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_69742 : Nat := 118140960795 + 69742 * 2 ^ 59
def prefixEnd_69742 : Nat := 4983230072969 + 3 ^ 40 * 69742 * 2
def baseEnd_69742 : Nat := 23874111870647578536179

theorem tailTrace_69742 : CollatzResearch.WordTrace tailWord_69742 prefixEnd_69742 23874111870647578536179 := by
  unfold tailWord_69742
  simp only [CollatzResearch.WordTrace]
  refine ⟨317962464168014978803435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1695799808896079886951653 317962464168014978803435)
  ·
    refine ⟨476943696252022468205153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317962464168014978803435 476943696252022468205153)
    ·
      refine ⟨357707772189016851153865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 476943696252022468205153 357707772189016851153865)
      ·
        refine ⟨268280829141762638365399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357707772189016851153865 268280829141762638365399)
        ·
          refine ⟨402421243712643957548099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268280829141762638365399 402421243712643957548099)
          ·
            refine ⟨603631865568965936322149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402421243712643957548099 603631865568965936322149)
            ·
              refine ⟨113180974794181113060403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 603631865568965936322149 113180974794181113060403)
              ·
                refine ⟨169771462191271669590605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113180974794181113060403 169771462191271669590605)
                ·
                  refine ⟨63664298321726876096477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169771462191271669590605 63664298321726876096477)
                  ·
                    refine ⟨23874111870647578536179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63664298321726876096477 23874111870647578536179)
                    ·
                      rfl

theorem cell22_69742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_69742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69742 prefixEnd_69742 := by exact prefixLift 69742
  have htrace : WordTrace (prefixWord ++ tailWord_69742) baseStart_69742 baseEnd_69742 := by
    simpa [prefixWord, tailWord_69742, baseEnd_69742] using wordTrace_append hprefix tailTrace_69742
  have hstable : (prefixWord ++ tailWord_69742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69742).length < 2 ^ (prefixWord ++ tailWord_69742).sum := by decide
  have hdescent : baseEnd_69742 < baseStart_69742 := by decide
  rcases family_descends (prefixWord ++ tailWord_69742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69836 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_69836 : Nat := 118140960795 + 69836 * 2 ^ 59
def prefixEnd_69836 : Nat := 4983230072969 + 3 ^ 40 * 69836 * 2
def baseEnd_69836 : Nat := 23906289991662666685891

theorem tailTrace_69836 : CollatzResearch.WordTrace tailWord_69836 prefixEnd_69836 23906289991662666685891 := by
  unfold tailWord_69836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273564087501786942174681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1698085450002382589566241 1273564087501786942174681)
  ·
    refine ⟨955173065626340206631011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1273564087501786942174681 955173065626340206631011)
    ·
      refine ⟨1432759598439510309946517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955173065626340206631011 1432759598439510309946517)
      ·
        refine ⟨67160606176852045778743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1432759598439510309946517 67160606176852045778743)
        ·
          refine ⟨100740909265278068668115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67160606176852045778743 100740909265278068668115)
          ·
            refine ⟨151111363897917103002173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100740909265278068668115 151111363897917103002173)
            ·
              refine ⟨56666761461718913625815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151111363897917103002173 56666761461718913625815)
              ·
                refine ⟨85000142192578370438723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56666761461718913625815 85000142192578370438723)
                ·
                  refine ⟨127500213288867555658085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85000142192578370438723 127500213288867555658085)
                  ·
                    refine ⟨23906289991662666685891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127500213288867555658085 23906289991662666685891)
                    ·
                      rfl

theorem cell22_69836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_69836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69836 prefixEnd_69836 := by exact prefixLift 69836
  have htrace : WordTrace (prefixWord ++ tailWord_69836) baseStart_69836 baseEnd_69836 := by
    simpa [prefixWord, tailWord_69836, baseEnd_69836] using wordTrace_append hprefix tailTrace_69836
  have hstable : (prefixWord ++ tailWord_69836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69836).length < 2 ^ (prefixWord ++ tailWord_69836).sum := by decide
  have hdescent : baseEnd_69836 < baseStart_69836 := by decide
  rcases family_descends (prefixWord ++ tailWord_69836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69845 : List Nat := [1, 3, 2, 4, 2, 10]
def baseStart_69845 : Nat := 118140960795 + 69845 * 2 ^ 59
def prefixEnd_69845 : Nat := 4983230072969 + 3 ^ 40 * 69845 * 2
def baseEnd_69845 : Nat := 295177418217156089023

theorem tailTrace_69845 : CollatzResearch.WordTrace tailWord_69845 prefixEnd_69845 295177418217156089023 := by
  unfold tailWord_69845
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547456431970968421426989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1698304287980645614284659 2547456431970968421426989)
  ·
    refine ⟨955296161989113158035121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2547456431970968421426989 955296161989113158035121)
    ·
      refine ⟨716472121491834868526341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 955296161989113158035121 716472121491834868526341)
      ·
        refine ⟨134338522779719037848689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 716472121491834868526341 134338522779719037848689)
        ·
          refine ⟨100753892084789278386517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134338522779719037848689 100753892084789278386517)
          ·
            refine ⟨295177418217156089023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 100753892084789278386517 295177418217156089023)
            ·
              rfl

theorem cell22_69845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 10].length) (baseStart_69845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69845 prefixEnd_69845 := by exact prefixLift 69845
  have htrace : WordTrace (prefixWord ++ tailWord_69845) baseStart_69845 baseEnd_69845 := by
    simpa [prefixWord, tailWord_69845, baseEnd_69845] using wordTrace_append hprefix tailTrace_69845
  have hstable : (prefixWord ++ tailWord_69845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69845).length < 2 ^ (prefixWord ++ tailWord_69845).sum := by decide
  have hdescent : baseEnd_69845 < baseStart_69845 := by decide
  rcases family_descends (prefixWord ++ tailWord_69845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69905 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_69905 : Nat := 118140960795 + 69905 * 2 ^ 59
def prefixEnd_69905 : Nat := 4983230072969 + 3 ^ 40 * 69905 * 2
def baseEnd_69905 : Nat := 23929910101769486710679

theorem tailTrace_69905 : CollatzResearch.WordTrace tailWord_69905 prefixEnd_69905 23929910101769486710679 := by
  unfold tailWord_69905
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549644811753598668611169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1699763207835732445740779 2549644811753598668611169)
  ·
    refine ⟨1912233608815199001458377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2549644811753598668611169 1912233608815199001458377)
    ·
      refine ⟨1434175206611399251093783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1912233608815199001458377 1434175206611399251093783)
      ·
        refine ⟨2151262809917098876640675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1434175206611399251093783 2151262809917098876640675)
        ·
          refine ⟨3226894214875648314961013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2151262809917098876640675 3226894214875648314961013)
          ·
            refine ⟨302521332644592029527595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3226894214875648314961013 302521332644592029527595)
            ·
              refine ⟨453781998966888044291393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302521332644592029527595 453781998966888044291393)
              ·
                refine ⟨340336499225166033218545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453781998966888044291393 340336499225166033218545)
                ·
                  refine ⟨255252374418874524913909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340336499225166033218545 255252374418874524913909)
                  ·
                    refine ⟨23929910101769486710679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255252374418874524913909 23929910101769486710679)
                    ·
                      rfl

theorem cell22_69905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_69905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69905 prefixEnd_69905 := by exact prefixLift 69905
  have htrace : WordTrace (prefixWord ++ tailWord_69905) baseStart_69905 baseEnd_69905 := by
    simpa [prefixWord, tailWord_69905, baseEnd_69905] using wordTrace_append hprefix tailTrace_69905
  have hstable : (prefixWord ++ tailWord_69905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69905).length < 2 ^ (prefixWord ++ tailWord_69905).sum := by decide
  have hdescent : baseEnd_69905 < baseStart_69905 := by decide
  rcases family_descends (prefixWord ++ tailWord_69905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69922 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_69922 : Nat := 118140960795 + 69922 * 2 ^ 59
def prefixEnd_69922 : Nat := 4983230072969 + 3 ^ 40 * 69922 * 2
def baseEnd_69922 : Nat := 23935729549187109035627

theorem tailTrace_69922 : CollatzResearch.WordTrace tailWord_69922 prefixEnd_69922 23935729549187109035627 := by
  unfold tailWord_69922
  simp only [CollatzResearch.WordTrace]
  refine ⟨637566213173002642995005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1700176568461340381320013 637566213173002642995005)
  ·
    refine ⟨239087329939875991123127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 637566213173002642995005 239087329939875991123127)
    ·
      refine ⟨358630994909813986684691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239087329939875991123127 358630994909813986684691)
      ·
        refine ⟨537946492364720980027037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358630994909813986684691 537946492364720980027037)
        ·
          refine ⟨201729934636770367510139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 537946492364720980027037 201729934636770367510139)
          ·
            refine ⟨302594901955155551265209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201729934636770367510139 302594901955155551265209)
            ·
              refine ⟨226946176466366663448907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302594901955155551265209 226946176466366663448907)
              ·
                refine ⟨340419264699549995173361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226946176466366663448907 340419264699549995173361)
                ·
                  refine ⟨255314448524662496380021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340419264699549995173361 255314448524662496380021)
                  ·
                    refine ⟨23935729549187109035627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255314448524662496380021 23935729549187109035627)
                    ·
                      rfl

theorem cell22_69922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_69922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69922 prefixEnd_69922 := by exact prefixLift 69922
  have htrace : WordTrace (prefixWord ++ tailWord_69922) baseStart_69922 baseEnd_69922 := by
    simpa [prefixWord, tailWord_69922, baseEnd_69922] using wordTrace_append hprefix tailTrace_69922
  have hstable : (prefixWord ++ tailWord_69922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69922).length < 2 ^ (prefixWord ++ tailWord_69922).sum := by decide
  have hdescent : baseEnd_69922 < baseStart_69922 := by decide
  rcases family_descends (prefixWord ++ tailWord_69922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69924 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 5]
def baseStart_69924 : Nat := 118140960795 + 69924 * 2 ^ 59
def prefixEnd_69924 : Nat := 4983230072969 + 3 ^ 40 * 69924 * 2
def baseEnd_69924 : Nat := 7978804730019923495207

theorem tailTrace_69924 : CollatzResearch.WordTrace tailWord_69924 prefixEnd_69924 7978804730019923495207 := by
  unfold tailWord_69924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275168899342382456776413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1700225199123176609035217 1275168899342382456776413)
  ·
    refine ⟨478188337253393421291155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1275168899342382456776413 478188337253393421291155)
    ·
      refine ⟨717282505880090131936733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 478188337253393421291155 717282505880090131936733)
      ·
        refine ⟨268980939705033799476275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 717282505880090131936733 268980939705033799476275)
        ·
          refine ⟨403471409557550699214413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268980939705033799476275 403471409557550699214413)
          ·
            refine ⟨151301778584081512205405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 403471409557550699214413 151301778584081512205405)
            ·
              refine ⟨56738166969030567077027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151301778584081512205405 56738166969030567077027)
              ·
                refine ⟨85107250453545850615541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56738166969030567077027 85107250453545850615541)
                ·
                  refine ⟨7978804730019923495207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85107250453545850615541 7978804730019923495207)
                  ·
                    rfl

theorem cell22_69924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_69924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69924 prefixEnd_69924 := by exact prefixLift 69924
  have htrace : WordTrace (prefixWord ++ tailWord_69924) baseStart_69924 baseEnd_69924 := by
    simpa [prefixWord, tailWord_69924, baseEnd_69924] using wordTrace_append hprefix tailTrace_69924
  have hstable : (prefixWord ++ tailWord_69924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69924).length < 2 ^ (prefixWord ++ tailWord_69924).sum := by decide
  have hdescent : baseEnd_69924 < baseStart_69924 := by decide
  rcases family_descends (prefixWord ++ tailWord_69924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69935 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 6]
def baseStart_69935 : Nat := 118140960795 + 69935 * 2 ^ 59
def prefixEnd_69935 : Nat := 4983230072969 + 3 ^ 40 * 69935 * 2
def baseEnd_69935 : Nat := 7980059904953136153529

theorem tailTrace_69935 : CollatzResearch.WordTrace tailWord_69935 prefixEnd_69935 7980059904953136153529 := by
  unfold tailWord_69935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550739001644913792203259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1700492667763275861468839 2550739001644913792203259)
  ·
    refine ⟨3826108502467370688304889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2550739001644913792203259 3826108502467370688304889)
    ·
      refine ⟨2869581376850528016228667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3826108502467370688304889 2869581376850528016228667)
      ·
        refine ⟨4304372065275792024343001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869581376850528016228667 4304372065275792024343001)
        ·
          refine ⟨3228279048956844018257251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304372065275792024343001 3228279048956844018257251)
          ·
            refine ⟨4842418573435266027385877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228279048956844018257251 4842418573435266027385877)
            ·
              refine ⟨226988370629778095033713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4842418573435266027385877 226988370629778095033713)
              ·
                refine ⟨170241277972333571275285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226988370629778095033713 170241277972333571275285)
                ·
                  refine ⟨7980059904953136153529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170241277972333571275285 7980059904953136153529)
                  ·
                    rfl

theorem cell22_69935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 6].length) (baseStart_69935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69935 prefixEnd_69935 := by exact prefixLift 69935
  have htrace : WordTrace (prefixWord ++ tailWord_69935) baseStart_69935 baseEnd_69935 := by
    simpa [prefixWord, tailWord_69935, baseEnd_69935] using wordTrace_append hprefix tailTrace_69935
  have hstable : (prefixWord ++ tailWord_69935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69935).length < 2 ^ (prefixWord ++ tailWord_69935).sum := by decide
  have hdescent : baseEnd_69935 < baseStart_69935 := by decide
  rcases family_descends (prefixWord ++ tailWord_69935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69952 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 4]
def baseStart_69952 : Nat := 118140960795 + 69952 * 2 ^ 59
def prefixEnd_69952 : Nat := 4983230072969 + 3 ^ 40 * 69952 * 2
def baseEnd_69952 : Nat := 7981999720759010261845

theorem tailTrace_69952 : CollatzResearch.WordTrace tailWord_69952 prefixEnd_69952 7981999720759010261845 := by
  unfold tailWord_69952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275679521291662847786055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1700906028388883797048073 1275679521291662847786055)
  ·
    refine ⟨1913519281937494271679083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1275679521291662847786055 1913519281937494271679083)
    ·
      refine ⟨2870278922906241407518625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913519281937494271679083 2870278922906241407518625)
      ·
        refine ⟨2152709192179681055638969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2870278922906241407518625 2152709192179681055638969)
        ·
          refine ⟨1614531894134760791729227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2152709192179681055638969 1614531894134760791729227)
          ·
            refine ⟨2421797841202141187593841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614531894134760791729227 2421797841202141187593841)
            ·
              refine ⟨1816348380901605890695381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421797841202141187593841 1816348380901605890695381)
              ·
                refine ⟨42570665177381388063173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1816348380901605890695381 42570665177381388063173)
                ·
                  refine ⟨7981999720759010261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42570665177381388063173 7981999720759010261845)
                  ·
                    rfl

theorem cell22_69952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_69952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_69952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_69952 prefixEnd_69952 := by exact prefixLift 69952
  have htrace : WordTrace (prefixWord ++ tailWord_69952) baseStart_69952 baseEnd_69952 := by
    simpa [prefixWord, tailWord_69952, baseEnd_69952] using wordTrace_append hprefix tailTrace_69952
  have hstable : (prefixWord ++ tailWord_69952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69952).length < 2 ^ (prefixWord ++ tailWord_69952).sum := by decide
  have hdescent : baseEnd_69952 < baseStart_69952 := by decide
  rcases family_descends (prefixWord ++ tailWord_69952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70010 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_70010 : Nat := 118140960795 + 70010 * 2 ^ 59
def prefixEnd_70010 : Nat := 4983230072969 + 3 ^ 40 * 70010 * 2
def baseEnd_70010 : Nat := 23965853747584212835357

theorem tailTrace_70010 : CollatzResearch.WordTrace tailWord_70010 prefixEnd_70010 23965853747584212835357 := by
  unfold tailWord_70010
  simp only [CollatzResearch.WordTrace]
  refine ⟨638368619093300400295871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1702316317582134400788989 638368619093300400295871)
  ·
    refine ⟨957552928639950600443807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 638368619093300400295871 957552928639950600443807)
    ·
      refine ⟨1436329392959925900665711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957552928639950600443807 1436329392959925900665711)
      ·
        refine ⟨2154494089439888850998567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436329392959925900665711 2154494089439888850998567)
        ·
          refine ⟨3231741134159833276497851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154494089439888850998567 3231741134159833276497851)
          ·
            refine ⟨4847611701239749914746777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231741134159833276497851 4847611701239749914746777)
            ·
              refine ⟨3635708775929812436060083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4847611701239749914746777 3635708775929812436060083)
              ·
                refine ⟨5453563163894718654090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635708775929812436060083 5453563163894718654090125)
                ·
                  refine ⟨2045086186460519495283797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5453563163894718654090125 2045086186460519495283797)
                  ·
                    refine ⟨23965853747584212835357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2045086186460519495283797 23965853747584212835357)
                    ·
                      rfl

theorem cell22_70010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_70010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70010 prefixEnd_70010 := by exact prefixLift 70010
  have htrace : WordTrace (prefixWord ++ tailWord_70010) baseStart_70010 baseEnd_70010 := by
    simpa [prefixWord, tailWord_70010, baseEnd_70010] using wordTrace_append hprefix tailTrace_70010
  have hstable : (prefixWord ++ tailWord_70010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70010).length < 2 ^ (prefixWord ++ tailWord_70010).sum := by decide
  have hdescent : baseEnd_70010 < baseStart_70010 := by decide
  rcases family_descends (prefixWord ++ tailWord_70010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70012 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_70012 : Nat := 118140960795 + 70012 * 2 ^ 59
def prefixEnd_70012 : Nat := 4983230072969 + 3 ^ 40 * 70012 * 2
def baseEnd_70012 : Nat := 23966538388456874285351

theorem tailTrace_70012 : CollatzResearch.WordTrace tailWord_70012 prefixEnd_70012 23966538388456874285351 := by
  unfold tailWord_70012
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276773711182977971378145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1702364948243970628504193 1276773711182977971378145)
  ·
    refine ⟨957580283387233478533609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1276773711182977971378145 957580283387233478533609)
    ·
      refine ⟨718185212540425108900207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 957580283387233478533609 718185212540425108900207)
      ·
        refine ⟨1077277818810637663350311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718185212540425108900207 1077277818810637663350311)
        ·
          refine ⟨1615916728215956495025467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077277818810637663350311 1615916728215956495025467)
          ·
            refine ⟨2423875092323934742538201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615916728215956495025467 2423875092323934742538201)
            ·
              refine ⟨1817906319242951056903651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423875092323934742538201 1817906319242951056903651)
              ·
                refine ⟨2726859478864426585355477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817906319242951056903651 2726859478864426585355477)
                ·
                  refine ⟨63910769035884998094269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2726859478864426585355477 63910769035884998094269)
                  ·
                    refine ⟨23966538388456874285351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63910769035884998094269 23966538388456874285351)
                    ·
                      rfl

theorem cell22_70012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_70012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70012 prefixEnd_70012 := by exact prefixLift 70012
  have htrace : WordTrace (prefixWord ++ tailWord_70012) baseStart_70012 baseEnd_70012 := by
    simpa [prefixWord, tailWord_70012, baseEnd_70012] using wordTrace_append hprefix tailTrace_70012
  have hstable : (prefixWord ++ tailWord_70012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70012).length < 2 ^ (prefixWord ++ tailWord_70012).sum := by decide
  have hdescent : baseEnd_70012 < baseStart_70012 := by decide
  rcases family_descends (prefixWord ++ tailWord_70012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70046 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_70046 : Nat := 118140960795 + 70046 * 2 ^ 59
def prefixEnd_70046 : Nat := 4983230072969 + 3 ^ 40 * 70046 * 2
def baseEnd_70046 : Nat := 23978177283292118935247

theorem tailTrace_70046 : CollatzResearch.WordTrace tailWord_70046 prefixEnd_70046 23978177283292118935247 := by
  unfold tailWord_70046
  simp only [CollatzResearch.WordTrace]
  refine ⟨319348438030347468686749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1703191669495186499662661 319348438030347468686749)
  ·
    refine ⟨119755664261380300757531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 319348438030347468686749 119755664261380300757531)
    ·
      refine ⟨179633496392070451136297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119755664261380300757531 179633496392070451136297)
      ·
        refine ⟨134725122294052838352223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179633496392070451136297 134725122294052838352223)
        ·
          refine ⟨202087683441079257528335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134725122294052838352223 202087683441079257528335)
          ·
            refine ⟨303131525161618886292503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202087683441079257528335 303131525161618886292503)
            ·
              refine ⟨454697287742428329438755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303131525161618886292503 454697287742428329438755)
              ·
                refine ⟨682045931613642494158133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454697287742428329438755 682045931613642494158133)
                ·
                  refine ⟨63941806088778983827325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 682045931613642494158133 63941806088778983827325)
                  ·
                    refine ⟨23978177283292118935247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63941806088778983827325 23978177283292118935247)
                    ·
                      rfl

theorem cell22_70046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_70046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70046 prefixEnd_70046 := by exact prefixLift 70046
  have htrace : WordTrace (prefixWord ++ tailWord_70046) baseStart_70046 baseEnd_70046 := by
    simpa [prefixWord, tailWord_70046, baseEnd_70046] using wordTrace_append hprefix tailTrace_70046
  have hstable : (prefixWord ++ tailWord_70046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70046).length < 2 ^ (prefixWord ++ tailWord_70046).sum := by decide
  have hdescent : baseEnd_70046 < baseStart_70046 := by decide
  rcases family_descends (prefixWord ++ tailWord_70046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70076 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 5]
def baseStart_70076 : Nat := 118140960795 + 70076 * 2 ^ 59
def prefixEnd_70076 : Nat := 4983230072969 + 3 ^ 40 * 70076 * 2
def baseEnd_70076 : Nat := 7996148965460680228385

theorem tailTrace_70076 : CollatzResearch.WordTrace tailWord_70076 prefixEnd_70076 7996148965460680228385 := by
  unfold tailWord_70076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1277940847067047436543041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1703921129422729915390721 1277940847067047436543041)
  ·
    refine ⟨958455635300285577407281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1277940847067047436543041 958455635300285577407281)
    ·
      refine ⟨718841726475214183055461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958455635300285577407281 718841726475214183055461)
      ·
        refine ⟨134782823714102659322899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 718841726475214183055461 134782823714102659322899)
        ·
          refine ⟨202174235571153988984349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134782823714102659322899 202174235571153988984349)
          ·
            refine ⟨75815338339182745869131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202174235571153988984349 75815338339182745869131)
            ·
              refine ⟨113723007508774118803697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75815338339182745869131 113723007508774118803697)
              ·
                refine ⟨85292255631580589102773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113723007508774118803697 85292255631580589102773)
                ·
                  refine ⟨7996148965460680228385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85292255631580589102773 7996148965460680228385)
                  ·
                    rfl

theorem cell22_70076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_70076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70076 prefixEnd_70076 := by exact prefixLift 70076
  have htrace : WordTrace (prefixWord ++ tailWord_70076) baseStart_70076 baseEnd_70076 := by
    simpa [prefixWord, tailWord_70076, baseEnd_70076] using wordTrace_append hprefix tailTrace_70076
  have hstable : (prefixWord ++ tailWord_70076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70076).length < 2 ^ (prefixWord ++ tailWord_70076).sum := by decide
  have hdescent : baseEnd_70076 < baseStart_70076 := by decide
  rcases family_descends (prefixWord ++ tailWord_70076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70087 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 6]
def baseStart_70087 : Nat := 118140960795 + 70087 * 2 ^ 59
def prefixEnd_70087 : Nat := 4983230072969 + 3 ^ 40 * 70087 * 2
def baseEnd_70087 : Nat := 7997404140393892886707

theorem tailTrace_70087 : CollatzResearch.WordTrace tailWord_70087 prefixEnd_70087 7997404140393892886707 := by
  unfold tailWord_70087
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556282897094243751736515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1704188598062829167824343 2556282897094243751736515)
  ·
    refine ⟨3834424345641365627604773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2556282897094243751736515 3834424345641365627604773)
    ·
      refine ⟨718954564807756055175895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3834424345641365627604773 718954564807756055175895)
      ·
        refine ⟨1078431847211634082763843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718954564807756055175895 1078431847211634082763843)
        ·
          refine ⟨1617647770817451124145765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078431847211634082763843 1617647770817451124145765)
          ·
            refine ⟨303308957028272085777331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1617647770817451124145765 303308957028272085777331)
            ·
              refine ⟨454963435542408128665997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303308957028272085777331 454963435542408128665997)
              ·
                refine ⟨170611288328403048249749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 454963435542408128665997 170611288328403048249749)
                ·
                  refine ⟨7997404140393892886707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170611288328403048249749 7997404140393892886707)
                  ·
                    rfl

theorem cell22_70087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 6].length) (baseStart_70087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70087 prefixEnd_70087 := by exact prefixLift 70087
  have htrace : WordTrace (prefixWord ++ tailWord_70087) baseStart_70087 baseEnd_70087 := by
    simpa [prefixWord, tailWord_70087, baseEnd_70087] using wordTrace_append hprefix tailTrace_70087
  have hstable : (prefixWord ++ tailWord_70087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70087).length < 2 ^ (prefixWord ++ tailWord_70087).sum := by decide
  have hdescent : baseEnd_70087 < baseStart_70087 := by decide
  rcases family_descends (prefixWord ++ tailWord_70087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70114 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_70114 : Nat := 118140960795 + 70114 * 2 ^ 59
def prefixEnd_70114 : Nat := 4983230072969 + 3 ^ 40 * 70114 * 2
def baseEnd_70114 : Nat := 24001455072962608235039

theorem tailTrace_70114 : CollatzResearch.WordTrace tailWord_70114 prefixEnd_70114 24001455072962608235039 := by
  unfold tailWord_70114
  simp only [CollatzResearch.WordTrace]
  refine ⟨639316916999106840742349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1704845111997618241979597 639316916999106840742349)
  ·
    refine ⟨239743843874665065278381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 639316916999106840742349 239743843874665065278381)
    ·
      refine ⟨89903941452999399479393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239743843874665065278381 89903941452999399479393)
      ·
        refine ⟨67427956089749549609545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89903941452999399479393 67427956089749549609545)
        ·
          refine ⟨50570967067312162207159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67427956089749549609545 50570967067312162207159)
          ·
            refine ⟨75856450600968243310739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50570967067312162207159 75856450600968243310739)
            ·
              refine ⟨113784675901452364966109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75856450600968243310739 113784675901452364966109)
              ·
                refine ⟨42669253463044636862291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113784675901452364966109 42669253463044636862291)
                ·
                  refine ⟨64003880194566955293437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42669253463044636862291 64003880194566955293437)
                  ·
                    refine ⟨24001455072962608235039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64003880194566955293437 24001455072962608235039)
                    ·
                      rfl

theorem cell22_70114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_70114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70114 prefixEnd_70114 := by exact prefixLift 70114
  have htrace : WordTrace (prefixWord ++ tailWord_70114) baseStart_70114 baseEnd_70114 := by
    simpa [prefixWord, tailWord_70114, baseEnd_70114] using wordTrace_append hprefix tailTrace_70114
  have hstable : (prefixWord ++ tailWord_70114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70114).length < 2 ^ (prefixWord ++ tailWord_70114).sum := by decide
  have hdescent : baseEnd_70114 < baseStart_70114 := by decide
  rcases family_descends (prefixWord ++ tailWord_70114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70119 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 6, 3]
def baseStart_70119 : Nat := 118140960795 + 70119 * 2 ^ 59
def prefixEnd_70119 : Nat := 4983230072969 + 3 ^ 40 * 70119 * 2
def baseEnd_70119 : Nat := 24003166675144261860023

theorem tailTrace_70119 : CollatzResearch.WordTrace tailWord_70119 prefixEnd_70119 24003166675144261860023 := by
  unfold tailWord_70119
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557450032978313216901411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1704966688652208811267607 2557450032978313216901411)
  ·
    refine ⟨3836175049467469825352117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2557450032978313216901411 3836175049467469825352117)
    ·
      refine ⟨359641410887575296126761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3836175049467469825352117 359641410887575296126761)
      ·
        refine ⟨269731058165681472095071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359641410887575296126761 269731058165681472095071)
        ·
          refine ⟨404596587248522208142607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269731058165681472095071 404596587248522208142607)
          ·
            refine ⟨606894880872783312213911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404596587248522208142607 606894880872783312213911)
            ·
              refine ⟨910342321309174968320867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606894880872783312213911 910342321309174968320867)
              ·
                refine ⟨1365513481963762452481301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910342321309174968320867 1365513481963762452481301)
                ·
                  refine ⟨64008444467051364960061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1365513481963762452481301 64008444467051364960061)
                  ·
                    refine ⟨24003166675144261860023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64008444467051364960061 24003166675144261860023)
                    ·
                      rfl

theorem cell22_70119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_70119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70119 prefixEnd_70119 := by exact prefixLift 70119
  have htrace : WordTrace (prefixWord ++ tailWord_70119) baseStart_70119 baseEnd_70119 := by
    simpa [prefixWord, tailWord_70119, baseEnd_70119] using wordTrace_append hprefix tailTrace_70119
  have hstable : (prefixWord ++ tailWord_70119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70119).length < 2 ^ (prefixWord ++ tailWord_70119).sum := by decide
  have hdescent : baseEnd_70119 < baseStart_70119 := by decide
  rcases family_descends (prefixWord ++ tailWord_70119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70189 : List Nat := [1, 5, 4, 1, 1, 2, 2, 2, 4]
def baseStart_70189 : Nat := 118140960795 + 70189 * 2 ^ 59
def prefixEnd_70189 : Nat := 4983230072969 + 3 ^ 40 * 70189 * 2
def baseEnd_70189 : Nat := 8009043035229137536603

theorem tailTrace_70189 : CollatzResearch.WordTrace tailWord_70189 prefixEnd_70189 8009043035229137536603 := by
  unfold tailWord_70189
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560003142724715171949621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1706668761816476781299747 2560003142724715171949621)
  ·
    refine ⟨240000294630442047370277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2560003142724715171949621 240000294630442047370277)
    ·
      refine ⟨45000055243207883881927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240000294630442047370277 45000055243207883881927)
      ·
        refine ⟨67500082864811825822891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45000055243207883881927 67500082864811825822891)
        ·
          refine ⟨101250124297217738734337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67500082864811825822891 101250124297217738734337)
          ·
            refine ⟨75937593222913304050753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101250124297217738734337 75937593222913304050753)
            ·
              refine ⟨56953194917184978038065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75937593222913304050753 56953194917184978038065)
              ·
                refine ⟨42714896187888733528549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56953194917184978038065 42714896187888733528549)
                ·
                  refine ⟨8009043035229137536603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42714896187888733528549 8009043035229137536603)
                  ·
                    rfl

theorem cell22_70189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_70189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70189 prefixEnd_70189 := by exact prefixLift 70189
  have htrace : WordTrace (prefixWord ++ tailWord_70189) baseStart_70189 baseEnd_70189 := by
    simpa [prefixWord, tailWord_70189, baseEnd_70189] using wordTrace_append hprefix tailTrace_70189
  have hstable : (prefixWord ++ tailWord_70189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70189).length < 2 ^ (prefixWord ++ tailWord_70189).sum := by decide
  have hdescent : baseEnd_70189 < baseStart_70189 := by decide
  rcases family_descends (prefixWord ++ tailWord_70189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70194 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_70194 : Nat := 118140960795 + 70194 * 2 ^ 59
def prefixEnd_70194 : Nat := 4983230072969 + 3 ^ 40 * 70194 * 2
def baseEnd_70194 : Nat := 8009613569289688744931

theorem tailTrace_70194 : CollatzResearch.WordTrace tailWord_70194 prefixEnd_70194 8009613569289688744931 := by
  unfold tailWord_70194
  simp only [CollatzResearch.WordTrace]
  refine ⟨640046376926650256470409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1706790338471067350587757 640046376926650256470409)
  ·
    refine ⟨480034782694987692352807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 640046376926650256470409 480034782694987692352807)
    ·
      refine ⟨720052174042481538529211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480034782694987692352807 720052174042481538529211)
      ·
        refine ⟨1080078261063722307793817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720052174042481538529211 1080078261063722307793817)
        ·
          refine ⟨810058695797791730845363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080078261063722307793817 810058695797791730845363)
          ·
            refine ⟨1215088043696687596268045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810058695797791730845363 1215088043696687596268045)
            ·
              refine ⟨455658016386257848600517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1215088043696687596268045 455658016386257848600517)
              ·
                refine ⟨85435878072423346612597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455658016386257848600517 85435878072423346612597)
                ·
                  refine ⟨8009613569289688744931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85435878072423346612597 8009613569289688744931)
                  ·
                    rfl

theorem cell22_70194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_70194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70194 prefixEnd_70194 := by exact prefixLift 70194
  have htrace : WordTrace (prefixWord ++ tailWord_70194) baseStart_70194 baseEnd_70194 := by
    simpa [prefixWord, tailWord_70194, baseEnd_70194] using wordTrace_append hprefix tailTrace_70194
  have hstable : (prefixWord ++ tailWord_70194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70194).length < 2 ^ (prefixWord ++ tailWord_70194).sum := by decide
  have hdescent : baseEnd_70194 < baseStart_70194 := by decide
  rcases family_descends (prefixWord ++ tailWord_70194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70209 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_70209 : Nat := 118140960795 + 70209 * 2 ^ 59
def prefixEnd_70209 : Nat := 4983230072969 + 3 ^ 40 * 70209 * 2
def baseEnd_70209 : Nat := 24033975514414027109747

theorem tailTrace_70209 : CollatzResearch.WordTrace tailWord_70209 prefixEnd_70209 24033975514414027109747 := by
  unfold tailWord_70209
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560732602652258587677681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1707155068434839058451787 2560732602652258587677681)
  ·
    refine ⟨1920549451989193940758261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2560732602652258587677681 1920549451989193940758261)
    ·
      refine ⟨180051511123986931946087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1920549451989193940758261 180051511123986931946087)
      ·
        refine ⟨270077266685980397919131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180051511123986931946087 270077266685980397919131)
        ·
          refine ⟨405115900028970596878697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270077266685980397919131 405115900028970596878697)
          ·
            refine ⟨303836925021727947659023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405115900028970596878697 303836925021727947659023)
            ·
              refine ⟨455755387532591921488535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303836925021727947659023 455755387532591921488535)
              ·
                refine ⟨683633081298887882232803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455755387532591921488535 683633081298887882232803)
                ·
                  refine ⟨1025449621948331823349205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683633081298887882232803 1025449621948331823349205)
                  ·
                    refine ⟨24033975514414027109747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1025449621948331823349205 24033975514414027109747)
                    ·
                      rfl

theorem cell22_70209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_70209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70209 prefixEnd_70209 := by exact prefixLift 70209
  have htrace : WordTrace (prefixWord ++ tailWord_70209) baseStart_70209 baseEnd_70209 := by
    simpa [prefixWord, tailWord_70209, baseEnd_70209] using wordTrace_append hprefix tailTrace_70209
  have hstable : (prefixWord ++ tailWord_70209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70209).length < 2 ^ (prefixWord ++ tailWord_70209).sum := by decide
  have hdescent : baseEnd_70209 < baseStart_70209 := by decide
  rcases family_descends (prefixWord ++ tailWord_70209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70241 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_70241 : Nat := 118140960795 + 70241 * 2 ^ 59
def prefixEnd_70241 : Nat := 4983230072969 + 3 ^ 40 * 70241 * 2
def baseEnd_70241 : Nat := 24044929768376610309649

theorem tailTrace_70241 : CollatzResearch.WordTrace tailWord_70241 prefixEnd_70241 24044929768376610309649 := by
  unfold tailWord_70241
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561899738536328052842577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1707933159024218701895051 2561899738536328052842577)
  ·
    refine ⟨1921424803902246039631933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2561899738536328052842577 1921424803902246039631933)
    ·
      refine ⟨720534301463342264861975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1921424803902246039631933 720534301463342264861975)
      ·
        refine ⟨1080801452195013397292963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720534301463342264861975 1080801452195013397292963)
        ·
          refine ⟨1621202178292520095939445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080801452195013397292963 1621202178292520095939445)
          ·
            refine ⟨151987704214923758994323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1621202178292520095939445 151987704214923758994323)
            ·
              refine ⟨227981556322385638491485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151987704214923758994323 227981556322385638491485)
              ·
                refine ⟨85493083620894614434307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227981556322385638491485 85493083620894614434307)
                ·
                  refine ⟨128239625431341921651461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85493083620894614434307 128239625431341921651461)
                  ·
                    refine ⟨24044929768376610309649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128239625431341921651461 24044929768376610309649)
                    ·
                      rfl

theorem cell22_70241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_70241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70241 prefixEnd_70241 := by exact prefixLift 70241
  have htrace : WordTrace (prefixWord ++ tailWord_70241) baseStart_70241 baseEnd_70241 := by
    simpa [prefixWord, tailWord_70241, baseEnd_70241] using wordTrace_append hprefix tailTrace_70241
  have hstable : (prefixWord ++ tailWord_70241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70241).length < 2 ^ (prefixWord ++ tailWord_70241).sum := by decide
  have hdescent : baseEnd_70241 < baseStart_70241 := by decide
  rcases family_descends (prefixWord ++ tailWord_70241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70256 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_70256 : Nat := 118140960795 + 70256 * 2 ^ 59
def prefixEnd_70256 : Nat := 4983230072969 + 3 ^ 40 * 70256 * 2
def baseEnd_70256 : Nat := 8016688191640523728201

theorem tailTrace_70256 : CollatzResearch.WordTrace tailWord_70256 prefixEnd_70256 8016688191640523728201 := by
  unfold tailWord_70256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281223416740992807319311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1708297888987990409759081 1281223416740992807319311)
  ·
    refine ⟨1921835125111489210978967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1281223416740992807319311 1921835125111489210978967)
    ·
      refine ⟨2882752687667233816468451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921835125111489210978967 2882752687667233816468451)
      ·
        refine ⟨4324129031500850724702677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882752687667233816468451 4324129031500850724702677)
        ·
          refine ⟨101346774175801188860219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4324129031500850724702677 101346774175801188860219)
          ·
            refine ⟨152020161263701783290329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101346774175801188860219 152020161263701783290329)
            ·
              refine ⟨114015120947776337467747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152020161263701783290329 114015120947776337467747)
              ·
                refine ⟨171022681421664506201621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114015120947776337467747 171022681421664506201621)
                ·
                  refine ⟨8016688191640523728201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171022681421664506201621 8016688191640523728201)
                  ·
                    rfl

theorem cell22_70256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_70256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70256 prefixEnd_70256 := by exact prefixLift 70256
  have htrace : WordTrace (prefixWord ++ tailWord_70256) baseStart_70256 baseEnd_70256 := by
    simpa [prefixWord, tailWord_70256, baseEnd_70256] using wordTrace_append hprefix tailTrace_70256
  have hstable : (prefixWord ++ tailWord_70256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70256).length < 2 ^ (prefixWord ++ tailWord_70256).sum := by decide
  have hdescent : baseEnd_70256 < baseStart_70256 := by decide
  rcases family_descends (prefixWord ++ tailWord_70256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70286 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_70286 : Nat := 118140960795 + 70286 * 2 ^ 59
def prefixEnd_70286 : Nat := 4983230072969 + 3 ^ 40 * 70286 * 2
def baseEnd_70286 : Nat := 24060334188011492934511

theorem tailTrace_70286 : CollatzResearch.WordTrace tailWord_70286 prefixEnd_70286 24060334188011492934511 := by
  unfold tailWord_70286
  simp only [CollatzResearch.WordTrace]
  refine ⟨320442627921662592278839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1709027348915533825487141 320442627921662592278839)
  ·
    refine ⟨480663941882493888418259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320442627921662592278839 480663941882493888418259)
    ·
      refine ⟨720995912823740832627389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480663941882493888418259 720995912823740832627389)
      ·
        refine ⟨270373467308902812235271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 720995912823740832627389 270373467308902812235271)
        ·
          refine ⟨405560200963354218352907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270373467308902812235271 405560200963354218352907)
          ·
            refine ⟨608340301445031327529361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405560200963354218352907 608340301445031327529361)
            ·
              refine ⟨456255226083773495647021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608340301445031327529361 456255226083773495647021)
              ·
                refine ⟨171095709781415060867633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456255226083773495647021 171095709781415060867633)
                ·
                  refine ⟨128321782336061295650725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171095709781415060867633 128321782336061295650725)
                  ·
                    refine ⟨24060334188011492934511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128321782336061295650725 24060334188011492934511)
                    ·
                      rfl

theorem cell22_70286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_70286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70286 prefixEnd_70286 := by exact prefixLift 70286
  have htrace : WordTrace (prefixWord ++ tailWord_70286) baseStart_70286 baseEnd_70286 := by
    simpa [prefixWord, tailWord_70286, baseEnd_70286] using wordTrace_append hprefix tailTrace_70286
  have hstable : (prefixWord ++ tailWord_70286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70286).length < 2 ^ (prefixWord ++ tailWord_70286).sum := by decide
  have hdescent : baseEnd_70286 < baseStart_70286 := by decide
  rcases family_descends (prefixWord ++ tailWord_70286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70290 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_70290 : Nat := 118140960795 + 70290 * 2 ^ 59
def prefixEnd_70290 : Nat := 4983230072969 + 3 ^ 40 * 70290 * 2
def baseEnd_70290 : Nat := 8020567823252271944833

theorem tailTrace_70290 : CollatzResearch.WordTrace tailWord_70290 prefixEnd_70290 8020567823252271944833 := by
  unfold tailWord_70290
  simp only [CollatzResearch.WordTrace]
  refine ⟨640921728839702355344081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1709124610239206280917549 640921728839702355344081)
  ·
    refine ⟨480691296629776766508061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 640921728839702355344081 480691296629776766508061)
    ·
      refine ⟨180259236236166287440523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 480691296629776766508061 180259236236166287440523)
      ·
        refine ⟨270388854354249431160785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180259236236166287440523 270388854354249431160785)
        ·
          refine ⟨202791640765687073370589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270388854354249431160785 202791640765687073370589)
          ·
            refine ⟨76046865287132652513971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202791640765687073370589 76046865287132652513971)
            ·
              refine ⟨114070297930698978770957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76046865287132652513971 114070297930698978770957)
              ·
                refine ⟨42776361724012117039109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114070297930698978770957 42776361724012117039109)
                ·
                  refine ⟨8020567823252271944833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42776361724012117039109 8020567823252271944833)
                  ·
                    rfl

theorem cell22_70290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_70290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70290 prefixEnd_70290 := by exact prefixLift 70290
  have htrace : WordTrace (prefixWord ++ tailWord_70290) baseStart_70290 baseEnd_70290 := by
    simpa [prefixWord, tailWord_70290, baseEnd_70290] using wordTrace_append hprefix tailTrace_70290
  have hstable : (prefixWord ++ tailWord_70290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70290).length < 2 ^ (prefixWord ++ tailWord_70290).sum := by decide
  have hdescent : baseEnd_70290 < baseStart_70290 := by decide
  rcases family_descends (prefixWord ++ tailWord_70290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70318 : List Nat := [4, 1, 4, 1, 1, 2, 2, 7]
def baseStart_70318 : Nat := 118140960795 + 70318 * 2 ^ 59
def prefixEnd_70318 : Nat := 4983230072969 + 3 ^ 40 * 70318 * 2
def baseEnd_70318 : Nat := 2674587604663786237157

theorem tailTrace_70318 : CollatzResearch.WordTrace tailWord_70318 prefixEnd_70318 2674587604663786237157 := by
  unfold tailWord_70318
  simp only [CollatzResearch.WordTrace]
  refine ⟨320588519907171275424451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1709805439504913468930405 320588519907171275424451)
  ·
    refine ⟨480882779860756913136677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320588519907171275424451 480882779860756913136677)
    ·
      refine ⟨90165521223891921213127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 480882779860756913136677 90165521223891921213127)
      ·
        refine ⟨135248281835837881819691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90165521223891921213127 135248281835837881819691)
        ·
          refine ⟨202872422753756822729537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135248281835837881819691 202872422753756822729537)
          ·
            refine ⟨152154317065317617047153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202872422753756822729537 152154317065317617047153)
            ·
              refine ⟨114115737798988212785365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152154317065317617047153 114115737798988212785365)
              ·
                refine ⟨2674587604663786237157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114115737798988212785365 2674587604663786237157)
                ·
                  rfl

theorem cell22_70318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_70318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70318 prefixEnd_70318 := by exact prefixLift 70318
  have htrace : WordTrace (prefixWord ++ tailWord_70318) baseStart_70318 baseEnd_70318 := by
    simpa [prefixWord, tailWord_70318, baseEnd_70318] using wordTrace_append hprefix tailTrace_70318
  have hstable : (prefixWord ++ tailWord_70318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70318).length < 2 ^ (prefixWord ++ tailWord_70318).sum := by decide
  have hdescent : baseEnd_70318 < baseStart_70318 := by decide
  rcases family_descends (prefixWord ++ tailWord_70318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70367 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 1, 3]
def baseStart_70367 : Nat := 118140960795 + 70367 * 2 ^ 59
def prefixEnd_70367 : Nat := 4983230072969 + 3 ^ 40 * 70367 * 2
def baseEnd_70367 : Nat := 24088062143354281659263

theorem tailTrace_70367 : CollatzResearch.WordTrace tailWord_70367 prefixEnd_70367 24088062143354281659263 := by
  unfold tailWord_70367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566495336079851571929355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1710996890719901047952903 2566495336079851571929355)
  ·
    refine ⟨3849743004119777357894033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2566495336079851571929355 3849743004119777357894033)
    ·
      refine ⟨2887307253089833018420525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3849743004119777357894033 2887307253089833018420525)
      ·
        refine ⟨1082740219908687381907697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2887307253089833018420525 1082740219908687381907697)
        ·
          refine ⟨812055164931515536430773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082740219908687381907697 812055164931515536430773)
          ·
            refine ⟨76130171712329581540385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 812055164931515536430773 76130171712329581540385)
            ·
              refine ⟨57097628784247186155289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76130171712329581540385 57097628784247186155289)
              ·
                refine ⟨42823221588185389616467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57097628784247186155289 42823221588185389616467)
                ·
                  refine ⟨64234832382278084424701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42823221588185389616467 64234832382278084424701)
                  ·
                    refine ⟨24088062143354281659263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64234832382278084424701 24088062143354281659263)
                    ·
                      rfl

theorem cell22_70367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_70367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70367 prefixEnd_70367 := by exact prefixLift 70367
  have htrace : WordTrace (prefixWord ++ tailWord_70367) baseStart_70367 baseEnd_70367 := by
    simpa [prefixWord, tailWord_70367, baseEnd_70367] using wordTrace_append hprefix tailTrace_70367
  have hstable : (prefixWord ++ tailWord_70367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70367).length < 2 ^ (prefixWord ++ tailWord_70367).sum := by decide
  have hdescent : baseEnd_70367 < baseStart_70367 := by decide
  rcases family_descends (prefixWord ++ tailWord_70367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70408 : List Nat := [2, 1, 3, 2, 2, 2, 1, 5, 4]
def baseStart_70408 : Nat := 118140960795 + 70408 * 2 ^ 59
def prefixEnd_70408 : Nat := 4983230072969 + 3 ^ 40 * 70408 * 2
def baseEnd_70408 : Nat := 8034032427081280461379

theorem tailTrace_70408 : CollatzResearch.WordTrace tailWord_70408 prefixEnd_70408 8034032427081280461379 := by
  unfold tailWord_70408
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283995364465657787085939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1711993819287543716114585 1283995364465657787085939)
  ·
    refine ⟨1925993046698486680628909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283995364465657787085939 1925993046698486680628909)
    ·
      refine ⟨722247392511932505235841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1925993046698486680628909 722247392511932505235841)
      ·
        refine ⟨541685544383949378926881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 722247392511932505235841 541685544383949378926881)
        ·
          refine ⟨406264158287962034195161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541685544383949378926881 406264158287962034195161)
          ·
            refine ⟨304698118715971525646371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406264158287962034195161 304698118715971525646371)
            ·
              refine ⟨457047178073957288469557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304698118715971525646371 457047178073957288469557)
              ·
                refine ⟨42848172944433495794021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457047178073957288469557 42848172944433495794021)
                ·
                  refine ⟨8034032427081280461379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42848172944433495794021 8034032427081280461379)
                  ·
                    rfl

theorem cell22_70408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_70408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70408 prefixEnd_70408 := by exact prefixLift 70408
  have htrace : WordTrace (prefixWord ++ tailWord_70408) baseStart_70408 baseEnd_70408 := by
    simpa [prefixWord, tailWord_70408, baseEnd_70408] using wordTrace_append hprefix tailTrace_70408
  have hstable : (prefixWord ++ tailWord_70408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70408).length < 2 ^ (prefixWord ++ tailWord_70408).sum := by decide
  have hdescent : baseEnd_70408 < baseStart_70408 := by decide
  rcases family_descends (prefixWord ++ tailWord_70408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70419 : List Nat := [1, 1, 1, 2, 1, 3, 13]
def baseStart_70419 : Nat := 118140960795 + 70419 * 2 ^ 59
def prefixEnd_70419 : Nat := 4983230072969 + 3 ^ 40 * 70419 * 2
def baseEnd_70419 : Nat := 892809733557165902189

theorem tailTrace_70419 : CollatzResearch.WordTrace tailWord_70419 prefixEnd_70419 892809733557165902189 := by
  unfold tailWord_70419
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568391931891464452822311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1712261287927642968548207 2568391931891464452822311)
  ·
    refine ⟨3852587897837196679233467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568391931891464452822311 3852587897837196679233467)
    ·
      refine ⟨5778881846755795018850201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3852587897837196679233467 5778881846755795018850201)
      ·
        refine ⟨4334161385066846264137651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5778881846755795018850201 4334161385066846264137651)
        ·
          refine ⟨6501242077600269396206477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4334161385066846264137651 6501242077600269396206477)
          ·
            refine ⟨2437965779100101023577429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6501242077600269396206477 2437965779100101023577429)
            ·
              refine ⟨892809733557165902189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 2437965779100101023577429 892809733557165902189)
              ·
                rfl

theorem cell22_70419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 13].length) (baseStart_70419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70419 prefixEnd_70419 := by exact prefixLift 70419
  have htrace : WordTrace (prefixWord ++ tailWord_70419) baseStart_70419 baseEnd_70419 := by
    simpa [prefixWord, tailWord_70419, baseEnd_70419] using wordTrace_append hprefix tailTrace_70419
  have hstable : (prefixWord ++ tailWord_70419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70419).length < 2 ^ (prefixWord ++ tailWord_70419).sum := by decide
  have hdescent : baseEnd_70419 < baseStart_70419 := by decide
  rcases family_descends (prefixWord ++ tailWord_70419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70421 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_70421 : Nat := 118140960795 + 70421 * 2 ^ 59
def prefixEnd_70421 : Nat := 4983230072969 + 3 ^ 40 * 70421 * 2
def baseEnd_70421 : Nat := 24106547446916140809097

theorem tailTrace_70421 : CollatzResearch.WordTrace tailWord_70421 prefixEnd_70421 24106547446916140809097 := by
  unfold tailWord_70421
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568464877884218794395117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1712309918589479196263411 2568464877884218794395117)
  ·
    refine ⟨963174329206582047898169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2568464877884218794395117 963174329206582047898169)
    ·
      refine ⟨722380746904936535923627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 963174329206582047898169 722380746904936535923627)
      ·
        refine ⟨1083571120357404803885441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722380746904936535923627 1083571120357404803885441)
        ·
          refine ⟨812678340268053602914081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083571120357404803885441 812678340268053602914081)
          ·
            refine ⟨609508755201040202185561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812678340268053602914081 609508755201040202185561)
            ·
              refine ⟨457131566400780151639171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609508755201040202185561 457131566400780151639171)
              ·
                refine ⟨685697349601170227458757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457131566400780151639171 685697349601170227458757)
                ·
                  refine ⟨128568253050219417648517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 685697349601170227458757 128568253050219417648517)
                  ·
                    refine ⟨24106547446916140809097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128568253050219417648517 24106547446916140809097)
                    ·
                      rfl

theorem cell22_70421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_70421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70421 prefixEnd_70421 := by exact prefixLift 70421
  have htrace : WordTrace (prefixWord ++ tailWord_70421) baseStart_70421 baseEnd_70421 := by
    simpa [prefixWord, tailWord_70421, baseEnd_70421] using wordTrace_append hprefix tailTrace_70421
  have hstable : (prefixWord ++ tailWord_70421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70421).length < 2 ^ (prefixWord ++ tailWord_70421).sum := by decide
  have hdescent : baseEnd_70421 < baseStart_70421 := by decide
  rcases family_descends (prefixWord ++ tailWord_70421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70453 : List Nat := [1, 3, 3, 1, 3, 1, 4, 6]
def baseStart_70453 : Nat := 118140960795 + 70453 * 2 ^ 59
def prefixEnd_70453 : Nat := 4983230072969 + 3 ^ 40 * 70453 * 2
def baseEnd_70453 : Nat := 2679722411208747112111

theorem tailTrace_70453 : CollatzResearch.WordTrace tailWord_70453 prefixEnd_70453 2679722411208747112111 := by
  unfold tailWord_70453
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569632013768288259560013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1713088009178858839706675 2569632013768288259560013)
  ·
    refine ⟨963612005163108097335005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2569632013768288259560013 963612005163108097335005)
    ·
      refine ⟨361354501936165536500627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 963612005163108097335005 361354501936165536500627)
      ·
        refine ⟨542031752904248304750941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361354501936165536500627 542031752904248304750941)
        ·
          refine ⟨203261907339093114281603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542031752904248304750941 203261907339093114281603)
          ·
            refine ⟨304892861008639671422405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203261907339093114281603 304892861008639671422405)
            ·
              refine ⟨57167411439119938391701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304892861008639671422405 57167411439119938391701)
              ·
                refine ⟨2679722411208747112111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57167411439119938391701 2679722411208747112111)
                ·
                  rfl

theorem cell22_70453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 6].length) (baseStart_70453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70453 prefixEnd_70453 := by exact prefixLift 70453
  have htrace : WordTrace (prefixWord ++ tailWord_70453) baseStart_70453 baseEnd_70453 := by
    simpa [prefixWord, tailWord_70453, baseEnd_70453] using wordTrace_append hprefix tailTrace_70453
  have hstable : (prefixWord ++ tailWord_70453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70453).length < 2 ^ (prefixWord ++ tailWord_70453).sum := by decide
  have hdescent : baseEnd_70453 < baseStart_70453 := by decide
  rcases family_descends (prefixWord ++ tailWord_70453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70496 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_70496 : Nat := 118140960795 + 70496 * 2 ^ 59
def prefixEnd_70496 : Nat := 4983230072969 + 3 ^ 40 * 70496 * 2
def baseEnd_70496 : Nat := 24132221479640945183867

theorem tailTrace_70496 : CollatzResearch.WordTrace tailWord_70496 prefixEnd_70496 24132221479640945183867 := by
  unfold tailWord_70496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285600176306253301687671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1714133568408337735583561 1285600176306253301687671)
  ·
    refine ⟨1928400264459379952531507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1285600176306253301687671 1928400264459379952531507)
    ·
      refine ⟨2892600396689069928797261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1928400264459379952531507 2892600396689069928797261)
      ·
        refine ⟨1084725148758401223298973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2892600396689069928797261 1084725148758401223298973)
        ·
          refine ⟨406771930784400458737115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1084725148758401223298973 406771930784400458737115)
          ·
            refine ⟨610157896176600688105673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406771930784400458737115 610157896176600688105673)
            ·
              refine ⟨457618422132450516079255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610157896176600688105673 457618422132450516079255)
              ·
                refine ⟨686427633198675774118883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457618422132450516079255 686427633198675774118883)
                ·
                  refine ⟨1029641449798013661178325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686427633198675774118883 1029641449798013661178325)
                  ·
                    refine ⟨24132221479640945183867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1029641449798013661178325 24132221479640945183867)
                    ·
                      rfl

theorem cell22_70496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_70496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70496 prefixEnd_70496 := by exact prefixLift 70496
  have htrace : WordTrace (prefixWord ++ tailWord_70496) baseStart_70496 baseEnd_70496 := by
    simpa [prefixWord, tailWord_70496, baseEnd_70496] using wordTrace_append hprefix tailTrace_70496
  have hstable : (prefixWord ++ tailWord_70496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70496).length < 2 ^ (prefixWord ++ tailWord_70496).sum := by decide
  have hdescent : baseEnd_70496 < baseStart_70496 := by decide
  rcases family_descends (prefixWord ++ tailWord_70496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70577 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 4]
def baseStart_70577 : Nat := 118140960795 + 70577 * 2 ^ 59
def prefixEnd_70577 : Nat := 4983230072969 + 3 ^ 40 * 70577 * 2
def baseEnd_70577 : Nat := 8053316478327911302873

theorem tailTrace_70577 : CollatzResearch.WordTrace tailWord_70577 prefixEnd_70577 8053316478327911302873 := by
  unfold tailWord_70577
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574154665319057437073985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1716103110212704958049323 2574154665319057437073985)
  ·
    refine ⟨1930615998989293077805489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2574154665319057437073985 1930615998989293077805489)
    ·
      refine ⟨1447961999241969808354117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1930615998989293077805489 1447961999241969808354117)
      ·
        refine ⟨271492874857869339066397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1447961999241969808354117 271492874857869339066397)
        ·
          refine ⟨101809828071701002149899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271492874857869339066397 101809828071701002149899)
          ·
            refine ⟨152714742107551503224849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101809828071701002149899 152714742107551503224849)
            ·
              refine ⟨114536056580663627418637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152714742107551503224849 114536056580663627418637)
              ·
                refine ⟨42951021217748860281989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114536056580663627418637 42951021217748860281989)
                ·
                  refine ⟨8053316478327911302873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42951021217748860281989 8053316478327911302873)
                  ·
                    rfl

theorem cell22_70577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_70577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70577 prefixEnd_70577 := by exact prefixLift 70577
  have htrace : WordTrace (prefixWord ++ tailWord_70577) baseStart_70577 baseEnd_70577 := by
    simpa [prefixWord, tailWord_70577, baseEnd_70577] using wordTrace_append hprefix tailTrace_70577
  have hstable : (prefixWord ++ tailWord_70577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70577).length < 2 ^ (prefixWord ++ tailWord_70577).sum := by decide
  have hdescent : baseEnd_70577 < baseStart_70577 := by decide
  rcases family_descends (prefixWord ++ tailWord_70577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70592 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_70592 : Nat := 118140960795 + 70592 * 2 ^ 59
def prefixEnd_70592 : Nat := 4983230072969 + 3 ^ 40 * 70592 * 2
def baseEnd_70592 : Nat := 24165084241528694783573

theorem tailTrace_70592 : CollatzResearch.WordTrace tailWord_70592 prefixEnd_70592 24165084241528694783573 := by
  unfold tailWord_70592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1287350880132357499435015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1716467840176476665913353 1287350880132357499435015)
  ·
    refine ⟨1931026320198536249152523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1287350880132357499435015 1931026320198536249152523)
    ·
      refine ⟨2896539480297804373728785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931026320198536249152523 2896539480297804373728785)
      ·
        refine ⟨2172404610223353280296589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2896539480297804373728785 2172404610223353280296589)
        ·
          refine ⟨814651728833757480111221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2172404610223353280296589 814651728833757480111221)
          ·
            refine ⟨76373599578164763760427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 814651728833757480111221 76373599578164763760427)
            ·
              refine ⟨114560399367247145640641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76373599578164763760427 114560399367247145640641)
              ·
                refine ⟨85920299525435359230481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114560399367247145640641 85920299525435359230481)
                ·
                  refine ⟨64440224644076519422861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85920299525435359230481 64440224644076519422861)
                  ·
                    refine ⟨24165084241528694783573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64440224644076519422861 24165084241528694783573)
                    ·
                      rfl

theorem cell22_70592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_70592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70592 prefixEnd_70592 := by exact prefixLift 70592
  have htrace : WordTrace (prefixWord ++ tailWord_70592) baseStart_70592 baseEnd_70592 := by
    simpa [prefixWord, tailWord_70592, baseEnd_70592] using wordTrace_append hprefix tailTrace_70592
  have hstable : (prefixWord ++ tailWord_70592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70592).length < 2 ^ (prefixWord ++ tailWord_70592).sum := by decide
  have hdescent : baseEnd_70592 < baseStart_70592 := by decide
  rcases family_descends (prefixWord ++ tailWord_70592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70667 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 5]
def baseStart_70667 : Nat := 118140960795 + 70667 * 2 ^ 59
def prefixEnd_70667 : Nat := 4983230072969 + 3 ^ 40 * 70667 * 2
def baseEnd_70667 : Nat := 8063586091417833052781

theorem tailTrace_70667 : CollatzResearch.WordTrace tailWord_70667 prefixEnd_70667 8063586091417833052781 := by
  unfold tailWord_70667
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577437234993002807850255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1718291489995335205233503 2577437234993002807850255)
  ·
    refine ⟨3866155852489504211775383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2577437234993002807850255 3866155852489504211775383)
    ·
      refine ⟨5799233778734256317663075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3866155852489504211775383 5799233778734256317663075)
      ·
        refine ⟨8698850668101384476494613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5799233778734256317663075 8698850668101384476494613)
        ·
          refine ⟨407758625067252397335685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8698850668101384476494613 407758625067252397335685)
          ·
            refine ⟨76454742200109824500441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 407758625067252397335685 76454742200109824500441)
            ·
              refine ⟨57341056650082368375331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76454742200109824500441 57341056650082368375331)
              ·
                refine ⟨86011584975123552562997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57341056650082368375331 86011584975123552562997)
                ·
                  refine ⟨8063586091417833052781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86011584975123552562997 8063586091417833052781)
                  ·
                    rfl

theorem cell22_70667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 5].length) (baseStart_70667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70667 prefixEnd_70667 := by exact prefixLift 70667
  have htrace : WordTrace (prefixWord ++ tailWord_70667) baseStart_70667 baseEnd_70667 := by
    simpa [prefixWord, tailWord_70667, baseEnd_70667] using wordTrace_append hprefix tailTrace_70667
  have hstable : (prefixWord ++ tailWord_70667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70667).length < 2 ^ (prefixWord ++ tailWord_70667).sum := by decide
  have hdescent : baseEnd_70667 < baseStart_70667 := by decide
  rcases family_descends (prefixWord ++ tailWord_70667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70680 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_70680 : Nat := 118140960795 + 70680 * 2 ^ 59
def prefixEnd_70680 : Nat := 4983230072969 + 3 ^ 40 * 70680 * 2
def baseEnd_70680 : Nat := 24195208439925798583303

theorem tailTrace_70680 : CollatzResearch.WordTrace tailWord_70680 prefixEnd_70680 24195208439925798583303 := by
  unfold tailWord_70680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288955691972953014036747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1718607589297270685382329 1288955691972953014036747)
  ·
    refine ⟨1933433537959429521055121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1288955691972953014036747 1933433537959429521055121)
    ·
      refine ⟨1450075153469572140791341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1933433537959429521055121 1450075153469572140791341)
      ·
        refine ⟨543778182551089552796753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1450075153469572140791341 543778182551089552796753)
        ·
          refine ⟨407833636913317164597565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543778182551089552796753 407833636913317164597565)
          ·
            refine ⟨152937613842493936724087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 407833636913317164597565 152937613842493936724087)
            ·
              refine ⟨229406420763740905086131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152937613842493936724087 229406420763740905086131)
              ·
                refine ⟨344109631145611357629197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229406420763740905086131 344109631145611357629197)
                ·
                  refine ⟨129041111679604259110949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344109631145611357629197 129041111679604259110949)
                  ·
                    refine ⟨24195208439925798583303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129041111679604259110949 24195208439925798583303)
                    ·
                      rfl

theorem cell22_70680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_70680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70680 prefixEnd_70680 := by exact prefixLift 70680
  have htrace : WordTrace (prefixWord ++ tailWord_70680) baseStart_70680 baseEnd_70680 := by
    simpa [prefixWord, tailWord_70680, baseEnd_70680] using wordTrace_append hprefix tailTrace_70680
  have hstable : (prefixWord ++ tailWord_70680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70680).length < 2 ^ (prefixWord ++ tailWord_70680).sum := by decide
  have hdescent : baseEnd_70680 < baseStart_70680 := by decide
  rcases family_descends (prefixWord ++ tailWord_70680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70712 : List Nat := [2, 1, 2, 1, 5, 2, 1, 4, 4]
def baseStart_70712 : Nat := 118140960795 + 70712 * 2 ^ 59
def prefixEnd_70712 : Nat := 4983230072969 + 3 ^ 40 * 70712 * 2
def baseEnd_70712 : Nat := 8068720897962793927735

theorem tailTrace_70712 : CollatzResearch.WordTrace tailWord_70712 prefixEnd_70712 8068720897962793927735 := by
  unfold tailWord_70712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289539259914987746619195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1719385679886650328825593 1289539259914987746619195)
  ·
    refine ⟨1934308889872481619928793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289539259914987746619195 1934308889872481619928793)
    ·
      refine ⟨1450731667404361214946595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1934308889872481619928793 1450731667404361214946595)
      ·
        refine ⟨2176097501106541822419893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450731667404361214946595 2176097501106541822419893)
        ·
          refine ⟨204009140728738295851865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2176097501106541822419893 204009140728738295851865)
          ·
            refine ⟨153006855546553721888899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204009140728738295851865 153006855546553721888899)
            ·
              refine ⟨229510283319830582833349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153006855546553721888899 229510283319830582833349)
              ·
                refine ⟨43033178122468234281253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229510283319830582833349 43033178122468234281253)
                ·
                  refine ⟨8068720897962793927735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43033178122468234281253 8068720897962793927735)
                  ·
                    rfl

theorem cell22_70712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_70712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70712 prefixEnd_70712 := by exact prefixLift 70712
  have htrace : WordTrace (prefixWord ++ tailWord_70712) baseStart_70712 baseEnd_70712 := by
    simpa [prefixWord, tailWord_70712, baseEnd_70712] using wordTrace_append hprefix tailTrace_70712
  have hstable : (prefixWord ++ tailWord_70712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70712).length < 2 ^ (prefixWord ++ tailWord_70712).sum := by decide
  have hdescent : baseEnd_70712 < baseStart_70712 := by decide
  rcases family_descends (prefixWord ++ tailWord_70712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70727 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 2, 3]
def baseStart_70727 : Nat := 118140960795 + 70727 * 2 ^ 59
def prefixEnd_70727 : Nat := 4983230072969 + 3 ^ 40 * 70727 * 2
def baseEnd_70727 : Nat := 24211297500433342658159

theorem tailTrace_70727 : CollatzResearch.WordTrace tailWord_70727 prefixEnd_70727 24211297500433342658159 := by
  unfold tailWord_70727
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579625614775633055034435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1719750409850422036689623 2579625614775633055034435)
  ·
    refine ⟨3869438422163449582551653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2579625614775633055034435 3869438422163449582551653)
    ·
      refine ⟨725519704155646796728435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3869438422163449582551653 725519704155646796728435)
      ·
        refine ⟨1088279556233470195092653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725519704155646796728435 1088279556233470195092653)
        ·
          refine ⟨408104833587551323159745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1088279556233470195092653 408104833587551323159745)
          ·
            refine ⟨306078625190663492369809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408104833587551323159745 306078625190663492369809)
            ·
              refine ⟨229558968892997619277357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306078625190663492369809 229558968892997619277357)
              ·
                refine ⟨86084613334874107229009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229558968892997619277357 86084613334874107229009)
                ·
                  refine ⟨64563460001155580421757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86084613334874107229009 64563460001155580421757)
                  ·
                    refine ⟨24211297500433342658159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64563460001155580421757 24211297500433342658159)
                    ·
                      rfl

theorem cell22_70727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_70727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70727 prefixEnd_70727 := by exact prefixLift 70727
  have htrace : WordTrace (prefixWord ++ tailWord_70727) baseStart_70727 baseEnd_70727 := by
    simpa [prefixWord, tailWord_70727, baseEnd_70727] using wordTrace_append hprefix tailTrace_70727
  have hstable : (prefixWord ++ tailWord_70727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70727).length < 2 ^ (prefixWord ++ tailWord_70727).sum := by decide
  have hdescent : baseEnd_70727 < baseStart_70727 := by decide
  rcases family_descends (prefixWord ++ tailWord_70727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70755 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 7, 3]
def baseStart_70755 : Nat := 118140960795 + 70755 * 2 ^ 59
def prefixEnd_70755 : Nat := 4983230072969 + 3 ^ 40 * 70755 * 2
def baseEnd_70755 : Nat := 24220882472650602958073

theorem tailTrace_70755 : CollatzResearch.WordTrace tailWord_70755 prefixEnd_70755 24220882472650602958073 := by
  unfold tailWord_70755
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580646858674193837053719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1720431239116129224702479 2580646858674193837053719)
  ·
    refine ⟨3870970288011290755580579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2580646858674193837053719 3870970288011290755580579)
    ·
      refine ⟨5806455432016936133370869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3870970288011290755580579 5806455432016936133370869)
      ·
        refine ⟨544355196751587762503519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5806455432016936133370869 544355196751587762503519)
        ·
          refine ⟨816532795127381643755279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544355196751587762503519 816532795127381643755279)
          ·
            refine ⟨1224799192691072465632919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816532795127381643755279 1224799192691072465632919)
            ·
              refine ⟨1837198789036608698449379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224799192691072465632919 1837198789036608698449379)
              ·
                refine ⟨2755798183554913047674069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837198789036608698449379 2755798183554913047674069)
                ·
                  refine ⟨64589019927068274554861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2755798183554913047674069 64589019927068274554861)
                  ·
                    refine ⟨24220882472650602958073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64589019927068274554861 24220882472650602958073)
                    ·
                      rfl

theorem cell22_70755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 3].length) (baseStart_70755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70755 prefixEnd_70755 := by exact prefixLift 70755
  have htrace : WordTrace (prefixWord ++ tailWord_70755) baseStart_70755 baseEnd_70755 := by
    simpa [prefixWord, tailWord_70755, baseEnd_70755] using wordTrace_append hprefix tailTrace_70755
  have hstable : (prefixWord ++ tailWord_70755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70755).length < 2 ^ (prefixWord ++ tailWord_70755).sum := by decide
  have hdescent : baseEnd_70755 < baseStart_70755 := by decide
  rcases family_descends (prefixWord ++ tailWord_70755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70823 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 1, 3]
def baseStart_70823 : Nat := 118140960795 + 70823 * 2 ^ 59
def prefixEnd_70823 : Nat := 4983230072969 + 3 ^ 40 * 70823 * 2
def baseEnd_70823 : Nat := 24244160262321092257865

theorem tailTrace_70823 : CollatzResearch.WordTrace tailWord_70823 prefixEnd_70823 24244160262321092257865 := by
  unfold tailWord_70823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583127022427841450529123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1722084681618560967019415 2583127022427841450529123)
  ·
    refine ⟨3874690533641762175793685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2583127022427841450529123 3874690533641762175793685)
    ·
      refine ⟨181626118764457601990329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3874690533641762175793685 181626118764457601990329)
      ·
        refine ⟨136219589073343201492747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181626118764457601990329 136219589073343201492747)
        ·
          refine ⟨204329383610014802239121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136219589073343201492747 204329383610014802239121)
          ·
            refine ⟨153247037707511101679341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204329383610014802239121 153247037707511101679341)
            ·
              refine ⟨57467639140316663129753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153247037707511101679341 57467639140316663129753)
              ·
                refine ⟨43100729355237497347315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57467639140316663129753 43100729355237497347315)
                ·
                  refine ⟨64651094032856246020973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43100729355237497347315 64651094032856246020973)
                  ·
                    refine ⟨24244160262321092257865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64651094032856246020973 24244160262321092257865)
                    ·
                      rfl

theorem cell22_70823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_70823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70823 prefixEnd_70823 := by exact prefixLift 70823
  have htrace : WordTrace (prefixWord ++ tailWord_70823) baseStart_70823 baseEnd_70823 := by
    simpa [prefixWord, tailWord_70823, baseEnd_70823] using wordTrace_append hprefix tailTrace_70823
  have hstable : (prefixWord ++ tailWord_70823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70823).length < 2 ^ (prefixWord ++ tailWord_70823).sum := by decide
  have hdescent : baseEnd_70823 < baseStart_70823 := by decide
  rcases family_descends (prefixWord ++ tailWord_70823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70849 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_70849 : Nat := 118140960795 + 70849 * 2 ^ 59
def prefixEnd_70849 : Nat := 4983230072969 + 3 ^ 40 * 70849 * 2
def baseEnd_70849 : Nat := 24253060593665691107785

theorem tailTrace_70849 : CollatzResearch.WordTrace tailWord_70849 prefixEnd_70849 24253060593665691107785 := by
  unfold tailWord_70849
  simp only [CollatzResearch.WordTrace]
  refine ⟨2584075320333647890975601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1722716880222431927317067 2584075320333647890975601)
  ·
    refine ⟨1938056490250235918231701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2584075320333647890975601 1938056490250235918231701)
    ·
      refine ⟨90846397980479808667111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1938056490250235918231701 90846397980479808667111)
      ·
        refine ⟨136269596970719713000667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90846397980479808667111 136269596970719713000667)
        ·
          refine ⟨204404395456079569501001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136269596970719713000667 204404395456079569501001)
          ·
            refine ⟨153303296592059677125751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204404395456079569501001 153303296592059677125751)
            ·
              refine ⟨229954944888089515688627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153303296592059677125751 229954944888089515688627)
              ·
                refine ⟨344932417332134273532941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229954944888089515688627 344932417332134273532941)
                ·
                  refine ⟨129349656499550352574853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344932417332134273532941 129349656499550352574853)
                  ·
                    refine ⟨24253060593665691107785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129349656499550352574853 24253060593665691107785)
                    ·
                      rfl

theorem cell22_70849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_70849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70849 prefixEnd_70849 := by exact prefixLift 70849
  have htrace : WordTrace (prefixWord ++ tailWord_70849) baseStart_70849 baseEnd_70849 := by
    simpa [prefixWord, tailWord_70849, baseEnd_70849] using wordTrace_append hprefix tailTrace_70849
  have hstable : (prefixWord ++ tailWord_70849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70849).length < 2 ^ (prefixWord ++ tailWord_70849).sum := by decide
  have hdescent : baseEnd_70849 < baseStart_70849 := by decide
  rcases family_descends (prefixWord ++ tailWord_70849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70881 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 4]
def baseStart_70881 : Nat := 118140960795 + 70881 * 2 ^ 59
def prefixEnd_70881 : Nat := 4983230072969 + 3 ^ 40 * 70881 * 2
def baseEnd_70881 : Nat := 8088004949209424769229

theorem tailTrace_70881 : CollatzResearch.WordTrace tailWord_70881 prefixEnd_70881 8088004949209424769229 := by
  unfold tailWord_70881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585242456217717356140497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1723494970811811570760331 2585242456217717356140497)
  ·
    refine ⟨1938931842163288017105373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2585242456217717356140497 1938931842163288017105373)
    ·
      refine ⟨727099440811233006414515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1938931842163288017105373 727099440811233006414515)
      ·
        refine ⟨1090649161216849509621773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727099440811233006414515 1090649161216849509621773)
        ·
          refine ⟨408993435456318566108165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1090649161216849509621773 408993435456318566108165)
          ·
            refine ⟨76686269148059731145281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 408993435456318566108165 76686269148059731145281)
            ·
              refine ⟨57514701861044798358961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76686269148059731145281 57514701861044798358961)
              ·
                refine ⟨43136026395783598769221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57514701861044798358961 43136026395783598769221)
                ·
                  refine ⟨8088004949209424769229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43136026395783598769221 8088004949209424769229)
                  ·
                    rfl

theorem cell22_70881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_70881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70881 prefixEnd_70881 := by exact prefixLift 70881
  have htrace : WordTrace (prefixWord ++ tailWord_70881) baseStart_70881 baseEnd_70881 := by
    simpa [prefixWord, tailWord_70881, baseEnd_70881] using wordTrace_append hprefix tailTrace_70881
  have hstable : (prefixWord ++ tailWord_70881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70881).length < 2 ^ (prefixWord ++ tailWord_70881).sum := by decide
  have hdescent : baseEnd_70881 < baseStart_70881 := by decide
  rcases family_descends (prefixWord ++ tailWord_70881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70892 : List Nat := [2, 2, 1, 1, 2, 6, 1, 7]
def baseStart_70892 : Nat := 118140960795 + 70892 * 2 ^ 59
def prefixEnd_70892 : Nat := 4983230072969 + 3 ^ 40 * 70892 * 2
def baseEnd_70892 : Nat := 2696420041380879142517

theorem tailTrace_70892 : CollatzResearch.WordTrace tailWord_70892 prefixEnd_70892 2696420041380879142517 := by
  unfold tailWord_70892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292821829588933117395465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1723762439451910823193953 1292821829588933117395465)
  ·
    refine ⟨969616372191699838046599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1292821829588933117395465 969616372191699838046599)
    ·
      refine ⟨1454424558287549757069899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969616372191699838046599 1454424558287549757069899)
      ·
        refine ⟨2181636837431324635604849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454424558287549757069899 2181636837431324635604849)
        ·
          refine ⟨1636227628073493476703637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181636837431324635604849 1636227628073493476703637)
          ·
            refine ⟨76698170065945006720483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1636227628073493476703637 76698170065945006720483)
            ·
              refine ⟨115047255098917510080725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76698170065945006720483 115047255098917510080725)
              ·
                refine ⟨2696420041380879142517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 115047255098917510080725 2696420041380879142517)
                ·
                  rfl

theorem cell22_70892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 7].length) (baseStart_70892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70892 prefixEnd_70892 := by exact prefixLift 70892
  have htrace : WordTrace (prefixWord ++ tailWord_70892) baseStart_70892 baseEnd_70892 := by
    simpa [prefixWord, tailWord_70892, baseEnd_70892] using wordTrace_append hprefix tailTrace_70892
  have hstable : (prefixWord ++ tailWord_70892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70892).length < 2 ^ (prefixWord ++ tailWord_70892).sum := by decide
  have hdescent : baseEnd_70892 < baseStart_70892 := by decide
  rcases family_descends (prefixWord ++ tailWord_70892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70905 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_70905 : Nat := 118140960795 + 70905 * 2 ^ 59
def prefixEnd_70905 : Nat := 4983230072969 + 3 ^ 40 * 70905 * 2
def baseEnd_70905 : Nat := 24272230538100211707613

theorem tailTrace_70905 : CollatzResearch.WordTrace tailWord_70905 prefixEnd_70905 24272230538100211707613 := by
  unfold tailWord_70905
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586117808130769455014169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1724078538753846303342779 2586117808130769455014169)
  ·
    refine ⟨1939588356098077091260627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2586117808130769455014169 1939588356098077091260627)
    ·
      refine ⟨2909382534147115636890941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1939588356098077091260627 2909382534147115636890941)
      ·
        refine ⟨1091018450305168363834103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2909382534147115636890941 1091018450305168363834103)
        ·
          refine ⟨1636527675457752545751155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091018450305168363834103 1636527675457752545751155)
          ·
            refine ⟨2454791513186628818626733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636527675457752545751155 2454791513186628818626733)
            ·
              refine ⟨920546817444985806985025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2454791513186628818626733 920546817444985806985025)
              ·
                refine ⟨690410113083739355238769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920546817444985806985025 690410113083739355238769)
                ·
                  refine ⟨517807584812804516429077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 690410113083739355238769 517807584812804516429077)
                  ·
                    refine ⟨24272230538100211707613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 517807584812804516429077 24272230538100211707613)
                    ·
                      rfl

theorem cell22_70905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_70905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70905 prefixEnd_70905 := by exact prefixLift 70905
  have htrace : WordTrace (prefixWord ++ tailWord_70905) baseStart_70905 baseEnd_70905 := by
    simpa [prefixWord, tailWord_70905, baseEnd_70905] using wordTrace_append hprefix tailTrace_70905
  have hstable : (prefixWord ++ tailWord_70905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70905).length < 2 ^ (prefixWord ++ tailWord_70905).sum := by decide
  have hdescent : baseEnd_70905 < baseStart_70905 := by decide
  rcases family_descends (prefixWord ++ tailWord_70905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70930 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_70930 : Nat := 118140960795 + 70930 * 2 ^ 59
def prefixEnd_70930 : Nat := 4983230072969 + 3 ^ 40 * 70930 * 2
def baseEnd_70930 : Nat := 24280788549008479832537

theorem tailTrace_70930 : CollatzResearch.WordTrace tailWord_70930 prefixEnd_70930 24280788549008479832537 := by
  unfold tailWord_70930
  simp only [CollatzResearch.WordTrace]
  refine ⟨646757408260049681168561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1724686422026799149782829 646757408260049681168561)
  ·
    refine ⟨485068056195037260876421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 646757408260049681168561 485068056195037260876421)
    ·
      refine ⟨90950260536569486414329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 485068056195037260876421 90950260536569486414329)
      ·
        refine ⟨68212695402427114810747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90950260536569486414329 68212695402427114810747)
        ·
          refine ⟨102319043103640672216121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68212695402427114810747 102319043103640672216121)
          ·
            refine ⟨76739282327730504162091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102319043103640672216121 76739282327730504162091)
            ·
              refine ⟨115108923491595756243137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76739282327730504162091 115108923491595756243137)
              ·
                refine ⟨86331692618696817182353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115108923491595756243137 86331692618696817182353)
                ·
                  refine ⟨64748769464022612886765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86331692618696817182353 64748769464022612886765)
                  ·
                    refine ⟨24280788549008479832537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64748769464022612886765 24280788549008479832537)
                    ·
                      rfl

theorem cell22_70930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_70930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70930 prefixEnd_70930 := by exact prefixLift 70930
  have htrace : WordTrace (prefixWord ++ tailWord_70930) baseStart_70930 baseEnd_70930 := by
    simpa [prefixWord, tailWord_70930, baseEnd_70930] using wordTrace_append hprefix tailTrace_70930
  have hstable : (prefixWord ++ tailWord_70930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70930).length < 2 ^ (prefixWord ++ tailWord_70930).sum := by decide
  have hdescent : baseEnd_70930 < baseStart_70930 := by decide
  rcases family_descends (prefixWord ++ tailWord_70930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70941 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_70941 : Nat := 118140960795 + 70941 * 2 ^ 59
def prefixEnd_70941 : Nat := 4983230072969 + 3 ^ 40 * 70941 * 2
def baseEnd_70941 : Nat := 24284554073808117807503

theorem tailTrace_70941 : CollatzResearch.WordTrace tailWord_70941 prefixEnd_70941 24284554073808117807503 := by
  unfold tailWord_70941
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587430836000347603324677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1724953890666898402216451 2587430836000347603324677)
  ·
    refine ⟨485143281750065175623377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2587430836000347603324677 485143281750065175623377)
    ·
      refine ⟨363857461312548881717533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 485143281750065175623377 363857461312548881717533)
      ·
        refine ⟨136446547992205830644075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 363857461312548881717533 136446547992205830644075)
        ·
          refine ⟨204669821988308745966113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136446547992205830644075 204669821988308745966113)
          ·
            refine ⟨153502366491231559474585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204669821988308745966113 153502366491231559474585)
            ·
              refine ⟨115126774868423669605939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153502366491231559474585 115126774868423669605939)
              ·
                refine ⟨172690162302635504408909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115126774868423669605939 172690162302635504408909)
                ·
                  refine ⟨64758810863488314153341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172690162302635504408909 64758810863488314153341)
                  ·
                    refine ⟨24284554073808117807503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64758810863488314153341 24284554073808117807503)
                    ·
                      rfl

theorem cell22_70941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_70941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70941 prefixEnd_70941 := by exact prefixLift 70941
  have htrace : WordTrace (prefixWord ++ tailWord_70941) baseStart_70941 baseEnd_70941 := by
    simpa [prefixWord, tailWord_70941, baseEnd_70941] using wordTrace_append hprefix tailTrace_70941
  have hstable : (prefixWord ++ tailWord_70941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70941).length < 2 ^ (prefixWord ++ tailWord_70941).sum := by decide
  have hdescent : baseEnd_70941 < baseStart_70941 := by decide
  rcases family_descends (prefixWord ++ tailWord_70941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70999 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 6]
def baseStart_70999 : Nat := 118140960795 + 70999 * 2 ^ 59
def prefixEnd_70999 : Nat := 4983230072969 + 3 ^ 40 * 70999 * 2
def baseEnd_70999 : Nat := 8101469553038433285775

theorem tailTrace_70999 : CollatzResearch.WordTrace tailWord_70999 prefixEnd_70999 8101469553038433285775 := by
  unfold tailWord_70999
  simp only [CollatzResearch.WordTrace]
  refine ⟨2589546269790223508936051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1726364179860149005957367 2589546269790223508936051)
  ·
    refine ⟨3884319404685335263404077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2589546269790223508936051 3884319404685335263404077)
    ·
      refine ⟨1456619776757000723776529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3884319404685335263404077 1456619776757000723776529)
      ·
        refine ⟨1092464832567750542832397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1456619776757000723776529 1092464832567750542832397)
        ·
          refine ⟨409674312212906453562149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1092464832567750542832397 409674312212906453562149)
          ·
            refine ⟨76813933539919960042903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 409674312212906453562149 76813933539919960042903)
            ·
              refine ⟨115220900309879940064355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76813933539919960042903 115220900309879940064355)
              ·
                refine ⟨172831350464819910096533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115220900309879940064355 172831350464819910096533)
                ·
                  refine ⟨8101469553038433285775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 172831350464819910096533 8101469553038433285775)
                  ·
                    rfl

theorem cell22_70999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 6].length) (baseStart_70999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_70999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_70999 prefixEnd_70999 := by exact prefixLift 70999
  have htrace : WordTrace (prefixWord ++ tailWord_70999) baseStart_70999 baseEnd_70999 := by
    simpa [prefixWord, tailWord_70999, baseEnd_70999] using wordTrace_append hprefix tailTrace_70999
  have hstable : (prefixWord ++ tailWord_70999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70999).length < 2 ^ (prefixWord ++ tailWord_70999).sum := by decide
  have hdescent : baseEnd_70999 < baseStart_70999 := by decide
  rcases family_descends (prefixWord ++ tailWord_70999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71018 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_71018 : Nat := 118140960795 + 71018 * 2 ^ 59
def prefixEnd_71018 : Nat := 4983230072969 + 3 ^ 40 * 71018 * 2
def baseEnd_71018 : Nat := 24310912747405583632267

theorem tailTrace_71018 : CollatzResearch.WordTrace tailWord_71018 prefixEnd_71018 24310912747405583632267 := by
  unfold tailWord_71018
  simp only [CollatzResearch.WordTrace]
  refine ⟨647559814180347438469427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1726826171147593169251805 647559814180347438469427)
  ·
    refine ⟨971339721270521157704141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 647559814180347438469427 971339721270521157704141)
    ·
      refine ⟨364252395476445434139053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 971339721270521157704141 364252395476445434139053)
      ·
        refine ⟨136594648303667037802145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 364252395476445434139053 136594648303667037802145)
        ·
          refine ⟨102445986227750278351609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136594648303667037802145 102445986227750278351609)
          ·
            refine ⟨76834489670812708763707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102445986227750278351609 76834489670812708763707)
            ·
              refine ⟨115251734506219063145561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76834489670812708763707 115251734506219063145561)
              ·
                refine ⟨86438800879664297359171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115251734506219063145561 86438800879664297359171)
                ·
                  refine ⟨129658201319496446038757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86438800879664297359171 129658201319496446038757)
                  ·
                    refine ⟨24310912747405583632267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129658201319496446038757 24310912747405583632267)
                    ·
                      rfl

theorem cell22_71018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_71018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71018 prefixEnd_71018 := by exact prefixLift 71018
  have htrace : WordTrace (prefixWord ++ tailWord_71018) baseStart_71018 baseEnd_71018 := by
    simpa [prefixWord, tailWord_71018, baseEnd_71018] using wordTrace_append hprefix tailTrace_71018
  have hstable : (prefixWord ++ tailWord_71018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71018).length < 2 ^ (prefixWord ++ tailWord_71018).sum := by decide
  have hdescent : baseEnd_71018 < baseStart_71018 := by decide
  rcases family_descends (prefixWord ++ tailWord_71018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71080 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 2, 4]
def baseStart_71080 : Nat := 118140960795 + 71080 * 2 ^ 59
def prefixEnd_71080 : Nat := 4983230072969 + 3 ^ 40 * 71080 * 2
def baseEnd_71080 : Nat := 24332136614458088582077

theorem tailTrace_71080 : CollatzResearch.WordTrace tailWord_71080 prefixEnd_71080 24332136614458088582077 := by
  unfold tailWord_71080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296250291248387171317347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1728333721664516228423129 1296250291248387171317347)
  ·
    refine ⟨1944375436872580756976021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1296250291248387171317347 1944375436872580756976021)
    ·
      refine ⟨91142598603402222983251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1944375436872580756976021 91142598603402222983251)
      ·
        refine ⟨136713897905103334474877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91142598603402222983251 136713897905103334474877)
        ·
          refine ⟨51267711714413750428079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136713897905103334474877 51267711714413750428079)
          ·
            refine ⟨76901567571620625642119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51267711714413750428079 76901567571620625642119)
            ·
              refine ⟨115352351357430938463179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76901567571620625642119 115352351357430938463179)
              ·
                refine ⟨173028527036146407694769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115352351357430938463179 173028527036146407694769)
                ·
                  refine ⟨129771395277109805771077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173028527036146407694769 129771395277109805771077)
                  ·
                    refine ⟨24332136614458088582077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129771395277109805771077 24332136614458088582077)
                    ·
                      rfl

theorem cell22_71080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_71080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71080 prefixEnd_71080 := by exact prefixLift 71080
  have htrace : WordTrace (prefixWord ++ tailWord_71080) baseStart_71080 baseEnd_71080 := by
    simpa [prefixWord, tailWord_71080, baseEnd_71080] using wordTrace_append hprefix tailTrace_71080
  have hstable : (prefixWord ++ tailWord_71080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71080).length < 2 ^ (prefixWord ++ tailWord_71080).sum := by decide
  have hdescent : baseEnd_71080 < baseStart_71080 := by decide
  rcases family_descends (prefixWord ++ tailWord_71080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71093 : List Nat := [1, 3, 3, 2, 2, 1, 1, 5, 1, 3]
def baseStart_71093 : Nat := 118140960795 + 71093 * 2 ^ 59
def prefixEnd_71093 : Nat := 4983230072969 + 3 ^ 40 * 71093 * 2
def baseEnd_71093 : Nat := 24336586780130388007037

theorem tailTrace_71093 : CollatzResearch.WordTrace tailWord_71093 prefixEnd_71093 24336586780130388007037 := by
  unfold tailWord_71093
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592974731449677562857933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1728649820966451708571955 2592974731449677562857933)
  ·
    refine ⟨972365524293629086071725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2592974731449677562857933 972365524293629086071725)
    ·
      refine ⟨364637071610110907276897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 972365524293629086071725 364637071610110907276897)
      ·
        refine ⟨273477803707583180457673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364637071610110907276897 273477803707583180457673)
        ·
          refine ⟨205108352780687385343255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273477803707583180457673 205108352780687385343255)
          ·
            refine ⟨307662529171031078014883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205108352780687385343255 307662529171031078014883)
            ·
              refine ⟨461493793756546617022325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307662529171031078014883 461493793756546617022325)
              ·
                refine ⟨43265043164676245345843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461493793756546617022325 43265043164676245345843)
                ·
                  refine ⟨64897564747014368018765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43265043164676245345843 64897564747014368018765)
                  ·
                    refine ⟨24336586780130388007037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64897564747014368018765 24336586780130388007037)
                    ·
                      rfl

theorem cell22_71093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_71093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71093 prefixEnd_71093 := by exact prefixLift 71093
  have htrace : WordTrace (prefixWord ++ tailWord_71093) baseStart_71093 baseEnd_71093 := by
    simpa [prefixWord, tailWord_71093, baseEnd_71093] using wordTrace_append hprefix tailTrace_71093
  have hstable : (prefixWord ++ tailWord_71093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71093).length < 2 ^ (prefixWord ++ tailWord_71093).sum := by decide
  have hdescent : baseEnd_71093 < baseStart_71093 := by decide
  rcases family_descends (prefixWord ++ tailWord_71093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71151 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 4]
def baseStart_71151 : Nat := 118140960795 + 71151 * 2 ^ 59
def prefixEnd_71151 : Nat := 4983230072969 + 3 ^ 40 * 71151 * 2
def baseEnd_71151 : Nat := 8118813788479190018953

theorem tailTrace_71151 : CollatzResearch.WordTrace tailWord_71151 prefixEnd_71151 8118813788479190018953 := by
  unfold tailWord_71151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595090165239553468469307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1730060110159702312312871 2595090165239553468469307)
  ·
    refine ⟨3892635247859330202703961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2595090165239553468469307 3892635247859330202703961)
    ·
      refine ⟨2919476435894497652027971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3892635247859330202703961 2919476435894497652027971)
      ·
        refine ⟨4379214653841746478041957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2919476435894497652027971 4379214653841746478041957)
        ·
          refine ⟨821102747595327464632867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4379214653841746478041957 821102747595327464632867)
          ·
            refine ⟨1231654121392991196949301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821102747595327464632867 1231654121392991196949301)
            ·
              refine ⟨115467573880592924713997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1231654121392991196949301 115467573880592924713997)
              ·
                refine ⟨43300340205222346767749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115467573880592924713997 43300340205222346767749)
                ·
                  refine ⟨8118813788479190018953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43300340205222346767749 8118813788479190018953)
                  ·
                    rfl

theorem cell22_71151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 4].length) (baseStart_71151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_71151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_71151 prefixEnd_71151 := by exact prefixLift 71151
  have htrace : WordTrace (prefixWord ++ tailWord_71151) baseStart_71151 baseEnd_71151 := by
    simpa [prefixWord, tailWord_71151, baseEnd_71151] using wordTrace_append hprefix tailTrace_71151
  have hstable : (prefixWord ++ tailWord_71151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71151).length < 2 ^ (prefixWord ++ tailWord_71151).sum := by decide
  have hdescent : baseEnd_71151 < baseStart_71151 := by decide
  rcases family_descends (prefixWord ++ tailWord_71151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
